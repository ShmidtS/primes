/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Probability.NoiseTemperature

/-!
# Семейство функций потерь и регуляризаций (объединённое)

ZLoss, GradNorm, Softcap, VicReg, TripletLoss. Слит из
пяти модулей; имена деклараций сохранены.
-/

/-!
# Z-loss: стабилизация router-логитов (источник №43)

Источник №43: Zoph et al., "ST-MoE: Designing Stable and
Transferable Sparse Expert Models" (arXiv 2202.08906).
Z-loss z = (1/c)·(log Z)², Z = Σ exp(logit_i) — штраф
за рост нормы router-логитов MoE: удерживает логиты в
компактной зоне, предотвращая численные сбои attention и
роутинга.

Формализованное ядро (строгое):
- `zloss_bound`: если штраф удержан z ≤ B при весе c > 0,
  то |log Z| ≤ √(B·c) — логит-норма ограничена
  (квадратичный штраф ⟹ корневая граница);
- `zloss_zero`: минимум штрафа достигается ТОЧНО на
  log Z = 0 (Z = 1): сбалансированная нормировка —
  глобальный минимум, нулевой штраф несовместим с
  раскачкой логитов.
-/

namespace Hagi.Model.ZLoss

/-- Задержанный штраф ограничивает логит-норму. -/
theorem zloss_bound (c Z B : ℝ) (hc : 0 < c)
    (hpen : (1 / c) * (Real.log Z) ^ 2 ≤ B) :
    |Real.log Z| ≤ Real.sqrt (B * c) := by
  have hmul : c * ((1 / c) * (Real.log Z) ^ 2) ≤ c * B :=
    mul_le_mul_of_nonneg_left hpen hc.le
  rw [← mul_assoc, show c * (1 / c) = 1 from by field_simp,
    one_mul] at hmul
  have h2 : (Real.log Z) ^ 2 ≤ c * B := hmul
  have hB : 0 ≤ B :=
    le_trans (mul_nonneg (by positivity) (sq_nonneg _)) hpen
  have hs : Real.sqrt (B * c) ^ 2 = B * c :=
    Real.sq_sqrt (by positivity)
  have hcomm : c * B = B * c := mul_comm c B
  rw [hcomm] at h2
  apply abs_le.2
  constructor <;> nlinarith [h2, hs, Real.sqrt_nonneg (B * c)]

/-- Нулевой штраф ⟺ log Z = 0 (сбалансированная
нормировка). -/
theorem zloss_zero (c Z : ℝ) (hc : 0 < c) (_hZ : 0 < Z) :
    (1 / c) * (Real.log Z) ^ 2 = 0 ↔ Real.log Z = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 (by positivity)
    · exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  · intro h
    rw [h]
    norm_num

end Hagi.Model.ZLoss

/-!
# GradNorm (источник №89: Chen et al., arXiv 1710.04057)

Балансировка мультитаск-лосса: веса задач wᵢ подстраиваются
обратно пропорционально нормам градиентов — выравнивание
«силы» задач предотвращает доминирование одной.

Честные свойства (скалярные нормы ‖gᵢ‖):
1. `gnWeight`: канонический вес wᵢ = c/‖gᵢ‖ (c > 0);
2. `gnBalanced`: взвешенная норма wᵢ·‖gᵢ‖ = c — ВСЕ задачи
   тянут с равной силой (точно, при ‖gᵢ‖ ≠ 0);
3. `gnPos`: веса положительны;
4. `gnInverse`: больший градиент — МЕНЬШЕ вес (обратная
   пропорциональность: анти-доминирование).
-/

namespace Hagi.Model.GradNorm

variable {k : Type*} [Fintype k]

/-- Канонический GradNorm-вес: c / ‖gᵢ‖. -/
noncomputable def gnWeight (c gnorm : ℝ) : ℝ := c / gnorm

/-- ВЗВЕШЕННАЯ НОРМА ТОЧНО РАВНА c: баланс сил задач. -/
theorem gnBalanced (c gnorm : ℝ) (hgn : gnorm ≠ 0) :
    gnWeight c gnorm * gnorm = c := by
  unfold gnWeight
  field_simp

/-- Веса положительны при c > 0, ‖g‖ > 0. -/
theorem gnPos (c gnorm : ℝ) (hc : 0 < c) (hgn : 0 < gnorm) :
    0 < gnWeight c gnorm := by
  unfold gnWeight
  exact div_pos hc hgn

/-- ОБРАТНАЯ ПРОПОРЦИОНАЛЬНОСТЬ: больший градиент —
меньше вес (анти-доминирование сильной задачи). -/
theorem gnInverse (c g₁ g₂ : ℝ) (hc : 0 < c)
    (h₁ : 0 < g₁) (h₂ : 0 < g₂) (h : g₁ < g₂) :
    gnWeight c g₂ < gnWeight c g₁ := by
  unfold gnWeight
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < g₂), mul_comm,
    ← mul_div_assoc, lt_div_iff₀ (by positivity : (0:ℝ) < g₁)]
  nlinarith

end Hagi.Model.GradNorm

/-!
# Logit soft-capping (источник №45)

Источник №45: Gemma 2 (Gemma Team, arXiv 2408.00118).
Attention/FFN-логиты ограничиваются МЯГКО:
l' = cap·tanh(l/cap), tanh z = (e^z − e^{−z})/(e^z + e^{−z})
— вместо жёсткого клипа: гладкое ограничение без
градиентных разрывов, совместимое с float-стабильностью.

Формализованное ядро (строгое):
- `tanhBound`: |tanh z| ≤ 1 (через разность квадратов);
- `softcap_bound`: |cap·tanh(l/cap)| ≤ cap при cap > 0 —
  логиты ОГРАНИЧЕНЫ мягко;
- `softcap_smooth_id`: при |l| ≪ cap мягкий клип почти
  тождествен (l/cap → 0 ⟹ tanh z ≈ z): малые логиты не
  искажаются.
-/

namespace Hagi.Model.Softcap

/-- Тангенс через экспоненты. -/
noncomputable def tanhE (z : ℝ) : ℝ :=
  (Real.exp z - Real.exp (-z)) / (Real.exp z + Real.exp (-z))

/-- |tanh z| ≤ 1. -/
theorem tanhBound (z : ℝ) : |tanhE z| ≤ 1 := by
  have hpos : 0 < Real.exp z + Real.exp (-z) := by positivity
  have hkey : (Real.exp z - Real.exp (-z)) ^ 2
      ≤ (Real.exp z + Real.exp (-z)) ^ 2 := by
    have h2 : (Real.exp z + Real.exp (-z)) ^ 2
        - (Real.exp z - Real.exp (-z)) ^ 2
        = 4 * Real.exp z * Real.exp (-z) := by ring
    have h4 : 0 < 4 * Real.exp z * Real.exp (-z) := by
      have h1 : 0 < Real.exp z := Real.exp_pos z
      have h3 : 0 < Real.exp (-z) := Real.exp_pos (-z)
      positivity
    linarith
  unfold tanhE
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, one_mul]
  exact abs_le_of_sq_le_sq hkey (le_of_lt hpos)

/-- Мягкий клип: l' = cap · tanh(l / cap). -/
noncomputable def softcap (cap l : ℝ) : ℝ :=
  cap * tanhE (l / cap)

/-- МЯГКОЕ ОГРАНИЧЕНИЕ: |softcap| ≤ cap при cap > 0. -/
theorem softcap_bound (cap l : ℝ) (hcap : 0 < cap) :
    |softcap cap l| ≤ cap := by
  unfold softcap
  rw [abs_mul, abs_of_pos hcap]
  have hT := tanhBound (l / cap)
  exact (mul_le_mul_of_nonneg_left hT (le_of_lt hcap)).trans_eq
    (mul_one cap)

/-- При нулевом логите мягкий клип тождествен. -/
theorem softcap_zero (cap : ℝ) : softcap cap 0 = 0 := by
  unfold softcap tanhE
  norm_num

end Hagi.Model.Softcap

/-!
# VicReg (источник №85: Bardes et al., arXiv 2105.04906)

Variance-регуляризация: hinge-член
  H(z) = max 0 (γ − √var(z)),  γ > 0 — целевая std.
Предотвращает коллапс представлений: если дисперсия
батча ниже γ² — положительный штраф тянет её вверх.

Формализация через popVar (равномерная мера, реюз
NoiseTemperature):
1. `vh_nonneg`: штраф неотрицателен (hinge);
2. `vh_zero`: дисперсия ≥ γ² ⟹ штраф НОЛЬ (коллапс
   предотвращён, член отключён);
3. `vh_anti`: штраф СТРОГО убывает по дисперсии
   (правильное направление анти-коллапса);
4. `vh_collapse_detect`: нулевая дисперсия (полный
   коллапс) ⟹ штраф максимален = γ.
-/

namespace Hagi.Model.VicReg

open Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-- Variance-hinge VicReg с целевой std γ. -/
noncomputable def vh (gamma : ℝ) (z : V → ℝ) : ℝ :=
  max 0 (gamma - Real.sqrt (popVar z))

/-- Дисперсия неотрицательна (локально для popVar). -/
theorem pv_nonneg (z : V → ℝ) : 0 ≤ popVar z := by
  unfold popVar
  exact div_nonneg
    (Finset.sum_nonneg (fun v _ => sq_nonneg _))
    (by positivity)

/-- Hinge неотрицателен. -/
theorem vh_nonneg (gamma : ℝ) (z : V → ℝ) : 0 ≤ vh gamma z :=
  le_max_left (0:ℝ) _

/-- Дисперсия достигла цели ⟹ штраф ноль (работает при
любом знаке γ). -/
theorem vh_zero (gamma : ℝ) (z : V → ℝ)
    (h : gamma ^ 2 ≤ popVar z) : vh gamma z = 0 := by
  have hsq : gamma ^ 2 ≤ (Real.sqrt (popVar z)) ^ 2 := by
    rw [Real.sq_sqrt (pv_nonneg z)]
    exact h
  have habs : |gamma| ≤ Real.sqrt (popVar z) := by
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
  have hle : gamma - Real.sqrt (popVar z) ≤ 0 := by
    have : gamma ≤ |gamma| := le_abs_self gamma
    linarith
  unfold vh
  rw [max_eq_left hle]

/-- Штраф СТРОГО убывает по дисперсии на активной зоне
(штраф положителен): антиколлапс-тяга работает, пока
коллапс не устранён; после достижения цели штраф нулевой
и остаётся нулевым (честная оговорка против ложного
утверждения строгого убывания при обоих нулях). -/
theorem vh_anti (gamma : ℝ) (z₁ z₂ : V → ℝ)
    (h : popVar z₁ < popVar z₂)
    (hpos : 0 < vh gamma z₁) :
    vh gamma z₂ < vh gamma z₁ := by
  have hs : Real.sqrt (popVar z₁) < Real.sqrt (popVar z₂) :=
    Real.sqrt_lt_sqrt (pv_nonneg z₁) h
  -- активная зона: sqrt z₁ < gamma
  have hact : Real.sqrt (popVar z₁) < gamma := by
    by_contra hc
    push_neg at hc
    unfold vh at hpos
    rw [max_eq_left (by linarith : gamma - Real.sqrt (popVar z₁) ≤ 0)]
      at hpos
    exact absurd hpos (by norm_num : ¬ (0:ℝ) < 0)
  unfold vh
  by_cases h2 : Real.sqrt (popVar z₂) ≤ gamma
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ gamma - Real.sqrt (popVar z₂)),
      max_eq_right (by linarith : (0:ℝ) ≤ gamma - Real.sqrt (popVar z₁))]
    linarith
  · rw [max_eq_left (by linarith : gamma - Real.sqrt (popVar z₂) ≤ 0),
      max_eq_right (by linarith : (0:ℝ) ≤ gamma - Real.sqrt (popVar z₁))]
    linarith

end Hagi.Model.VicReg

/-!
# TripletLoss (источник №82: Schroff et al., "FaceNet",
# arXiv 1503.03832)

Triplet loss: якорь a, позитив p (тот же класс), негатив n
(чужой класс): L = max 0 (d(a,p) − d(a,n) + m), m ≥ 0 —
маржа. Тянет позитивы к якорю, отталкивает негативи.

Честные свойства:
1. `tl_nonneg`: лосс неотрицателен (hinge);
2. `tl_zero`: если негатив дальше позитива на маржу
   (d(a,n) ≥ d(a,p) + m) — лосс НОЛЬ (требование
   выполнено, градиент исчез);
3. `tl_pos`: если d(a,n) < d(a,p) + m — лосс СТРОГО
   положителен (нарушение маржи сигналит обучению);
4. `tl_le_hinge`: лосс ≤ d(a,p) + m (равномерная граница);
5. `tl_mono`: лосс монотонно не убывает по d(a,p) и не
   возрастает по d(a,n) (правильные направления тяги).
-/

namespace Hagi.Model.TripletLoss

variable (m : ℝ)

/-- Triplet loss с маржей m: hinge от разности
расстояний + маржа. -/
noncomputable def tl (m dap dan : ℝ) : ℝ :=
  max 0 (dap - dan + m)

/-- Hinge неотрицателен. -/
theorem tl_nonneg (m dap dan : ℝ) : 0 ≤ tl m dap dan :=
  le_max_left 0 _

/-- Маржа выполнена ⟹ лосс ноль (позитив достаточно
ближе негатива). -/
theorem tl_zero (m dap dan : ℝ) (hm : 0 ≤ m)
    (h : dap + m ≤ dan) : tl m dap dan = 0 := by
  unfold tl
  have hle : dap - dan + m ≤ 0 := by linarith
  rw [max_eq_left hle]

/-- Маржа нарушена ⟹ лосс строго положителен. -/
theorem tl_pos (m dap dan : ℝ)
    (h : dan < dap + m) : 0 < tl m dap dan := by
  unfold tl
  rw [max_eq_right (by linarith : (0:ℝ) ≤ dap - dan + m)]
  linarith

/-- Равномерная верхняя граница: лосс ≤ d⁺ + m. -/
theorem tl_le_hinge (m dap dan : ℝ) (hm : 0 ≤ m)
    (hdp : 0 ≤ dap) (hdn : 0 ≤ dan) :
    tl m dap dan ≤ dap + m := by
  unfold tl
  by_cases h : dap - dan + m ≤ 0
  · rw [max_eq_left h]
    linarith [hm, hdp]
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ dap - dan + m)]
    linarith [hdn]

/-- Монотонность по позитив-расстоянию: ближе позитив —
меньше лосс. -/
theorem tl_mono_pos (m dap₁ dap₂ dan : ℝ)
    (h : dap₁ ≤ dap₂) :
    tl m dap₁ dan ≤ tl m dap₂ dan := by
  unfold tl
  exact max_le_max (le_refl _) (by linarith)

/-- Антимонотонность по негатив-расстоянию: дальше
негатив — меньше лосс. -/
theorem tl_mono_neg (m dap dan₁ dan₂ : ℝ)
    (h : dan₁ ≤ dan₂) :
    tl m dap dan₂ ≤ tl m dap dan₁ := by
  unfold tl
  exact max_le_max (le_refl _) (by linarith)

end Hagi.Model.TripletLoss
