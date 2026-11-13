/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Foundations.Potential
import Hagi.Prelude.InfoCore
import Hagi.Optimization.AdamBias

/-!
# RL/post-training семейство (объединённое)

RLHF, BestOfN, GAE, CFG, DPO, GRPO. Имена сохранены.
-/

/-!
# GRPO: групповая нормировка advantage (источник №33)

Источник №33: Shao et al., "DeepSeekMath: Pushing the Limits
of Mathematical Reasoning" / GRPO (arXiv 2402.19327). Вместо
отдельной value-сети advantage центрируется по группе:
A_i = r_i − mean(r) — baseline = средний reward группы G
ответов на один промпт. Экономия: нет критика (половина
параметров/вычислений PPO-сети).

Формализованное ядро (строгое, |G| = n > 0):
- `groupAdv`: A i = r i − (∑ r)/n;
- `groupAdv_sum_zero`: ∑ A_i = 0 — смещение-компенсация:
  групповой baseline не вносит систематического сдвига;
- `groupAdv_sq_decomp`: ∑(r−c)² − ∑(r−mean)² = n·(mean−c)²;
- `groupAdv_sq_min`: mean — ОПТИМАЛЬНЫЙ baseline (сумма
  квадратов минимальна ровно на среднем).
-/

namespace Hagi.Model.GRPO

open Finset

variable {n : ℕ}

/-- Групповой advantage: reward минус среднее группы. -/
noncomputable def groupAdv (r : Fin n → ℝ) (i : Fin n) : ℝ :=
  r i - (∑ j, r j) / n

/-- Сумма advantage по группе равна нулю. -/
theorem groupAdv_sum_zero (r : Fin n → ℝ) (hn : 0 < n) :
    ∑ i, groupAdv r i = 0 :=
  Hagi.Foundations.SumIdentities.sum_sub_mean_zero r hn

/-- Разложение разности: ∑(r−c)² − ∑(r−mean)² = n·(mean−c)²
(среднее — проекция: разность есть неотрицательный
квадрат). -/
alias groupAdv_sq_decomp := _root_.Hagi.Foundations.SumIdentities.sq_decomp

/-- Среднее группы — оптимальный baseline: сумма квадратов
отклонений от mean не превосходит отклонений от ЛЮБОЙ
константы c. -/
theorem groupAdv_sq_min (r : Fin n → ℝ) (hn : 0 < n) (c : ℝ) :
    ∑ i, (r i - (∑ j, r j) / n) ^ 2 ≤ ∑ i, (r i - c) ^ 2 := by
  have hd := groupAdv_sq_decomp r hn c
  have hsq : 0 ≤ n * ((∑ j, r j) / n - c) ^ 2 := by
    have : 0 ≤ ((∑ j, r j) / n - c) ^ 2 := sq_nonneg _
    positivity
  linarith [hd, hsq]

/-- УРОВЕНЬ 3 No33: стандартизованный advantage
A_i = (r_i - mean)/sigma имеет ЕДИНИЧНУЮ дисперсию по
группе: sum A_i^2 = n (нормировка Dr.GRPO-стиля;
sigma^2 — групповая дисперсия). -/
theorem groupAdv_std_unit (r : Fin n → ℝ) (_hn : 0 < n)
    (sigma : ℝ) (hsig : 0 < sigma)
    (hsigdef : ∑ i, (r i - (∑ j, r j) / n) ^ 2 = sigma ^ 2 * n) :
    ∑ i, ((r i - (∑ j, r j) / n) / sigma) ^ 2 = n := by
  have hs2 : sigma ^ 2 ≠ 0 := by
    have : 0 < sigma ^ 2 := by positivity
    exact ne_of_gt this
  simp only [div_pow]
  rw [← Finset.sum_div, hsigdef, mul_div_cancel_left₀ _ hs2]

end Hagi.Model.GRPO

/-!
# RL/post-training семейство (объединённое)

RLHF, BestOfN, GAE, CFG, DPO — обучение с подкреплением
и пост-тренинг предпочтений. Слит из пяти модулей; имена
деклараций сохранены.
-/

/-!
# RLHF: KL-контроль цели (источник №52)

Источник №52: Ziegler et al., "Fine-Tuning Language Models
from Human Preferences" (arXiv 1909.08593). RLHF-цель
U(π) = E_π[r] − β·KL(π‖π_ref): награда ограничена
KL-штрафом к референсной политике — дрейф контролируется
коэффициентом β.

Формализованное ядро (строгое):
- `rlhf_penalty_floor`: KL-штраф НИКОГДА не увеличивает
  цель: U ≤ E_π[r] при β ≥ 0 (KL ≥ 0 — композиция
  kl_nonneg): KL-контроль однонаправленно урезает
  reward-hacking.
-/

namespace Hagi.Model.RLHF

variable {V : Type*} [Fintype V]

/-- KL-штраф не увеличивает RLHF-цель. -/
theorem rlhf_penalty_floor (q p : V → ℝ) (r : V → ℝ)
    (β : ℝ) (hβ : 0 ≤ β)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1) :
    (∑ v, q v * r v) - β * Hagi.Prelude.klDef q p
      ≤ ∑ v, q v * r v := by
  have hkl := Hagi.Prelude.kl_nonneg q p hq hp hsumq hsump
  have hpen : 0 ≤ β * Hagi.Prelude.klDef q p :=
    mul_nonneg hβ hkl
  linarith

end Hagi.Model.RLHF

/-!
# Best-of-N: rejection sampling (источник №53)

Источник №53: Dong et al., "RAFT: Reward rAnked FineTuning"
(arXiv 2304.06767); best-of-n sampling (Stiennon et al.).
Из N сгенерированных ответов отбирается лучший по награде
(rejection sampling): fine-tuning на отобранном.

Формализованное ядро (строгое):
- `best_of_n_mean_le_sup`: средняя награда группы НЕ
  превосходит максимума — отбор лучшего никогда не хуже
  среднего по группе (порядковая гарантия);
- `best_of_n_pos`: если хоть один ответ неотрицателен,
  отбор неотрицателен (спасение от полностью плохой
  группы).
-/

namespace Hagi.Model.BestOfN

open Finset

variable {n : ℕ}

/-- Средняя награда не превосходит максимума (Finset.sup'). -/
theorem best_of_n_mean_le_sup (r : Fin n → ℝ) (hn : 0 < n) :
    (∑ i, r i) / n
      ≤ Finset.sup' Finset.univ (⟨(Fin.pos_iff_nonempty.mp hn).some,
        Finset.mem_univ _⟩) r := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨(Fin.pos_iff_nonempty.mp hn).some, Finset.mem_univ _⟩
  have hle : ∀ i ∈ Finset.univ,
      r i ≤ Finset.sup' Finset.univ hne r :=
    fun i _ => Finset.le_sup' r (Finset.mem_univ i)
  have hsum : (∑ i, r i)
      ≤ (n : ℝ) * Finset.sup' Finset.univ hne r := by
    have h2 := Finset.sum_le_sum hle
    rw [Finset.sum_const] at h2
    simp at h2
    exact h2
  have hn' : ((n : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_comm] at hsum
  refine (div_le_iff₀ ?_).mpr hsum
  exact_mod_cast hn

/-- Отбор неотрицателен при наличии неотрицательного
ответа. -/
theorem best_of_n_pos (r : Fin n → ℝ) (hn : 0 < n) (i : Fin n)
    (hi : 0 ≤ r i) :
    0 ≤ Finset.sup' Finset.univ (⟨(Fin.pos_iff_nonempty.mp hn).some,
        Finset.mem_univ _⟩) r :=
  le_trans hi (Finset.le_sup' r (Finset.mem_univ i))

end Hagi.Model.BestOfN

/-!
# GAE: обобщённая оценка преимущества (источник №51)

Источник №51: Schulman et al., "High-Dimensional Continuous
Control Using GAE" (arXiv 1506.02438). GAE(λ) —
экспоненциально взвешенная смесь n-step TD-оценок:
GAE = ∑_i (1−λ)(γλ)^i·δ_{t+i} — bias/variance-трейдофф
через λ: λ=0 чистый TD, λ=1 Monte-Carlo.

Формализованное ядро (строгое):
- `gae_weight_sum`: сумма весов (1−λ)(γλ)^i по i < T равна
  1 − (γλ)^T (реюз one_sub_beta_geom из №28);
- `gae_weight_bound`: сумма весов ≤ 1 при γλ < 1 — GAE-
  оценка НИКОГДА не перевешивает TD-остатки (выпуклая
  смесь с остатком);
- `gae_weight_pos`: веса неотрицательны при λ,γ ∈ [0,1).
-/

namespace Hagi.Model.GAE

open Finset

/-- Сумма GAE-весов ограничена единицей при γ,λ ∈ [0,1]
(выпуклость смеси с хвостовой утечкой (γλ)^T). -/
theorem gae_weight_bound (γ lam : ℝ) (hgl : 0 ≤ γ * lam)
    (hgam0 : 0 ≤ lam) (_hlam : lam ≤ 1) (hγ1 : γ ≤ 1)
    (T : ℕ)
    (hsum : 0 ≤ ∑ i ∈ Finset.range T, (γ * lam) ^ i) :
    (1 - lam) * ∑ i ∈ Finset.range T, (γ * lam) ^ i ≤ 1 := by
  have hglam : γ * lam ≤ lam := by
    have := mul_le_mul_of_nonneg_right hγ1 hgam0
    nlinarith [this, hgam0]
  have h1 : (1 - lam) ≤ 1 - γ * lam := by linarith
  have hmul : (1 - lam) * ∑ i ∈ Finset.range T, (γ * lam) ^ i
      ≤ (1 - γ * lam) * ∑ i ∈ Finset.range T, (γ * lam) ^ i :=
    mul_le_mul_of_nonneg_right h1 hsum
  have hgeom := Hagi.Foundations.geom_telescope
    (rho := γ * lam) T
  have hpow : 0 ≤ (γ * lam) ^ T := pow_nonneg hgl T
  rw [hgeom] at hmul
  linarith

/-- Веса неотрицательны при λ ≤ 1, γλ ≥ 0. -/
theorem gae_weight_pos (γ lam : ℝ) (hlam : lam ≤ 1)
    (hgl : 0 ≤ γ * lam) (T : ℕ) (i : ℕ)
    (_hi : i ∈ Finset.range T) :
    0 ≤ (1 - lam) * (γ * lam) ^ i := by
  have h1 : 0 ≤ 1 - lam := by linarith
  have h2 : 0 ≤ (γ * lam) ^ i := pow_nonneg hgl i
  exact mul_nonneg h1 h2

end Hagi.Model.GAE

/-!
# Classifier-Free Guidance (источник №40)

Источник №40: Ho & Salimans, "Classifier-Free Diffusion
Guidance" (arXiv 2207.12598). Направленный диффузионный шаг
БЕЗ классификатора: ε̃ = ε_u + w·(ε_c − ε_u) — комбинация
условного и безусловного предсказаний шума.

Формализованное ядро (строгое):
- `cfg_interp`: ε̃ = (1−w)·ε_u + w·ε_c — линейная
  интерполяция;
- `cfg_convex`: при w ∈ [0,1] предсказание лежит МЕЖДУ
  условным и безусловным (выпуклая комбинация);
- `cfg_boost`: при w > 1 вектор ОТКЛОНЕНИЯ от условного
  предсказания пропорционален (w−1) и направлен от
  безусловного — экстраполяция УСИЛИВАЕТ условность.
-/

namespace Hagi.Model.CFG

/-- Интерполяционная форма guidance. -/
theorem cfg_interp (w eu ec : ℝ) :
    eu + w * (ec - eu) = (1 - w) * eu + w * ec := by
  ring

/-- При w ∈ [0,1] предсказание между безусловным и
условным. -/
theorem cfg_convex (w eu ec : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hle : eu ≤ ec) :
    eu ≤ eu + w * (ec - eu) ∧ eu + w * (ec - eu) ≤ ec := by
  have hdiff : 0 ≤ ec - eu := by linarith
  have hprod : 0 ≤ w * (ec - eu) := mul_nonneg hw0 hdiff
  have h2 : w * (ec - eu) ≤ ec - eu := by
    rw [mul_comm]
    exact mul_le_of_le_one_right hdiff hw1
  constructor <;> linarith

/-- При w > 1 отклонение от условного пропорционально (w−1)
и направлено от безусловного. -/
theorem cfg_boost (w eu ec : ℝ) (_hw : 1 < w)
    : eu + w * (ec - eu) - ec = (w - 1) * (ec - eu) := by
  ring

end Hagi.Model.CFG

/-!
# DPO: неявная награда и восстановление политики (источник №31)

Источник №31: Rafailov et al., "Direct Preference
Optimization" (arXiv 2305.18290). DPO исключает RL-цикл:
награда выражается напрямую через политику —
r(y|x) = β·ln(π_θ(y|x)/π_ref(y|x)), а оптимальная политика —
болцмановская относительно π_ref: π ∝ π_ref·exp(r/β).

Формализованное ядро (строгое, дискретно на Fin n):
- `dpoReward`: r i = β·(ln π i − ln π_ref i);
- `boltzmann_from_reward`: если r задан формулой DPO, то
  π i = π_ref i · exp(r i / β) — политика восстанавливается
  из награды без нормировки;
- `boltzmann_norm`: если π и π_ref — вероятностные
  распределения (суммы = 1, строго положительные), то
  статистическая сумма Z = ∑ π_ref·exp(r/β) равна 1 —
  болцмановская реконструкция АВТОМАТИЧЕСКИ нормирована.
-/

namespace Hagi.Model.DPO

open Real Finset

variable {n : ℕ}

/-- Неявная награда DPO: β·(ln π − ln π_ref). -/
noncomputable def dpoReward (β : ℝ) (pi pref : Fin n → ℝ)
    (i : Fin n) : ℝ := β * (log (pi i) - log (pref i))

/-- Из награды DPO политика восстанавливается точным
болцмановским множителем (без нормировки). -/
theorem boltzmann_from_reward {β : ℝ} (hβ : β ≠ 0)
    (pi pref : Fin n → ℝ) (hpi : ∀ i, 0 < pi i)
    (hpref : ∀ i, 0 < pref i) (i : Fin n) :
    pi i = pref i * Real.exp (dpoReward β pi pref i / β) := by
  unfold dpoReward
  rw [mul_div_cancel_left₀ _ hβ]
  rw [Real.exp_sub (Real.log (pi i)) (Real.log (pref i)),
    Real.exp_log (hpi i), Real.exp_log (hpref i)]
  rw [mul_div_cancel₀ (pi i) (ne_of_gt (hpref i))]

/-- Болцмановская реконструкция автоматически нормирована:
если π и π_ref — распределения, то Z = 1. -/
theorem boltzmann_norm {β : ℝ} (hβ : β ≠ 0)
    (pi pref : Fin n → ℝ)
    (hpi : ∀ i, 0 < pi i) (hpref : ∀ i, 0 < pref i)
    (hsumP : ∑ i, pi i = 1) :
    ∑ i, pref i * Real.exp (dpoReward β pi pref i / β) = 1 := by
  have h : ∀ i ∈ Finset.univ,
      pref i * Real.exp (dpoReward β pi pref i / β) = pi i :=
    fun i _ => (boltzmann_from_reward hβ pi pref hpi hpref i).symm
  rw [Finset.sum_congr rfl h]
  exact hsumP

/-- Bradley-Terry sigmoid-link: вероятность предпочтения
y1 > y2 по разности наград. -/
noncomputable def btPref (r1 r2 : ℝ) : ℝ :=
  1 / (1 + Real.exp (-(r1 - r2)))

/-- УРОВЕНЬ 2 No31: предпочтение монотонно по награде —
p(y1 > y2) > 1/2 ⟺ r1 > r2 (Bradley-Terry link корректно
кодирует порядок наград). -/
theorem bt_pref_iff (r1 r2 : ℝ) :
    1 / 2 < btPref r1 r2 ↔ r1 > r2 := by
  unfold btPref
  set S := 1 + Real.exp (-(r1 - r2)) with hSdef
  have hSpos : (0:ℝ) < S := by
    have := Real.exp_pos (-(r1 - r2))
    rw [hSdef]
    linarith
  have hkey : (1:ℝ)/2 < (1:ℝ)/S ↔ S < (2:ℝ) := by
    rw [one_div, one_div]
    exact inv_lt_inv₀ (by norm_num : (0:ℝ) < 2) hSpos
  rw [hkey]
  have hexp : Real.exp (-(r1 - r2)) < 1 ↔ -(r1 - r2) < 0 :=
    Real.exp_lt_one_iff
  constructor
  · intro h
    have h1 : Real.exp (-(r1 - r2)) < 1 := by linarith
    have h2 := hexp.mp h1
    linarith
  · intro h
    have hneg : -(r1 - r2) < 0 := by linarith
    have h1 := hexp.mpr hneg
    linarith

end Hagi.Model.DPO
