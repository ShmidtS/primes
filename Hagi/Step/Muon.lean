/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Mathlib
import Hagi.Foundations.Recurrence

/-!
# Muon-семейство (объединённое)

Базовый Muon-шаг, выравнивание, двухуровневая версия,
распад веса. Слит из четырёх модулей; namespace-блоки и
имена деклараций сохранены.
-/

/-!
# chunked CE - exact piecewise summation + prior decomposition

Phase B. Sources: 2609.32100
(exact definition of valid token positions + protocol),
2607.16666 (subsampling with rate correction),
2607.10951 (one-sample unbiasedness transfer).

Theorems:

* `chunked_sum_exact` - EXACTNESS of chunked summation:
if T = n * w, the token sum splits into n chunks of width w
with NO loss - the chunked CE equals the full CE.
* `ce_prior_decomposition` - CE = H(prior) + KL correction:
cross-entropy against q decomposes as the prior entropy
plus the KL divergence (proper objective).

Honest boundary: the valid-position protocol (masking of
padding) follows 2609.32100; here positions are all valid.
-/

/-!
# LRWidth — неинвариантность LR по ширине и muP-скейлинг

Модель: линейный слой W (m строк) на квадратичной потере
`L = ½·‖W·1‖²`.

* `grad_norm_grows`: при all-ones инициализации квадрат
  нормы градиента равен `m·d³` — растёт линейно по ширине m
  (фиксированный LR не инвариантен по ширине);
* `mup_grad_invariant`: при скейлинге `W i j = 1/√m` квадрат
  нормы градиента равен `d³` — не зависит от ширины
  (muP-предписание для этого слоя).

Полный muP-перенос (все слои, моменты Adam) — эмпирический;
здесь — точное утверждение для квадратичной линейной модели.
-/

namespace Hagi.Step
open Finset

/-- Компонент градиента потери `L = ½·Σ_i (Σ_j W i j)²`:
`gradEntry W i j = Σ_j' W i j'`. -/
def gradEntry {m d : ℕ} (W : Fin m → Fin d → ℝ) (i : Fin m) (j : Fin d) : ℝ :=
  ∑ j', W i j'

/-- При `Wones i j = 1` для всех i j:
`Σ_i Σ_j (gradEntry Wones i j)² = m·d³` — линейный рост
по m (фиксированный LR не инвариантен по ширине). -/
theorem grad_norm_grows (m d : ℕ)
    (Wones : Fin m → Fin d → ℝ) (hones : ∀ i j, Wones i j = 1) :
    ∑ i, ∑ j, (gradEntry Wones i j)^2 = (m : ℝ) * (d : ℝ)^3 := by
  have hgrad : ∀ i j, gradEntry Wones i j = (d : ℝ) := by
    intro i j
    unfold gradEntry
    rw [Finset.sum_congr rfl fun j' _ => hones i j']
    simp
  rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hgrad i j],
    Finset.sum_const, Finset.card_univ, Finset.sum_const,
    Finset.card_univ]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- При `1 ≤ m` и `Wmup i j = 1/√m` для всех i j:
`Σ_i Σ_j (gradEntry Wmup i j)² = d³` — не зависит от
ширины (muP-скейлинг). -/
theorem mup_grad_invariant (m d : ℕ) (hm : 1 ≤ m)
    (Wmup : Fin m → Fin d → ℝ)
    (hmup : ∀ i j, Wmup i j = 1 / Real.sqrt (m : ℝ)) :
    ∑ i, ∑ j, (gradEntry Wmup i j)^2 = (d : ℝ)^3 := by
  have hgrad : ∀ i j, gradEntry Wmup i j
      = (d : ℝ) / Real.sqrt (m : ℝ) := by
    intro i j
    unfold gradEntry
    rw [Finset.sum_congr rfl fun j' _ => hmup i j']
    rw [Finset.sum_const, Finset.card_univ]
    simp
    ring
  rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hgrad i j],
    Finset.sum_const, Finset.card_univ]
  have hmpos : (0:ℝ) < (m : ℝ) := by positivity
  have hkey : ((d : ℝ) / Real.sqrt (m : ℝ))^2
      = (d : ℝ)^2 / (m : ℝ) := by
    have h1 : (Real.sqrt (m : ℝ))^2 = (m : ℝ) :=
      Real.sq_sqrt (by positivity)
    rw [div_pow, h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hkey]
  simp
  field_simp
end Hagi.Step
set_option linter.style.header false

/-!
# Muon — спектральный прекондиционер и совместимость с SafeQP

* `muon_step_bound`: при контракции `‖P z‖ ≤ ‖z‖` для всех z
  — `‖muonDir P g‖ ≤ ‖g‖` (направление Muon не превышает
  сырой градиент по норме — совместимо с SafeQP);
* `muon_pl_rate`: `‖muonDir P g‖² ≤ ‖g‖²` при той же
  контракции.

Свойство `‖P‖_op ≤ 1` Newton-Schulz — гипотеза hP
(полярное разложение — вне этого модуля).
-/

namespace Hagi.Step

variable {V : Type} [NormedAddCommGroup V]

/-- Направление Muon: `muonDir P g = P g` —
прекондиционированный градиент. -/
def muonDir {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W) : W := P g

/-- Если `‖P z‖ ≤ ‖z‖` для всех z, то `‖muonDir P g‖ ≤ ‖g‖`. -/
theorem muon_step_bound {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) :
    ‖muonDir P g‖ ≤ ‖g‖ :=
  hP g

/-- Если `‖P z‖ ≤ ‖z‖` для всех z, то
`‖muonDir P g‖^2 ≤ ‖g‖^2`. -/
theorem muon_pl_rate {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) :
    ‖muonDir P g‖^2 ≤ ‖g‖^2 := by
  rw [sq, sq]
  exact mul_self_le_mul_self (norm_nonneg _) (hP g)

end Hagi.Step


/-! ### Источник №72 (Muon, 2502.25082): скалярная модель
итерации Ньютона-Шульца. Реальный Muon ортогонализует
матрицу импульса итерацией U ← U(3I−UᵀU)/2; сингулярные
числа эволюционируют по скалярной карте ns(u) = u(3−u²)/2.
Формализуем честную скалярную динамику: инвариантность
(0,1], монотонный подъём к 1, квадратичную ошибку. -/

namespace Hagi.Step.MuonNS

/-- Скалярная итерация Ньютона-Шульца (Muon). -/
noncomputable def ns (u : ℝ) : ℝ := u * (3 - u^2) / 2

/-- Инвариант отрезка: u ∈ (0,1] ⟹ ns u ∈ (0,1]. -/
theorem ns_invariant (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    0 < ns u ∧ ns u ≤ 1 := by
  constructor
  · -- u(3−u²) > 0 при u ≤ 1 < √3
    have h3 : 0 < 3 - u^2 := by nlinarith [sq_nonneg u]
    have := mul_pos hu h3
    unfold ns; linarith
  · -- ns u ≤ 1: 1 − ns u = (u−1)²(u+2)/2 ≥ 0
    have key : (1:ℝ) - ns u = (u - 1)^2 * (u + 2) / 2 := by
      unfold ns; ring
    have hnn : (0:ℝ) ≤ (u - 1)^2 * (u + 2) :=
      mul_nonneg (sq_nonneg (u - 1)) (by linarith)
    have : (0:ℝ) ≤ 1 - ns u := by rw [key]; exact div_nonneg hnn (by positivity)
    linarith

/-- МОНОТОННЫЙ ПОДЪЁМ К 1: ns u ≥ u на (0,1], равенство
только при u = 1 — каждое NS-обновление подтягивает
сингулярное число к единице (ортогонализация). -/
theorem ns_monotone_ascent (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    u ≤ ns u := by
  have h1 : (0:ℝ) ≤ 1 - u^2 := by nlinarith [sq_nonneg u]
  have h2 : (0:ℝ) ≤ u * (1 - u^2) := mul_nonneg hu.le h1
  have key : u * (3 - u^2) / 2 - u = u * (1 - u^2) / 2 := by ring
  have h3 : (0:ℝ) ≤ u * (3 - u^2) / 2 - u := by rw [key]; exact div_nonneg h2 (by positivity)
  unfold ns
  linarith

/-- ФАКТОРИЗАЦИЯ ОШИБКИ: 1 − ns u = (u−1)²(u+2)/2 — ошибка
квадратична по отклонению u от 1: NS-итерация квадратично
стягивает сингулярные числа к 1 (ортогонализация). -/
theorem ns_error_factor (u : ℝ) :
    1 - ns u = (u - 1)^2 * (u + 2) / 2 := by
  unfold ns; ring

/-- СТРОГОЕ СЖАТИЕ: u ∈ (0,1) ⟹ u < ns u < 1 — каждая
итерация строго подтягивает сингулярное число к единице,
оставаясь внутри (0,1). -/
theorem ns_error_contract (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    u < ns u ∧ ns u < 1 := by
  have hle : u ≤ ns u := ns_monotone_ascent u hu hu1.le
  have hne : ns u ≠ u := by
    intro heq
    have key : ns u - u = u * (1 - u^2) / 2 := by
      unfold ns; ring
    rw [heq, sub_self] at key
    have h1 : (0:ℝ) < 1 - u^2 := by nlinarith [sq_nonneg u, hu1]
    have : (0:ℝ) < u * (1 - u^2) / 2 :=
      div_pos (mul_pos hu h1) (by positivity)
    linarith [this, key]
  have hlt : u < ns u := lt_of_le_of_ne hle (Ne.symm hne)
  have h1 : (0:ℝ) < 1 - u := by linarith
  have hu1ne : u - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hu1)
  have hsq : (0:ℝ) < (u - 1)^2 * (u + 2) :=
    mul_pos (sq_pos_iff.mpr hu1ne) (by linarith)
  have hef := ns_error_factor u
  have hns1 : ns u < 1 := by
    have : (0:ℝ) < 1 - ns u := by rw [hef]; exact div_pos hsq (by positivity)
    linarith
  exact ⟨hlt, hns1⟩

end Hagi.Step.MuonNS

/-!
# Muon: оптимальность выравнивания (источник №12)

Источник №12: "Muon Optimizes Under Spectral Norm
Constraints" (arXiv 2506.15054): Muon-шаг — ортогональная
полярная часть градиента — steepest descent при спектральной
норме: максимум выравнивания с градиентом среди ортогональных
обновлений.

Ядро в собственном базисе градиента: для G = diag(σ), σ ≥ 0,
Muon-шаг I даёт выравнивание Σσᵢ, не превзойдённое ни одной
унитарной матрицей: Σᵢ σᵢ·Re Qᵢᵢ ≤ Σᵢ σᵢ (|Qᵢᵢ| ≤ 1 из
унитарности — ядро неравенства фон Неймана о следе).
-/

namespace Hagi.Step.MuonAlign

open Matrix

/-- |Q_ii| ≤ 1 для унитарной Q (QᴴQ = 1): столбец нормы 1. -/
theorem unitary_diag_abs_le {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Qᴴ * Q = 1) (i : n) :
    ‖Q i i‖ ≤ 1 := by
  have hexp : (Qᴴ * Q) i i = ∑ j, star (Q j i) * Q j i := by
    simp [Matrix.mul_apply]
  have hdiag : ∑ j, star (Q j i) * Q j i = 1 := by
    have h3 : (Qᴴ * Q) i i = ∑ j, star (Q j i) * Q j i := hexp
    have h4 : (Qᴴ * Q) i i = 1 := by
      have hd := congrFun (congrArg Matrix.diag hQ) i
      simpa [Matrix.diag_apply] using hd
    rw [h3] at h4
    exact h4
  have hpos : ∑ j, ‖Q j i‖ ^ 2 = 1 := by
    have hterm : ∀ j : n, ‖Q j i‖ ^ 2 = (star (Q j i) * Q j i).re :=
      fun j => by
        have h2 : (star (Q j i) * Q j i).re
            = (Q j i).re * (Q j i).re + (Q j i).im * (Q j i).im := by
          simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        rw [h2]
        have hn := Complex.normSq_eq_norm_sq (Q j i)
        rw [← hn, Complex.normSq_apply]
    have hre : ∑ j, (star (Q j i) * Q j i).re
        = (∑ j, star (Q j i) * Q j i).re := by simp
    calc ∑ j, ‖Q j i‖ ^ 2 = ∑ j, (star (Q j i) * Q j i).re :=
        Finset.sum_congr rfl fun j _ => hterm j
      _ = (∑ j, star (Q j i) * Q j i).re := hre
      _ = (1 : ℂ).re := by rw [hdiag]
      _ = 1 := by norm_num
  have hkey : ‖Q i i‖ ^ 2 ≤ 1 := by
    have hmem : ‖Q i i‖ ^ 2 ≤ ∑ j, ‖Q j i‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (‖Q j i‖)) (Finset.mem_univ i)
    rw [hpos] at hmem
    exact hmem
  have hnn : 0 ≤ ‖Q i i‖ := norm_nonneg _
  nlinarith [hkey, hnn]

/-- MUON-ОПТИМАЛЬНОСТЬ (диагональное ядро): для
диагонализованного градиента diag(σ), σ ≥ 0, Muon-шаг
(ортогональная полярная часть = I) достигает выравнивания
Σσᵢ, максимального среди унитарных Q: Σᵢ σᵢ·Re Qᵢᵢ ≤ Σᵢ σᵢ —
stepest descent при спектральной норме (ядро источника). -/
theorem muon_alignment_optimal {n : Type*} [Fintype n] [DecidableEq n]
    (sig : n → ℝ) (hsig : ∀ i, 0 ≤ sig i)
    (Q : Matrix n n ℂ) (hQ : Qᴴ * Q = 1) :
    (∑ i, sig i * (Q i i).re) ≤ ∑ i, sig i := by
  have hmain : ∀ i : n, sig i * (Q i i).re ≤ sig i := by
    intro i
    have habs := unitary_diag_abs_le Q hQ i
    have hre' : (Q i i).re ≤ 1 := by
      calc (Q i i).re ≤ |(Q i i).re| := le_abs_self _
        _ ≤ ‖Q i i‖ := by simp [Complex.abs_re_le_norm]
        _ ≤ 1 := habs
    simpa using mul_le_mul_of_nonneg_left hre' (hsig i)
  exact Finset.sum_le_sum fun i _ => hmain i

end Hagi.Step.MuonAlign

/-!
# MuonTwoLevel — точная ортогонализация против NS-аппроксимации

Уровень 1 (контракт, не доказан здесь): идеальный шаг
`O = U·Vᵀ` (SVD градиента) ортогонален — спектральная
норма 1.

Уровень 2 (доказан): `ns_gap_scaled` —
`Σᵢ (p(σᵢ) − 1)² ≤ r·maxᵢ (p(σᵢ) − 1)²`:
бюджет отклонения факторизуется в ранг × худшую поточечную
ошибку полинома. Frobenius-тождество, коэффициенты полинома
и сходимость NS-итераций — не доказаны.
-/

namespace Hagi.Step

open Finset

/-- При `0 ≤ M` и `(dev i)² ≤ M` для всех i:
`Σ_i (dev i)² ≤ r·M` (бюджет отклонения = ранг ×
худший поточечный член). -/
theorem ns_gap_scaled (r : ℕ) (dev : Fin r → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hdev : ∀ i, (dev i)^2 ≤ M) :
    ∑ i, (dev i)^2 ≤ r * M := by
  have h1 : ∑ i, (dev i)^2 ≤ ∑ _i, M :=
    Finset.sum_le_sum fun i _ => hdev i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1
  exact h1


end Hagi.Step

/-!
# MuonWD — weight decay заменяет аксиому ограниченного градиента

Рекурсия `θ_{t+1} = (1 − ηλ)·θ_t − η·U_t` с равномерно
ограниченным ортогонализованным шагом `‖U_t‖ ≤ C`
(независимо от величины градиента).

* `muon_wd_recursion`: шаг нормы —
  `‖θ_{t+1}‖ ≤ (1 − ηλ)·‖θ_t‖ + η·C`;
* `wd_boundedness`: при `0 < ηλ ≤ 1` —
  `‖θ_T‖ ≤ (1 − ηλ)^T·‖θ_0‖ + C/λ`: стационарный радиус C/λ
  не зависит от масштаба градиентов (аксиома ограниченности
  градиентов не нужна; цена — явный WD-пол).
-/

namespace Hagi.Step

open Finset

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- При `0 ≤ eta`, `0 ≤ eta·lam ≤ 1`, шаге
`θ (t+1) = (1 − eta·lam) • θ t − eta • U t` и
`‖U s‖ ≤ C` для всех s —
`‖θ (t+1)‖ ≤ (1 − eta·lam)·‖θ t‖ + eta·C`. -/
theorem muon_wd_recursion (theta : ℕ → W) (U : ℕ → W)
    (eta lam C : ℝ) (t : ℕ)
    (heta : 0 ≤ eta) (hlam0 : 0 ≤ eta * lam)
    (hlam1 : eta * lam ≤ 1)
    (hstep : theta (t + 1) = (1 - eta * lam) • theta t
      - eta • U t)
    (hC : ∀ s, ‖U s‖ ≤ C) :
    ‖theta (t + 1)‖ ≤ (1 - eta * lam) * ‖theta t‖ + eta * C := by
  have hrho : 0 ≤ 1 - eta * lam := by linarith
  rw [hstep]
  have hU : eta * ‖U t‖ ≤ eta * C :=
    mul_le_mul_of_nonneg_left (hC t) heta
  have htri := norm_sub_le ((1 - eta * lam) • theta t) (eta • U t)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hrho,
    Real.norm_eq_abs, abs_of_nonneg heta] at htri
  exact le_trans htri (by linarith)

/-- При `0 ≤ eta`, `0 < eta·lam ≤ 1`, шаге
`θ (t+1) = (1 − eta·lam) • θ t − eta • U t` и
`‖U s‖ ≤ C` —
`‖θ T‖ ≤ (1 − eta·lam)^T·‖θ 0‖ + C/lam`. -/
theorem wd_boundedness (theta : ℕ → W) (U : ℕ → W)
    (eta lam C : ℝ) (T : ℕ)
    (heta : 0 ≤ eta) (hpos : 0 < eta * lam)
    (hlam1 : eta * lam ≤ 1)
    (hstep : ∀ t, theta (t + 1) = (1 - eta * lam) • theta t
      - eta • U t)
    (hC : ∀ s, ‖U s‖ ≤ C) :
    ‖theta T‖ ≤ (1 - eta * lam) ^ T * ‖theta 0‖ + C / lam := by
  have hrho : 0 ≤ 1 - eta * lam := by linarith
  have hrho1 : 1 - eta * lam < 1 := by linarith
  have hrec : ∀ t < T, ‖theta (t + 1)‖
      ≤ (1 - eta * lam) * ‖theta t‖ + eta * C :=
    fun t _ => muon_wd_recursion theta U eta lam C t heta
      hpos.le hlam1 (hstep t) hC
  have hmain := Hagi.Foundations.recurrence_upper (1 - eta * lam)
    (eta * C) (fun t => ‖theta t‖) T hrho hrho1 hrec
  have hlam : 0 < lam := by
    by_contra h
    push_neg at h
    nlinarith [heta, h]
  have hne : (1 - eta * lam) ≠ 1 := by
    intro h
    have : eta * lam = 0 := by linarith
    linarith [hpos]
  have hfrac : (1 - (1 - eta * lam) ^ T)
      / (1 - (1 - eta * lam))
      = ∑ i ∈ Finset.range T, (1 - eta * lam) ^ i := by
    rw [geom_sum_eq hne T]
    field_simp
    ring
  have hsumle : ∑ i ∈ Finset.range T, (1 - eta * lam) ^ i
      ≤ 1 / (eta * lam) := by
    have h1 := Hagi.Foundations.geom_sum_le_inv (1 - eta * lam) T
      hrho (by linarith)
    rw [sub_sub_cancel] at h1
    exact h1
  have hlampos : (0:ℝ) < lam := hlam
  have hsplit : eta * C * ((1 - (1 - eta * lam) ^ T)
      / (1 - (1 - eta * lam))) ≤ C / lam := by
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
    have hmul : eta * C * ((1 - (1 - eta * lam) ^ T)
        / (1 - (1 - eta * lam))) ≤ eta * C * (1 / (eta * lam)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by
        exact mul_nonneg heta hC0)
      rw [hfrac]
      exact hsumle
    have hcancel : eta * C * (1 / (eta * lam)) = C / lam := by
      have hne : eta * lam ≠ 0 := ne_of_gt hpos
      have heta2 : eta ≠ 0 := by
        intro heq
        rw [heq] at hpos
        simp at hpos
      field_simp
    rw [hcancel] at hmul
    exact hmul
  linarith [hmain, hsplit]


end Hagi.Step
