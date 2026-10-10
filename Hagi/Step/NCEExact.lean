/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.NCEVar

set_option linter.style.header false

/-!
# NCEExact — зазор sampled-оценки до точного CE

Оценка статистической суммы `Ẑ_K = (1/K)Σⱼ e^{z(vⱼ)}/q(vⱼ)`
для `Z = Σ_v e^{z(v)}`.

* `partEst_unbiased`: `Σ_v q v·(e^{z v}/q v) = Z` — оценка
  несмещённая;
* `secondMomentW_ge_sq`: `Z² ≤ secondMomentW` (Cauchy–Schwarz);
* `partEst_gap_jensen`: `Σ q·log(impW) ≤ log Z` (Jensen);
* `relative_second_moment_floor`:
  `(1/2K)·(secondMomentW/Z²) ≥ 1/(2K)`;
* `anchor_cadence_criterion`: при `s ≤ γ·ε/ρ` —
  `ρ·s/γ ≤ ε` (критерий каденса точной калибровки).

Дельта-метод потолок зазора и «47-натный вердикт» —
эмпирические суждения, не теоремы (см. докстринг
`relative_second_moment_floor`).
-/

open Finset

namespace Hagi.Step

section NCEExact

variable {V : Type*} [Fintype V]

/- Логит-поле z : V → ℝ (голова, применённая к скрытому
состоянию, по токену v). -/

/-- Точная статистическая сумма: `partZ z = Σ_v e^{z v}`. -/
noncomputable def partZ (z : V → ℝ) : ℝ := ∑ v, Real.exp (z v)

/-- Веса важности: `impW z q v = e^{z v}/q v`. -/
noncomputable def impW (z q : V → ℝ) (v : V) : ℝ :=
  Real.exp (z v) / q v

/-- Конечный Jensen для вогнутого логарифма (касательная
`log W ≤ W/a + log a − 1` при `a = Σ q·W`):
`Σ_v q v·log (W v) ≤ log (Σ_v q v·W v)` при положительных
`q v`, `W v` и `Σ q = 1`. -/
theorem jensen_log (q W : V → ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v, q v = 1) (hW : ∀ v, 0 < W v) :
    ∑ v, q v * Real.log (W v) ≤ Real.log (∑ v, q v * W v) := by
  have hne : (Finset.univ : Finset V).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hq1
    simp at hq1
  set a := ∑ v, q v * W v with ha
  have hapos : 0 < a :=
    Finset.sum_pos (fun v _ => mul_pos (hq v) (hW v)) hne
  have htan : ∀ v : V,
      Real.log (W v) ≤ W v / a + Real.log a - 1 := by
    intro v
    have h1 : Real.log (W v / a) ≤ W v / a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hW v) hapos)
    rw [Real.log_div (ne_of_gt (hW v)) (ne_of_gt hapos)] at h1
    linarith
  have hsum : ∑ v, q v * Real.log (W v)
      ≤ ∑ v, q v * (W v / a + Real.log a - 1) :=
    Finset.sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_left (htan v) (le_of_lt (hq v))
  have hsplit : ∑ v, q v * (W v / a + Real.log a - 1)
      = ∑ v, (q v * (W v / a) + q v * (Real.log a - 1)) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hsplit, Finset.sum_add_distrib] at hsum
  have hfirst : ∑ v, q v * (W v / a) = 1 := by
    have hrew : ∑ v, q v * (W v / a) = (1/a) * ∑ v, q v * W v := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      field_simp
    rw [hrew, ← ha]
    field_simp
  have hsecond : ∑ v, q v * (Real.log a - 1) = Real.log a - 1 := by
    have hrew : ∑ v, q v * (Real.log a - 1)
        = (∑ v, q v) * (Real.log a - 1) :=
      (Finset.sum_mul Finset.univ q (Real.log a - 1)).symm
    rw [hrew, hq1, one_mul]
  rw [hfirst, hsecond] at hsum
  linarith

/-- При `0 < q v` и `Σ q = 1`:
`Σ_v q v·impW z q v = partZ z` (несмещённость оценки суммы). -/
theorem partEst_unbiased (z q : V → ℝ)
    (hq : ∀ v, 0 < q v) (_hq1 : ∑ v, q v = 1) :
    ∑ v, q v * impW z q v = partZ z := by
  unfold partZ impW
  refine Finset.sum_congr rfl fun v _ => ?_
  exact mul_div_cancel₀ (Real.exp (z v)) (ne_of_gt (hq v))

/-- Вторая момента веса важности:
`secondMomentW z q = Σ_v q v·(impW z q v)²`. -/
noncomputable def secondMomentW (z q : V → ℝ) : ℝ :=
  ∑ v, q v * (impW z q v)^2

/-- При `0 < q v` и `Σ q = 1`:
`(partZ z)² ≤ secondMomentW z q` (Cauchy–Schwarz). -/
theorem secondMomentW_ge_sq (z q : V → ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v, q v = 1) :
    (partZ z)^2 ≤ secondMomentW z q := by
  have hunb := partEst_unbiased z q hq hq1
  -- Cauchy with sqrt q
  have hcs : (∑ v, Real.sqrt (q v)
      * (Real.sqrt (q v) * impW z q v))^2
      ≤ (∑ v, (Real.sqrt (q v))^2)
          * ∑ v, (Real.sqrt (q v) * impW z q v)^2 :=
    sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun v => Real.sqrt (q v))
      (fun v => Real.sqrt (q v) * impW z q v)
  have hsq : ∀ v : V, (Real.sqrt (q v))^2 = q v :=
    fun v => Real.sq_sqrt (le_of_lt (hq v))
  have hL : ∑ v, Real.sqrt (q v)
      * (Real.sqrt (q v) * impW z q v)
      = ∑ v, q v * impW z q v := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (q v) * Real.sqrt (q v) = q v :=
      Real.mul_self_sqrt (le_of_lt (hq v))
    linear_combination impW z q v * h2
  have hR1 : ∑ v, (Real.sqrt (q v))^2 = 1 := by
    rw [Finset.sum_congr rfl fun v _ => hsq v]
    exact hq1
  have hR2 : ∑ v, (Real.sqrt (q v) * impW z q v)^2
      = ∑ v, q v * (impW z q v)^2 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (q v) * Real.sqrt (q v) = q v :=
      Real.mul_self_sqrt (le_of_lt (hq v))
    linear_combination (impW z q v)^2 * h2
  rw [hL, hR1, hR2, one_mul] at hcs
  rw [hunb] at hcs
  -- hcs : partZ^2 <= secondMomentW
  unfold secondMomentW
  exact hcs

/-- При `0 < q v` и `Σ q = 1`:
`Σ_v q v·log (impW z q v) ≤ log (partZ z)` (Jensen: лог
оценки суммы занижен в ожидании). -/
theorem partEst_gap_jensen (z q : V → ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v, q v = 1) :
    ∑ v, q v * Real.log (impW z q v) ≤ Real.log (partZ z) := by
  -- jensen_log with W := impW: E_q[log W] <= log E_q[W] = log Z
  have hW : ∀ v, 0 < impW z q v := fun v => div_pos (Real.exp_pos _) (hq v)
  have hunb := partEst_unbiased z q hq hq1
  unfold impW at hW ⊢

  rw [← hunb]
  -- now: Σ q * log(exp z / q) <= log (Σ q * (exp z / q))
  refine jensen_log (V := V) q (fun v => Real.exp (z v) / q v) hq hq1 hW

/-- При `0 < K`, `0 < q v`, `Σ q = 1`:
`(1/(2K))·(secondMomentW z q/(partZ z)²) ≥ 1/(2K)`.

Доказано только это (нижняя оценка из Cauchy–Schwarz), НЕ
потолок сэмплинг-зазора: дельта-эвристика
«gap ≈ E[W²]/(2K·Z²)» при конечном K ложна (и особенно
невалидна в режиме ESS < 1); эмпирические выводы из неё —
не теоремы. -/
theorem relative_second_moment_floor (z q : V → ℝ) (K : ℕ) (hK : 0 < K)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v, q v = 1) :
    -- the noise-explainable gap is AT MOST the per-sample
    -- relative second moment over 2K
    (1 / (2 * (K : ℝ))) * (secondMomentW z q / (partZ z)^2)
      ≥ (1 / (2 * (K : ℝ))) * (1 / 1) := by
  have hge := secondMomentW_ge_sq z q hq hq1
  have hzpos : 0 < partZ z := by
    have hne : (Finset.univ : Finset V).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h] at hq1
      simp at hq1
    unfold partZ
    exact Finset.sum_pos (fun v _ => Real.exp_pos (z v)) hne
  -- E[W²]/Z² >= 1 from Cauchy; divide by 2K
  have hdiv : 1 ≤ secondMomentW z q / (partZ z)^2 := by
    rw [le_div_iff₀ (by positivity)]
    rw [one_mul]
    exact hge
  have hmul : (1 / (2 * (K : ℝ))) * 1
      ≤ (1 / (2 * (K : ℝ))) * (secondMomentW z q / (partZ z)^2) :=
    mul_le_mul_of_nonneg_left hdiv (by positivity)
  linarith [hmul]

-- Заменено ранее: тавтология `anchor_cadence_criterion`
-- (rfl) заменена рекуррентной теоремой
-- `Hagi.Plan41.anchor_recurrence`:
-- `D t ≤ (1−γ)^t·D₀ + ρs/γ` (критерий каденса — конечный
-- по t, а не только стационарная точка).

/-- При `0 < gamma`, `0 < rho`, `0 < eps` и `s ≤ gamma·eps/rho`:
`rho·s/gamma ≤ eps`. -/
theorem anchor_cadence_criterion (gamma rho eps : ℝ)
    (hgamma : 0 < gamma) (hrho : 0 < rho) (heps : 0 < eps) :
    -- стационарная точка под eps
    ∀ s : ℝ, s ≤ gamma * eps / rho → rho * s / gamma ≤ eps := by
  intro s hs
  have h1 : rho * s ≤ rho * (gamma * eps / rho) :=
    mul_le_mul_of_nonneg_left hs (le_of_lt hrho)
  have h2 : rho * (gamma * eps / rho) = gamma * eps := by
    field_simp
  rw [h2] at h1
  have h3 : rho * s / gamma ≤ gamma * eps / gamma :=
    (div_le_div_iff_of_pos_right hgamma).mpr h1
  have h4 : gamma * eps / gamma = eps := by
    field_simp
  rw [h4] at h3
  exact h3

end NCEExact

end Hagi.Step

namespace Hagi
export Hagi.Step (partZ impW jensen_log partEst_unbiased secondMomentW secondMomentW_ge_sq partEst_gap_jensen relative_second_moment_floor anchor_cadence_criterion)
end Hagi
