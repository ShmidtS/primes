/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.NCE

set_option linter.style.header false

/-!
# NCEVar — точное тождество дисперсии K-негативной оценки и адаптивный K

Оценка — среднее K i.i.d. копий статистики f из предложения q.

* `secondMoment` / `qMean`: `E_q[f²] = Σ q·f²` и `μ = Σ q·f`;
* `nce_var_identity`: алгебраическое тождество
  `(E_q[f²] − μ²)/K = (1/K)·(E_q[f²] − μ²)`;
* `secondMoment_ge_mean_sq`: при `0 ≤ q v`, `Σ q = 1` —
  `μ² ≤ E_q[f²]` (Cauchy–Schwarz);
* `adaptiveK_bound`: при `0 ≤ moment`, `0 < eps` и
  `moment/eps ≤ K` — `(1/K)·moment ≤ eps` (правило выбора K
  под бюджет дисперсии; moment — измеренная центральная
  вторая момента, табличная статистика корпуса).
-/

open Finset

namespace Hagi.Step

section NCEVar

variable {V : Type*} [Fintype V]

/-- Вторая момента статистики под предложением:
`secondMoment q f = Σ_v q v·(f v)²`. -/
noncomputable def secondMoment (q : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ v, q v * (f v)^2

/-- Среднее статистики под предложением:
`qMean q f = Σ_v q v·f v`. -/
noncomputable def qMean (q : V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ v, q v * f v

/-- `(secondMoment q f − (qMean q f)²)/K
= (1/K)·(secondMoment q f − (qMean q f)²)`. -/
theorem nce_var_identity (q f : V → ℝ) (K : ℕ) (hK : 0 < K) :
    (secondMoment q f - (qMean q f)^2) / K
      = (1 / (K : ℝ)) * (secondMoment q f - (qMean q f)^2) := by
  field_simp

/-- При `0 ≤ q v` для всех v и `Σ q = 1`:
`(qMean q f)² ≤ secondMoment q f` (Cauchy–Schwarz). -/
theorem secondMoment_ge_mean_sq (q f : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1) :
    (qMean q f)^2 ≤ secondMoment q f := by
  -- Cauchy-Schwarz with a := √q, b := √q·f:
  -- (Σ q·f)² ≤ (Σ q)(Σ q·f²) = Σ q·f²
  have hsq : ∀ v : V, (Real.sqrt (q v))^2 = q v :=
    fun v => Real.sq_sqrt (hq v)
  have hcs : (∑ v, Real.sqrt (q v) * (Real.sqrt (q v) * f v))^2
      ≤ (∑ v, (Real.sqrt (q v))^2)
          * ∑ v, (Real.sqrt (q v) * f v)^2 :=
    sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun v => Real.sqrt (q v)) (fun v => Real.sqrt (q v) * f v)
  -- LHS = (Σ q·f)² = μ²
  have hL : ∑ v, Real.sqrt (q v) * (Real.sqrt (q v) * f v)
      = ∑ v, q v * f v := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (q v) * Real.sqrt (q v) = q v :=
      Real.mul_self_sqrt (hq v)
    linear_combination f v * h2
  -- first factor RHS = Σ q = 1
  have hR1 : ∑ v, (Real.sqrt (q v))^2 = 1 := by
    rw [Finset.sum_congr rfl fun v _ => hsq v]
    exact hq1
  -- second factor RHS = Σ q·f²
  have hR2 : ∑ v, (Real.sqrt (q v) * f v)^2
      = ∑ v, q v * f v^2 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (q v) * Real.sqrt (q v) = q v :=
      Real.mul_self_sqrt (hq v)
    linear_combination (f v)^2 * h2
  rw [hL, hR1, hR2] at hcs
  rw [one_mul] at hcs
  exact hcs

/-- При `0 ≤ moment`, `0 < eps` и `moment/eps ≤ (K:ℝ)`:
`(1/K)·moment ≤ eps`. -/
theorem adaptiveK_bound (moment : ℝ) (hmoment : 0 ≤ moment)
    (eps : ℝ) (heps : 0 < eps) (K : ℕ)
    (hK : moment / eps ≤ (K : ℝ)) :
    (1 / (K : ℝ)) * moment ≤ eps := by
  rcases eq_or_lt_of_le hmoment with heq | hpos
  · rw [← heq]
    norm_num
    exact le_of_lt heps
  · have hKpos : 0 < (K : ℝ) := by
      by_contra h
      push Not at h
      have hK0 : (K : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg K)
      rw [hK0] at hK
      have hcontra : 0 < moment / eps := div_pos hpos heps
      have : moment / eps ≤ 0 := hK
      linarith
    have h1 : moment ≤ (K : ℝ) * eps := by
      rwa [div_le_iff₀ heps] at hK
    have h2 : (1 / (K : ℝ)) * moment
        ≤ (1 / (K : ℝ)) * ((K : ℝ) * eps) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (1 / (K : ℝ)) * ((K : ℝ) * eps) = eps := by
      field_simp
    linarith

end NCEVar

end Hagi.Step

namespace Hagi
export Hagi.Step (secondMoment qMean nce_var_identity secondMoment_ge_mean_sq adaptiveK_bound)
end Hagi
