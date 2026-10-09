/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# WeightedVar — the weighted-variance core

`dQuad_nonneg`: for probability weights and any deviation
field, the squared weighted mean never exceeds the weighted
second moment (weighted Cauchy-Schwarz).
-/

namespace Hagi.Foundations

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Weighted variance nonnegativity: for probability
weights `pW`, `(∑ v, pW v * d v) ^ 2 ≤ ∑ v, pW v * d v ^ 2`. -/
theorem dQuad_nonneg (pW : V → ℝ) (d : V → ℝ)
    (hpW : ∀ v, 0 ≤ pW v) (hpW1 : ∑ v, pW v = 1) :
    (∑ v, pW v * d v)^2 ≤ ∑ v, pW v * d v^2 := by
  have hcs : (∑ v, Real.sqrt (pW v) * (Real.sqrt (pW v) * d v))^2
      ≤ (∑ v, (Real.sqrt (pW v))^2) * ∑ v, (Real.sqrt (pW v) * d v)^2 :=
    sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun v => Real.sqrt (pW v)) (fun v => Real.sqrt (pW v) * d v)
  have hsq : ∀ v : V, (Real.sqrt (pW v))^2 = pW v :=
    fun v => Real.sq_sqrt (hpW v)
  have hL : ∑ v, Real.sqrt (pW v) * (Real.sqrt (pW v) * d v)
      = ∑ v, pW v * d v := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (pW v) * Real.sqrt (pW v) = pW v :=
      Real.mul_self_sqrt (hpW v)
    linear_combination d v * h2
  have hR1 : ∑ v, (Real.sqrt (pW v))^2 = 1 := by
    rw [Finset.sum_congr rfl fun v _ => hsq v]
    exact hpW1
  have hR2 : ∑ v, (Real.sqrt (pW v) * d v)^2
      = ∑ v, pW v * d v^2 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have h2 : Real.sqrt (pW v) * Real.sqrt (pW v) = pW v :=
      Real.mul_self_sqrt (hpW v)
    linear_combination (d v)^2 * h2
  rw [hL, hR1, hR2, one_mul] at hcs
  exact hcs

end Hagi.Foundations
