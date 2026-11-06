/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.GatedCESafeStep

/-!
# Positive curvature from positive gated alignment

Positive alignment supplies a nonzero residual-transpose coordinate.  Expanding
that coordinate gives a residual-mediated feature, hence a strictly positive
term in the residual second-order mass.  The remaining finite-sum terms are
nonnegative, so the full curvature is positive and the safe step is exactly
its stationary quadratic-minimizer branch.

The finite-sum positivity route uses Mathlib's `Finset.sum_pos'` from
`Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`.  No saturation,
nonzero-feature, uniform-curvature, or convergence premise is used.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.GatedCEPositiveCurvature

open Hagi.Model.GatedCEGradient
open Hagi.Model.GatedCEDescent
open Hagi.Model.GatedCESafeStep

variable {V : Type} [Fintype V]
variable {d : ℕ}

/-- Positive alignment makes the residual second-order mass strictly positive. -/
theorem gatedResidualSecondOrderMass_pos_of_alignment_pos
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hA : 0 < gatedAlignment X θ t) :
    0 < gatedResidualSecondOrderMass X θ (gatedDirection X θ t) t := by
  classical
  have hexj : ∃ j, gatedResidualTranspose X θ t j ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : gatedAlignment X θ t = 0 := by
      unfold gatedAlignment
      apply Finset.sum_eq_zero
      intro j _hj
      rw [h j]
      norm_num
    linarith
  obtain ⟨j, hj⟩ := hexj
  have hexpand : gatedResidualTranspose X θ t j =
      (∑ v, gatedResidual X θ t v * X v j) *
        (1 / (Real.cosh (θ.ofLp j)) ^ 2) := by
    unfold gatedResidualTranspose
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _hv
    simp only [gatedResidual]
    ring
  have hj' := hj
  rw [hexpand] at hj'
  have hsum : (∑ v, gatedResidual X θ t v * X v j) ≠ 0 :=
    (mul_ne_zero_iff.mp hj').1
  have hexv : ∃ v, gatedResidual X θ t v * X v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum (Finset.sum_eq_zero fun v _hv => h v)
  obtain ⟨v, hv⟩ := hexv
  have hX : X v j ≠ 0 := (mul_ne_zero_iff.mp hv).2
  have hterm : 0 < |X v j| * ((gatedDirection X θ t).ofLp j) ^ 2 := by
    rw [gatedDirection_ofLp, neg_sq]
    exact mul_pos (abs_pos.mpr hX) (sq_pos_of_ne_zero hj)
  have hunit : 0 < gatedUnitSecondOrderMass X (gatedDirection X θ t) v := by
    unfold gatedUnitSecondOrderMass
    apply Finset.sum_pos'
    · intro i _hi
      positivity
    · exact ⟨j, Finset.mem_univ j, hterm⟩
  unfold gatedResidualSecondOrderMass
  apply Finset.sum_pos'
  · intro w _hw
    exact mul_nonneg (abs_nonneg _)
      (by unfold gatedUnitSecondOrderMass; positivity)
  · refine ⟨v, Finset.mem_univ v, ?_⟩
    exact mul_pos (abs_pos.mpr (mul_ne_zero_iff.mp hv).1) hunit

/-- Positive alignment makes the full quadratic-majorizer curvature positive. -/
theorem gatedCurvature_pos_of_alignment_pos
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hA : 0 < gatedAlignment X θ t) : 0 < gatedCurvature X θ t := by
  have hM := gatedResidualSecondOrderMass_pos_of_alignment_pos X θ t hA
  have hrange : 0 ≤ (gatedStepRange X (gatedDirection X θ t)) ^ 2 := sq_nonneg _
  unfold gatedCurvature
  nlinarith

/-- Under positive alignment the safe step is exactly `A / (2 * C)`. -/
theorem gatedSafeStepSize_eq_div_of_alignment_pos
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hA : 0 < gatedAlignment X θ t) :
    gatedSafeStepSize X θ t =
      gatedAlignment X θ t / (2 * gatedCurvature X θ t) := by
  have hC := gatedCurvature_pos_of_alignment_pos X θ t hA
  simp only [gatedSafeStepSize, ne_of_gt hC, ↓reduceIte]

end Hagi.Model.GatedCEPositiveCurvature
