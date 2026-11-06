/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.GatedCESafeStep

set_option linter.style.header false

/-!
# A feature-only uniform bound for gated curvature

The softmax residual has absolute value at most one.  Together with the local
`TanhTaylor` bounds on `1 / cosh(x)^2`, this controls the residual-transpose
direction by column-wise absolute feature sums.  Finite-sum comparison then
bounds the range and residual second-order mass in the safe-step majorizer.
The resulting positive curvature bound depends only on the feature matrix.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.GatedCEUniformCurvature

open Hagi.Model.GatedCEGradient
open Hagi.Model.GatedCEDescent
open Hagi.Model.GatedCESafeStep

variable {V : Type} [Fintype V]
variable {d : ℕ}

/-- Total absolute feature mass in one column. -/
noncomputable def gatedColumnAbsSum (X : Matrix V (Fin d) ℝ) (j : Fin d) : ℝ :=
  ∑ v, |X v j|

/-- First-order feature mass, abbreviated as `U` in the curvature bound. -/
noncomputable def gatedFirstOrderFeatureMass (X : Matrix V (Fin d) ℝ) : ℝ :=
  ∑ v, ∑ j, |X v j| * gatedColumnAbsSum X j

/-- Second-order feature mass, abbreviated as `Q` in the curvature bound. -/
noncomputable def gatedSecondOrderFeatureMass (X : Matrix V (Fin d) ℝ) : ℝ :=
  ∑ v, ∑ j, |X v j| * (gatedColumnAbsSum X j) ^ 2

/-- A deliberately loose positive feature-only bound on every curvature. -/
noncomputable def gatedCurvatureUniformBound (X : Matrix V (Fin d) ℝ) : ℝ :=
  1 + 2 * gatedSecondOrderFeatureMass X +
    (2 * gatedFirstOrderFeatureMass X) ^ 2 / 8

/-- Every softmax coordinate is at most one. -/
theorem softDef_le_one [Nonempty V] (z : V → ℝ) (v : V) :
    Hagi.Prelude.softDef z v ≤ 1 := by
  calc
    Hagi.Prelude.softDef z v ≤ ∑ w, Hagi.Prelude.softDef z w :=
      Finset.single_le_sum
        (fun w _hw => (Hagi.Prelude.softDef_pos z w).le) (Finset.mem_univ v)
    _ = 1 := Hagi.Prelude.softDef_sum_one z

/-- The actual softmax-minus-one-hot residual has absolute value at most one. -/
theorem abs_gatedResidual_le_one (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t v : V) :
    |gatedResidual X θ t v| ≤ 1 := by
  classical
  let : Nonempty V := ⟨t⟩
  have hpos := Hagi.Prelude.softDef_pos (gatedForward X θ) v
  have hle := softDef_le_one (gatedForward X θ) v
  by_cases hvt : v = t
  · subst v
    simp only [gatedResidual, ↓reduceIte]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [gatedResidual, hvt, ↓reduceIte, sub_zero,
      abs_of_nonneg hpos.le]
    exact hle

/-- The squared reciprocal hyperbolic cosine is strictly positive. -/
theorem coshInvSq_pos (x : ℝ) : 0 < 1 / (Real.cosh x) ^ 2 := by
  positivity

/-- The squared reciprocal hyperbolic cosine is at most one. -/
theorem coshInvSq_le_one (x : ℝ) : 1 / (Real.cosh x) ^ 2 ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < (Real.cosh x) ^ 2)).2
  nlinarith [Real.cosh_sq_sub_sinh_sq x, sq_nonneg (Real.sinh x)]

/-- Column feature mass is nonnegative. -/
theorem gatedColumnAbsSum_nonneg (X : Matrix V (Fin d) ℝ) (j : Fin d) :
    0 ≤ gatedColumnAbsSum X j := by
  unfold gatedColumnAbsSum
  positivity

/-- First-order feature mass is nonnegative. -/
theorem gatedFirstOrderFeatureMass_nonneg (X : Matrix V (Fin d) ℝ) :
    0 ≤ gatedFirstOrderFeatureMass X := by
  unfold gatedFirstOrderFeatureMass
  exact Finset.sum_nonneg fun v _hv => Finset.sum_nonneg fun j _hj =>
    mul_nonneg (abs_nonneg _) (gatedColumnAbsSum_nonneg X j)

/-- Second-order feature mass is nonnegative. -/
theorem gatedSecondOrderFeatureMass_nonneg (X : Matrix V (Fin d) ℝ) :
    0 ≤ gatedSecondOrderFeatureMass X := by
  unfold gatedSecondOrderFeatureMass
  positivity

/-- The residual transpose is controlled column-wise by absolute features. -/
theorem abs_gatedResidualTranspose_le (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (j : Fin d) :
    |gatedResidualTranspose X θ t j| ≤ gatedColumnAbsSum X j := by
  classical
  calc
    |gatedResidualTranspose X θ t j| ≤
        ∑ v, |(Hagi.Prelude.softDef (gatedForward X θ) v -
          if v = t then 1 else 0) *
          (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2))| := by
      unfold gatedResidualTranspose
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v, |gatedResidual X θ t v| * |X v j| *
        |1 / (Real.cosh (θ.ofLp j)) ^ 2| := by
      apply Finset.sum_congr rfl
      intro v _hv
      simp only [gatedResidual, abs_mul, mul_assoc]
    _ ≤ ∑ v, |X v j| := by
      apply Finset.sum_le_sum
      intro v _hv
      have hr := abs_gatedResidual_le_one X θ t v
      have hs : |1 / (Real.cosh (θ.ofLp j)) ^ 2| ≤ 1 := by
        rw [abs_of_nonneg (coshInvSq_pos _).le]
        exact coshInvSq_le_one _
      calc
        |gatedResidual X θ t v| * |X v j| *
            |1 / (Real.cosh (θ.ofLp j)) ^ 2| ≤ 1 * |X v j| * 1 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right hr (abs_nonneg _)) hs
            (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
        _ = |X v j| := by ring
    _ = gatedColumnAbsSum X j := rfl

/-- Every coordinate of the negative residual transpose has the same bound. -/
theorem abs_gatedDirection_ofLp_le (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (j : Fin d) :
    |(gatedDirection X θ t).ofLp j| ≤ gatedColumnAbsSum X j := by
  rw [gatedDirection_ofLp, abs_neg]
  exact abs_gatedResidualTranspose_le X θ t j

/-- One-unit absolute logit mass is bounded by first-order row features. -/
theorem gatedUnitAbsLogit_direction_le (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (v : V) :
    gatedUnitAbsLogit X (gatedDirection X θ t) v ≤
      ∑ j, |X v j| * gatedColumnAbsSum X j := by
  unfold gatedUnitAbsLogit
  calc
    ∑ j, |X v j * (gatedDirection X θ t).ofLp j| =
        ∑ j, |X v j| * |(gatedDirection X θ t).ofLp j| := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_mul]
    _ ≤ ∑ j, |X v j| * gatedColumnAbsSum X j := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left
        (abs_gatedDirection_ofLp_le X θ t j) (abs_nonneg _)

/-- The safe-step range is at most twice the first-order feature mass. -/
theorem gatedStepRange_direction_le (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    gatedStepRange X (gatedDirection X θ t) ≤
      2 * gatedFirstOrderFeatureMass X := by
  unfold gatedStepRange
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    ∑ v, gatedUnitAbsLogit X (gatedDirection X θ t) v ≤
        ∑ v, ∑ j, |X v j| * gatedColumnAbsSum X j := by
      apply Finset.sum_le_sum
      intro v _hv
      exact gatedUnitAbsLogit_direction_le X θ t v
    _ = gatedFirstOrderFeatureMass X := rfl

/-- One-unit second-order logit mass is bounded by second-order row features. -/
theorem gatedUnitSecondOrderMass_direction_le (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (v : V) :
    gatedUnitSecondOrderMass X (gatedDirection X θ t) v ≤
      ∑ j, |X v j| * (gatedColumnAbsSum X j) ^ 2 := by
  unfold gatedUnitSecondOrderMass
  apply Finset.sum_le_sum
  intro j _hj
  have hj := abs_gatedDirection_ofLp_le X θ t j
  have hsquare : ((gatedDirection X θ t).ofLp j) ^ 2 ≤
      (gatedColumnAbsSum X j) ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg ((gatedDirection X θ t).ofLp j),
      gatedColumnAbsSum_nonneg X j]
  exact mul_le_mul_of_nonneg_left hsquare (abs_nonneg _)

/-- Residual weighting does not increase the second-order feature bound. -/
theorem gatedResidualSecondOrderMass_direction_le (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    gatedResidualSecondOrderMass X θ (gatedDirection X θ t) t ≤
      gatedSecondOrderFeatureMass X := by
  unfold gatedResidualSecondOrderMass
  calc
    ∑ v, |gatedResidual X θ t v| *
        gatedUnitSecondOrderMass X (gatedDirection X θ t) v ≤
      ∑ v, gatedUnitSecondOrderMass X (gatedDirection X θ t) v := by
        apply Finset.sum_le_sum
        intro v _hv
        have hunit : 0 ≤ gatedUnitSecondOrderMass X (gatedDirection X θ t) v := by
          unfold gatedUnitSecondOrderMass
          positivity
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (abs_gatedResidual_le_one X θ t v) hunit
    _ ≤ ∑ v, ∑ j, |X v j| * (gatedColumnAbsSum X j) ^ 2 := by
      apply Finset.sum_le_sum
      intro v _hv
      exact gatedUnitSecondOrderMass_direction_le X θ t v
    _ = gatedSecondOrderFeatureMass X := rfl

/-- Every current gated curvature is bounded by the feature-only constant. -/
theorem gatedCurvature_le_uniformBound (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    gatedCurvature X θ t ≤ gatedCurvatureUniformBound X := by
  have hM := gatedResidualSecondOrderMass_direction_le X θ t
  have hR := gatedStepRange_direction_le X θ t
  have hR0 := gatedStepRange_nonneg X (gatedDirection X θ t)
  have hsquare : (gatedStepRange X (gatedDirection X θ t)) ^ 2 ≤
      (2 * gatedFirstOrderFeatureMass X) ^ 2 := by
    nlinarith
  unfold gatedCurvature gatedCurvatureUniformBound
  nlinarith

/-- The feature-only curvature bound is strictly positive, including at zero
features and in dimension zero. -/
theorem gatedCurvatureUniformBound_pos (X : Matrix V (Fin d) ℝ) :
    0 < gatedCurvatureUniformBound X := by
  have hQ := gatedSecondOrderFeatureMass_nonneg X
  unfold gatedCurvatureUniformBound
  nlinarith [sq_nonneg (2 * gatedFirstOrderFeatureMass X)]

end Hagi.Model.GatedCEUniformCurvature
