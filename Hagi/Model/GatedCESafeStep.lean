/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.GatedCEDescent
import Hagi.Model.TanhTaylor

/-!
# An explicit second-order safe step for gated categorical cross-entropy

The parameter line uses the actual negative residual-transpose direction of
`Hagi.Model.GatedCEDescent`.  Its logit displacement is decomposed into the
exact Jacobian action and a nonlinear `tanh` Taylor remainder.  A global
second-order bound for that remainder and the existing LSE range majorizer
give a conservative one-step upper bound for the actual cross-entropy.

For positive curvature the selected step is the stationary global minimizer
of this named quadratic majorizer.  At zero curvature the unit step is merely
a positive safe fallback certified by the positive-alignment theorem.  This
file makes no trajectory-convergence, hardware, global-CE-minimization, or
optimal-rate claim.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.GatedCESafeStep

open Hagi.Model.GatedCEGradient
open Hagi.Model.GatedCEDescent

variable {V : Type} [Fintype V]
variable {d : ℕ}

/-- Absolute one-unit logit mass of a supplied gated direction. -/
noncomputable def gatedUnitAbsLogit (X : Matrix V (Fin d) ℝ)
    (D : EuclideanSpace ℝ (Fin d)) (v : V) : ℝ :=
  ∑ j, |X v j * D.ofLp j|

/-- Twice the total one-unit absolute logit mass. -/
noncomputable def gatedStepRange (X : Matrix V (Fin d) ℝ)
    (D : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * ∑ v, gatedUnitAbsLogit X D v

/-- Actual nonlinear logit displacement on an affine parameter line. -/
noncomputable def gatedDisplacement (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) (eta : ℝ) : V → ℝ := fun v =>
  gatedForward X (θ + eta • D) v - gatedForward X θ v

/-- The range coefficient is nonnegative. -/
theorem gatedStepRange_nonneg (X : Matrix V (Fin d) ℝ)
    (D : EuclideanSpace ℝ (Fin d)) :
    0 ≤ gatedStepRange X D := by
  unfold gatedStepRange gatedUnitAbsLogit
  positivity

omit [Fintype V] in
/-- Global 1-Lipschitz `tanh` bounds each actual logit displacement. -/
theorem abs_gatedDisplacement_le (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) (eta : ℝ) (v : V) :
    |gatedDisplacement X θ D eta v| ≤ |eta| * gatedUnitAbsLogit X D v := by
  calc
    |gatedDisplacement X θ D eta v| =
        |∑ j, X v j * (Real.tanh ((θ + eta • D).ofLp j) -
          Real.tanh (θ.ofLp j))| := by
      simp only [gatedDisplacement, gatedForward, ← Finset.sum_sub_distrib]
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ ∑ j, |X v j * (Real.tanh ((θ + eta • D).ofLp j) -
          Real.tanh (θ.ofLp j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |X v j| * |Real.tanh ((θ + eta • D).ofLp j) -
          Real.tanh (θ.ofLp j)| := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_mul]
    _ ≤ ∑ j, |X v j| * |eta * D.ofLp j| := by
      apply Finset.sum_le_sum
      intro j _hj
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa using abs_tanh_sub_le ((θ + eta • D).ofLp j) (θ.ofLp j)
    _ = |eta| * gatedUnitAbsLogit X D v := by
      rw [gatedUnitAbsLogit, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_mul, abs_mul]
      ring

/-- For a nonnegative step, the actual displacement has the computed range. -/
theorem gated_displacement_range (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) {eta : ℝ}
    (heta : 0 ≤ eta) (u v : V) :
    gatedDisplacement X θ D eta u - gatedDisplacement X θ D eta v ≤
      eta * gatedStepRange X D := by
  have hpoint (w : V) : |gatedDisplacement X θ D eta w| ≤
      eta * gatedUnitAbsLogit X D w := by
    simpa [abs_of_nonneg heta] using abs_gatedDisplacement_le X θ D eta w
  have hsub (w : V) : gatedUnitAbsLogit X D w ≤
      ∑ z, gatedUnitAbsLogit X D z := by
    exact Finset.single_le_sum
      (fun z _hz => by unfold gatedUnitAbsLogit; positivity)
      (Finset.mem_univ w)
  have hsum : eta * gatedUnitAbsLogit X D u + eta * gatedUnitAbsLogit X D v ≤
      eta * ((∑ z, gatedUnitAbsLogit X D z) +
        ∑ z, gatedUnitAbsLogit X D z) := by
    simpa only [mul_add] using
      mul_le_mul_of_nonneg_left (add_le_add (hsub u) (hsub v)) heta
  have htri : gatedDisplacement X θ D eta u - gatedDisplacement X θ D eta v
      ≤ |gatedDisplacement X θ D eta u| + |gatedDisplacement X θ D eta v| :=
    le_trans (le_abs_self _) (abs_sub _ _)
  dsimp only [gatedStepRange]
  nlinarith [hpoint u, hpoint v]

/-- One-unit second-order logit mass of a supplied direction. -/
noncomputable def gatedUnitSecondOrderMass (X : Matrix V (Fin d) ℝ)
    (D : EuclideanSpace ℝ (Fin d)) (v : V) : ℝ :=
  ∑ j, |X v j| * (D.ofLp j) ^ 2

/-- Difference between actual logit displacement and its Jacobian action. -/
noncomputable def gatedLogitRemainder (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) (eta : ℝ) (v : V) : ℝ :=
  gatedDisplacement X θ D eta v - eta * gatedAction X θ D v

/-- The softmax-minus-one-hot residual at the current gated logits. -/
noncomputable def gatedResidual (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : V → ℝ := by
  classical
  exact fun v => Hagi.Prelude.softDef (gatedForward X θ) v -
    if v = t then 1 else 0

omit [Fintype V] in
/-- The decomposition into Jacobian displacement and nonlinear remainder is
an exact identity, not an approximation premise. -/
theorem gatedDisplacement_eq_linear_add_remainder
    (X : Matrix V (Fin d) ℝ) (θ D : EuclideanSpace ℝ (Fin d))
    (eta : ℝ) (v : V) :
    gatedDisplacement X θ D eta v = eta * gatedAction X θ D v +
      gatedLogitRemainder X θ D eta v := by
  unfold gatedLogitRemainder
  ring

omit [Fintype V] in
/-- Pointwise global second-order control of the actual nonlinear logit
remainder, using the proved scalar `tanh` Taylor estimate. -/
theorem abs_gatedLogitRemainder_le (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) (eta : ℝ) (v : V) :
    |gatedLogitRemainder X θ D eta v| ≤
      2 * eta ^ 2 * gatedUnitSecondOrderMass X D v := by
  have hrem (j : Fin d) :
      |Real.tanh ((θ + eta • D).ofLp j) - Real.tanh (θ.ofLp j) -
        (1 / (Real.cosh (θ.ofLp j)) ^ 2) * (eta * D.ofLp j)| ≤
        2 * eta ^ 2 * (D.ofLp j) ^ 2 := by
    have h := TanhTaylor.abs_tanh_taylor_sub_le
      (θ.ofLp j) ((θ + eta • D).ofLp j)
    rw [TanhTaylor.sechSq_eq_coshInvSq] at h
    have hcoord : (θ + eta • D).ofLp j - θ.ofLp j = eta * D.ofLp j := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hcoord] at h
    convert h using 1
    ring
  calc
    |gatedLogitRemainder X θ D eta v| =
        |∑ j, X v j * (Real.tanh ((θ + eta • D).ofLp j) -
          Real.tanh (θ.ofLp j) -
          (1 / (Real.cosh (θ.ofLp j)) ^ 2) * (eta * D.ofLp j))| := by
      apply congrArg abs
      simp only [gatedLogitRemainder, gatedDisplacement, gatedAction,
        gatedForward, Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ ∑ j, |X v j * (Real.tanh ((θ + eta • D).ofLp j) -
          Real.tanh (θ.ofLp j) -
          (1 / (Real.cosh (θ.ofLp j)) ^ 2) * (eta * D.ofLp j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |X v j| * |Real.tanh ((θ + eta • D).ofLp j) -
          Real.tanh (θ.ofLp j) -
          (1 / (Real.cosh (θ.ofLp j)) ^ 2) * (eta * D.ofLp j)| := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_mul]
    _ ≤ ∑ j, |X v j| * (2 * eta ^ 2 * (D.ofLp j) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (hrem j) (abs_nonneg _)
    _ = 2 * eta ^ 2 * gatedUnitSecondOrderMass X D v := by
      rw [gatedUnitSecondOrderMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- Residual-weighted second-order logit mass for a supplied direction. -/
noncomputable def gatedResidualSecondOrderMass (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  ∑ v, |gatedResidual X θ t v| * gatedUnitSecondOrderMass X D v

/-- Exact residual contraction of the nonlinear displacement. -/
theorem gated_residual_displacement_eq (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (eta : ℝ) :
    ∑ v, gatedResidual X θ t v *
        gatedDisplacement X θ (gatedDirection X θ t) eta v =
      -eta * gatedAlignment X θ t +
        ∑ v, gatedResidual X θ t v *
          gatedLogitRemainder X θ (gatedDirection X θ t) eta v := by
  classical
  have hfirst : ∑ v, gatedResidual X θ t v *
      gatedAction X θ (gatedDirection X θ t) v =
      -gatedAlignment X θ t := by
    simpa only [gatedResidual] using gated_first_order_eq X θ t
  have hterm (v : V) : gatedResidual X θ t v *
      gatedDisplacement X θ (gatedDirection X θ t) eta v =
      gatedResidual X θ t v *
        (eta * gatedAction X θ (gatedDirection X θ t) v) +
      gatedResidual X θ t v *
        gatedLogitRemainder X θ (gatedDirection X θ t) eta v := by
    rw [gatedDisplacement_eq_linear_add_remainder]
    ring
  calc
    ∑ v, gatedResidual X θ t v *
        gatedDisplacement X θ (gatedDirection X θ t) eta v =
      (∑ v, gatedResidual X θ t v *
        (eta * gatedAction X θ (gatedDirection X θ t) v)) +
      ∑ v, gatedResidual X θ t v *
        gatedLogitRemainder X θ (gatedDirection X θ t) eta v := by
          rw [Finset.sum_congr rfl (fun v _hv => hterm v),
            Finset.sum_add_distrib]
    _ = eta * (∑ v, gatedResidual X θ t v *
        gatedAction X θ (gatedDirection X θ t) v) +
      ∑ v, gatedResidual X θ t v *
        gatedLogitRemainder X θ (gatedDirection X θ t) eta v := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _hv
          ring
    _ = -eta * gatedAlignment X θ t +
      ∑ v, gatedResidual X θ t v *
        gatedLogitRemainder X θ (gatedDirection X θ t) eta v := by
          rw [hfirst]
          ring

/-- The residual-weighted Taylor error is at most `2 * eta^2 * M`. -/
theorem abs_gated_residualRemainder_le (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) (t : V) (eta : ℝ) :
    |∑ v, gatedResidual X θ t v * gatedLogitRemainder X θ D eta v| ≤
      2 * eta ^ 2 * gatedResidualSecondOrderMass X θ D t := by
  calc
    |∑ v, gatedResidual X θ t v * gatedLogitRemainder X θ D eta v| ≤
        ∑ v, |gatedResidual X θ t v * gatedLogitRemainder X θ D eta v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v, |gatedResidual X θ t v| * |gatedLogitRemainder X θ D eta v| := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [abs_mul]
    _ ≤ ∑ v, |gatedResidual X θ t v| *
        (2 * eta ^ 2 * gatedUnitSecondOrderMass X D v) := by
      apply Finset.sum_le_sum
      intro v _hv
      exact mul_le_mul_of_nonneg_left (abs_gatedLogitRemainder_le X θ D eta v)
        (abs_nonneg _)
    _ = 2 * eta ^ 2 * gatedResidualSecondOrderMass X θ D t := by
      rw [gatedResidualSecondOrderMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      ring

/-- The Taylor residual mass is nonnegative. -/
theorem gatedResidualSecondOrderMass_nonneg (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 ≤ gatedResidualSecondOrderMass X θ D t := by
  unfold gatedResidualSecondOrderMass gatedUnitSecondOrderMass
  positivity

/-- Generic actual-logit LSE assembly, including exact one-hot target
subtraction. -/
theorem ceOneHot_add_le_of_range [Nonempty V] [DecidableEq V]
    (z delta : V → ℝ) (M : ℝ) (t : V)
    (hM : ∀ u v, delta u - delta v ≤ M) :
    Hagi.ceOneHot t (fun v => z v + delta v) ≤ Hagi.ceOneHot t z +
      (∑ v, (Hagi.Prelude.softDef z v - if v = t then 1 else 0) * delta v) +
        M ^ 2 / 8 := by
  have hlse := Hagi.Energy.lse_shift_upper z (fun v => z v + delta v) M
    (fun u v => by
      convert hM u v using 1
      ring)
  have hone : (∑ v, (if v = t then (1 : ℝ) else 0) * delta v) = delta t := by
    classical
    simp
  simp only [Hagi.ceOneHot, Hagi.Core.ceOneHot, Hagi.Core.lse,
    sub_mul, Finset.sum_sub_distrib, hone]
  change Real.log (∑ v, Real.exp (z v + delta v)) ≤ _ at hlse
  simp only [Hagi.Energy.smax, add_sub_cancel_left] at hlse
  linarith

/-- Curvature `2 * M + range^2 / 8` of the gated quadratic majorizer. -/
noncomputable def gatedCurvature (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  2 * gatedResidualSecondOrderMass X θ (gatedDirection X θ t) t +
    (gatedStepRange X (gatedDirection X θ t)) ^ 2 / 8

/-- The conservative second-order upper bound for actual gated CE. -/
noncomputable def gatedMajorizer (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (eta : ℝ) : ℝ :=
  Hagi.ceOneHot t (gatedForward X θ) - eta * gatedAlignment X θ t +
    eta ^ 2 * gatedCurvature X θ t

/-- Actual LSE majorization on the gated nonlinear parameter line. -/
theorem gated_ceOneHot_lse_upper [Nonempty V] (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) {eta : ℝ} (heta : 0 ≤ eta) :
    Hagi.ceOneHot t (gatedForward X (gatedNextParameters X θ t eta)) ≤
      Hagi.ceOneHot t (gatedForward X θ) +
        (∑ v, gatedResidual X θ t v *
          gatedDisplacement X θ (gatedDirection X θ t) eta v) +
        (eta * gatedStepRange X (gatedDirection X θ t)) ^ 2 / 8 := by
  classical
  have h := ceOneHot_add_le_of_range
    (gatedForward X θ)
    (gatedDisplacement X θ (gatedDirection X θ t) eta)
    (eta * gatedStepRange X (gatedDirection X θ t)) t
    (gated_displacement_range X θ (gatedDirection X θ t) heta)
  have hnew : (fun v => gatedForward X θ v +
      gatedDisplacement X θ (gatedDirection X θ t) eta v) =
      gatedForward X (gatedNextParameters X θ t eta) := by
    funext v
    simp only [gatedDisplacement, gatedNextParameters]
    ring
  rw [hnew] at h
  simpa only [gatedResidual, gatedDisplacement, gatedNextParameters] using h

/-- The actual nonlinear gated CE is bounded by `old - eta*A + eta^2*C`. -/
theorem gated_ceOneHot_le_majorizer [Nonempty V] (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) {eta : ℝ} (heta : 0 ≤ eta) :
    Hagi.ceOneHot t (gatedForward X (gatedNextParameters X θ t eta)) ≤
      gatedMajorizer X θ t eta := by
  have hlse := gated_ceOneHot_lse_upper X θ t heta
  have hlinear := gated_residual_displacement_eq X θ t eta
  have hrem : (∑ v, gatedResidual X θ t v *
      gatedLogitRemainder X θ (gatedDirection X θ t) eta v) ≤
      2 * eta ^ 2 * gatedResidualSecondOrderMass X θ (gatedDirection X θ t) t :=
    le_trans (le_abs_self _) (abs_gated_residualRemainder_le X θ
      (gatedDirection X θ t) t eta)
  rw [hlinear] at hlse
  calc
    Hagi.ceOneHot t (gatedForward X (gatedNextParameters X θ t eta)) ≤
        Hagi.ceOneHot t (gatedForward X θ) - eta * gatedAlignment X θ t +
          (∑ v, gatedResidual X θ t v *
            gatedLogitRemainder X θ (gatedDirection X θ t) eta v) +
          (eta * gatedStepRange X (gatedDirection X θ t)) ^ 2 / 8 := by
      convert hlse using 1 <;> ring
    _ ≤ Hagi.ceOneHot t (gatedForward X θ) - eta * gatedAlignment X θ t +
          2 * eta ^ 2 * gatedResidualSecondOrderMass X θ
            (gatedDirection X θ t) t +
          (eta * gatedStepRange X (gatedDirection X θ t)) ^ 2 / 8 := by
      linarith
    _ = gatedMajorizer X θ t eta := by
      unfold gatedMajorizer gatedCurvature
      ring

/-- The full curvature is nonnegative; in particular it need not be positive. -/
theorem gatedCurvature_nonneg (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 ≤ gatedCurvature X θ t := by
  have hM := gatedResidualSecondOrderMass_nonneg X θ (gatedDirection X θ t) t
  have hsq : 0 ≤ (gatedStepRange X (gatedDirection X θ t)) ^ 2 := sq_nonneg _
  unfold gatedCurvature
  linarith

/-- Explicit safe step: unit fallback at zero curvature, otherwise the
positive-curvature quadratic stationary point. -/
noncomputable def gatedSafeStepSize (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  if gatedCurvature X θ t = 0 then 1
  else gatedAlignment X θ t / (2 * gatedCurvature X θ t)

/-- Exact certified drop of the quadratic upper bound at the safe step. -/
noncomputable def gatedSafeDrop (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  if gatedCurvature X θ t = 0 then gatedAlignment X θ t
  else (gatedAlignment X θ t) ^ 2 / (4 * gatedCurvature X θ t)

@[simp] theorem gatedSafeStepSize_of_curvature_eq_zero
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hC : gatedCurvature X θ t = 0) : gatedSafeStepSize X θ t = 1 := by
  simp [gatedSafeStepSize, hC]

@[simp] theorem gatedSafeDrop_of_curvature_eq_zero
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hC : gatedCurvature X θ t = 0) :
    gatedSafeDrop X θ t = gatedAlignment X θ t := by
  simp [gatedSafeDrop, hC]

/-- The computed safe step is nonnegative. -/
theorem gatedSafeStepSize_nonneg (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 ≤ gatedSafeStepSize X θ t := by
  have hA := gatedAlignment_nonneg X θ t
  have hC := gatedCurvature_nonneg X θ t
  by_cases hzero : gatedCurvature X θ t = 0
  · simp [gatedSafeStepSize, hzero]
  · have hpos : 0 < gatedCurvature X θ t := lt_of_le_of_ne hC (Ne.symm hzero)
    simp only [gatedSafeStepSize, hzero, ↓reduceIte]
    exact div_nonneg hA (by positivity)

/-- Positive alignment makes both branches of the step rule strictly positive. -/
theorem gatedSafeStepSize_pos_of_alignment_pos (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hA : 0 < gatedAlignment X θ t) : 0 < gatedSafeStepSize X θ t := by
  have hC := gatedCurvature_nonneg X θ t
  by_cases hzero : gatedCurvature X θ t = 0
  · simp [gatedSafeStepSize, hzero]
  · have hpos : 0 < gatedCurvature X θ t := lt_of_le_of_ne hC (Ne.symm hzero)
    simp only [gatedSafeStepSize, hzero, ↓reduceIte]
    exact div_pos hA (by positivity)

/-- The certified drop is nonnegative. -/
theorem gatedSafeDrop_nonneg (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : 0 ≤ gatedSafeDrop X θ t := by
  have hA := gatedAlignment_nonneg X θ t
  have hC := gatedCurvature_nonneg X θ t
  by_cases hzero : gatedCurvature X θ t = 0
  · simpa [gatedSafeDrop, hzero] using hA
  · have hpos : 0 < gatedCurvature X θ t := lt_of_le_of_ne hC (Ne.symm hzero)
    simp only [gatedSafeDrop, hzero, ↓reduceIte]
    exact div_nonneg (sq_nonneg _) (by positivity)

/-- Positive alignment gives a strictly positive certified drop. -/
theorem gatedSafeDrop_pos_of_alignment_pos (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hA : 0 < gatedAlignment X θ t) : 0 < gatedSafeDrop X θ t := by
  have hC := gatedCurvature_nonneg X θ t
  by_cases hzero : gatedCurvature X θ t = 0
  · simpa [gatedSafeDrop, hzero] using hA
  · have hpos : 0 < gatedCurvature X θ t := lt_of_le_of_ne hC (Ne.symm hzero)
    simp only [gatedSafeDrop, hzero, ↓reduceIte]
    exact div_pos (sq_pos_of_pos hA) (by positivity)

/-- Exact safe-step algebra.  At zero curvature this uses only the unit
fallback; it is not a minimization assertion for the linear majorizer. -/
theorem gated_safe_quadratic_identity (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    -gatedSafeStepSize X θ t * gatedAlignment X θ t +
        (gatedSafeStepSize X θ t) ^ 2 * gatedCurvature X θ t =
      -gatedSafeDrop X θ t := by
  by_cases hzero : gatedCurvature X θ t = 0
  · simp [gatedSafeStepSize, gatedSafeDrop, hzero]
  · simp only [gatedSafeStepSize, gatedSafeDrop, hzero, ↓reduceIte]
    field_simp
    ring

/-- At positive curvature the safe step globally minimizes this named
quadratic majorizer.  The zero-curvature unit fallback is outside this claim. -/
theorem gatedMajorizer_safeStep_le (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hC : 0 < gatedCurvature X θ t) (eta : ℝ) :
    gatedMajorizer X θ t (gatedSafeStepSize X θ t) ≤
      gatedMajorizer X θ t eta := by
  have hdiff : gatedMajorizer X θ t eta -
      gatedMajorizer X θ t (gatedSafeStepSize X θ t) =
      gatedCurvature X θ t * (eta - gatedSafeStepSize X θ t) ^ 2 := by
    simp only [gatedMajorizer, gatedSafeStepSize, ne_of_gt hC, ↓reduceIte]
    field_simp
    ring
  have hsquare : 0 ≤ gatedCurvature X θ t *
      (eta - gatedSafeStepSize X θ t) ^ 2 := by positivity
  linarith

/-- The safe step evaluates the certified majorizer to `old - drop`. -/
theorem gatedMajorizer_safeStep_eq (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    gatedMajorizer X θ t (gatedSafeStepSize X θ t) =
      Hagi.ceOneHot t (gatedForward X θ) - gatedSafeDrop X θ t := by
  have hid := gated_safe_quadratic_identity X θ t
  unfold gatedMajorizer
  linarith

/-- Actual CE after the explicit step is at most `old - drop`. -/
theorem gated_ceOneHot_safeStep_le_drop [Nonempty V]
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    Hagi.ceOneHot t (gatedForward X
      (gatedNextParameters X θ t (gatedSafeStepSize X θ t))) ≤
      Hagi.ceOneHot t (gatedForward X θ) - gatedSafeDrop X θ t := by
  rw [← gatedMajorizer_safeStep_eq X θ t]
  exact gated_ceOneHot_le_majorizer X θ t (gatedSafeStepSize_nonneg X θ t)

/-- Positive alignment gives strict descent of actual gated categorical CE
at the explicit computed step. -/
theorem gated_ceOneHot_safeStep_lt [Nonempty V]
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hA : 0 < gatedAlignment X θ t) :
    Hagi.ceOneHot t (gatedForward X
      (gatedNextParameters X θ t (gatedSafeStepSize X θ t))) <
        Hagi.ceOneHot t (gatedForward X θ) := by
  have hbound := gated_ceOneHot_safeStep_le_drop X θ t
  have hdrop := gatedSafeDrop_pos_of_alignment_pos X θ t hA
  linarith

/-- Binary identity features at zero parameters have nonzero alignment. -/
theorem identityTwoClass_gatedAlignment_test :
    gatedAlignment (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 2 := by
  norm_num [gatedAlignment, gatedResidualTranspose, gatedForward,
    Hagi.Prelude.softDef, Fin.sum_univ_two]

/-- The same binary example has residual mass `1/4`, range `2`, curvature `1`. -/
theorem identityTwoClass_gatedCurvature_test :
    gatedCurvature (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by
  norm_num [gatedCurvature, gatedResidualSecondOrderMass, gatedStepRange,
    gatedUnitAbsLogit, gatedUnitSecondOrderMass, gatedResidual, gatedDirection,
    gatedResidualTranspose, gatedForward, Hagi.Prelude.softDef, Fin.sum_univ_two]

/-- Consequently the binary safe step is positive and equals `1/4`. -/
theorem identityTwoClass_gatedSafeStepSize_test :
    gatedSafeStepSize (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 4 := by
  rw [gatedSafeStepSize, identityTwoClass_gatedCurvature_test,
    identityTwoClass_gatedAlignment_test]
  norm_num

/-- Its exact majorizer drop is `1/16`, so the example is nondegenerate. -/
theorem identityTwoClass_gatedSafeDrop_test :
    gatedSafeDrop (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 16 := by
  rw [gatedSafeDrop, identityTwoClass_gatedCurvature_test,
    identityTwoClass_gatedAlignment_test]
  norm_num

/-- The explicit binary arithmetic example descends in actual gated CE. -/
theorem identityTwoClass_gated_ceOneHot_safeStep_lt_test :
    Hagi.ceOneHot (0 : Fin 2) (gatedForward
      (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (gatedNextParameters (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
        (gatedSafeStepSize (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0))) <
      Hagi.ceOneHot (0 : Fin 2) (gatedForward
        (1 : Matrix (Fin 2) (Fin 2) ℝ) 0) := by
  apply gated_ceOneHot_safeStep_lt
  rw [identityTwoClass_gatedAlignment_test]
  norm_num

end Hagi.Model.GatedCESafeStep
