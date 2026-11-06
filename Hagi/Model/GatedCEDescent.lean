/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.GatedCEGradient

/-!
# Local CE descent for the trainable gated tanh controls

The direction is the negative transpose of the actual softmax residual through
the current sech-squared Jacobian of `gatedForward`.  The line derivative is
obtained by composing the categorical CE derivative with the parameter line;
finite sum exchange identifies it as minus the squared residual transpose.

Native little-o differentiation (`HasDerivAt.isLittleO` and
`Asymptotics.isLittleO_iff` in pinned Mathlib) then gives a strictly positive
step with strictly smaller actual CE.  This is local existence only: it neither
computes an explicit step nor asserts descent for every step or convergence of
an iteration.  The analytic composition APIs are documented at
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Deriv/Basic.html .
-/

set_option relaxedAutoImplicit false

open Filter

namespace Hagi.Model.GatedCEDescent

open Hagi.Model.GatedCEGradient

variable {V : Type} [Fintype V]
variable {d : ℕ}

/-- Transpose of the actual residual through the current sech-squared gated
Jacobian. -/
noncomputable def gatedResidualTranspose (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : Fin d → ℝ := by
  classical
  exact fun j => ∑ v,
    (Hagi.Prelude.softDef (gatedForward X θ) v - if v = t then 1 else 0) *
      (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2))

/-- Negative residual transpose on the Euclidean parameter carrier. -/
noncomputable def gatedDirection (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => -gatedResidualTranspose X θ t j)

/-- Squared Euclidean alignment of the residual-transpose direction. -/
noncomputable def gatedAlignment (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : ℝ :=
  ∑ j, gatedResidualTranspose X θ t j ^ 2

/-- Actual gated controls after a scalar step in the chosen direction. -/
noncomputable def gatedNextParameters (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (eta : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  θ + eta • gatedDirection X θ t

/-- Actual categorical CE along the parameter line. -/
noncomputable def gatedLineObjective (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (eta : ℝ) : ℝ :=
  Hagi.ceOneHot t (gatedForward X (gatedNextParameters X θ t eta))

@[simp] theorem gatedDirection_ofLp (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (j : Fin d) :
    (gatedDirection X θ t).ofLp j = -gatedResidualTranspose X θ t j := rfl

/-- The squared residual-transpose alignment is nonnegative. -/
theorem gatedAlignment_nonneg (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 ≤ gatedAlignment X θ t := by
  unfold gatedAlignment
  positivity

/-- Exact first-order identity for the negative residual-transpose direction.
Only expansion of `gatedAction` and finite sum exchange are used. -/
theorem gated_first_order_eq [DecidableEq V] (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    ∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
      if v = t then 1 else 0) * gatedAction X θ (gatedDirection X θ t) v =
      -gatedAlignment X θ t := by
  let R : Fin d → ℝ := gatedResidualTranspose X θ t
  calc
    ∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
        if v = t then 1 else 0) * gatedAction X θ (gatedDirection X θ t) v =
        ∑ v, ∑ j, (Hagi.Prelude.softDef (gatedForward X θ) v -
          if v = t then 1 else 0) *
          (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2 * -R j)) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [gatedAction, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [gatedDirection_ofLp]
    _ = ∑ j, ∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
          if v = t then 1 else 0) *
          (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2 * -R j)) :=
      Finset.sum_comm
    _ = ∑ j, -(R j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      calc
        ∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
            if v = t then 1 else 0) *
            (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2 * -R j)) =
            (∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
              if v = t then 1 else 0) *
              (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2))) * (-R j) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro v _hv
          ring
        _ = R j * (-R j) := by
          simp only [R, gatedResidualTranspose]
          congr 1
          apply Finset.sum_congr rfl
          intro x _hx
          have hdec : (‹DecidableEq V› x t) =
              Classical.propDecidable (x = t) := Subsingleton.elim _ _
          rw [hdec]
        _ = -(R j) ^ 2 := by ring
    _ = -gatedAlignment X θ t := by
      simp only [Finset.sum_neg_distrib, gatedAlignment, R]

/-- Derivative of the actual CE line at zero, by composition of differentiable
CE with the affine parameter line and the Cycle 97 gated derivative. -/
theorem hasDerivAt_gatedLineObjective [Nonempty V] [DecidableEq V]
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    HasDerivAt
      (fun eta : ℝ => Hagi.ceOneHot t (gatedForward X
        (θ + eta • gatedDirection X θ t))) (-gatedAlignment X θ t) 0 := by
  let D : EuclideanSpace ℝ (Fin d) := gatedDirection X θ t
  have hline : HasDerivAt (fun eta : ℝ => θ + eta • D) D 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const D).const_add θ
  have hforward : DifferentiableAt ℝ
      (fun w => Hagi.ceOneHot t (gatedForward X w)) θ :=
    CEGradient.differentiableAt_ceOneHot_comp (gatedForward X) θ t
      (differentiable_gatedForward X θ)
  have hforward' : DifferentiableAt ℝ
      (fun w => Hagi.ceOneHot t (gatedForward X w)) (θ + (0 : ℝ) • D) := by
    simpa using hforward
  have hcomp : HasDerivAt
      (fun eta : ℝ => Hagi.ceOneHot t (gatedForward X (θ + eta • D)))
      (fderiv ℝ (fun w => Hagi.ceOneHot t (gatedForward X w)) θ D) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero] using
      hforward'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  rw [GatedCEGradient.fderiv_ceOneHot_gatedForward] at hcomp
  have hfirst := gated_first_order_eq X θ t
  rw [hfirst] at hcomp
  simpa only [gatedLineObjective, gatedNextParameters, D] using hcomp

/-- A negative scalar derivative at zero yields an actually positive point
with a strictly smaller value. -/
theorem exists_pos_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (ha : a < 0) :
    ∃ eta > 0, f eta < f 0 := by
  have hc : 0 < -a / 2 := by linarith
  have hbound : ∀ᶠ eta in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ‖f eta - f 0 - (eta - 0) • a‖ ≤ (-a / 2) * ‖eta - 0‖ :=
    (Asymptotics.isLittleO_iff.1 hf.isLittleO hc).filter_mono
      nhdsWithin_le_nhds
  have hevent : ∀ᶠ eta in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < eta ∧ f eta < f 0 := by
    filter_upwards [hbound, self_mem_nhdsWithin] with eta hrem heta
    have heta' : 0 < eta := heta
    refine ⟨heta', ?_⟩
    simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_of_pos heta'] at hrem
    have hupper : f eta - f 0 - eta * a ≤ (-a / 2) * eta :=
      le_trans (le_abs_self _) hrem
    have hnegprod : eta * a < 0 := mul_neg_of_pos_of_neg heta' ha
    linarith
  exact hevent.exists

/-- Positive actual residual-transpose alignment gives a strictly positive
step to strictly smaller CE of the trainable gated forward map. -/
theorem exists_gated_ceOneHot_descent [Nonempty V] [DecidableEq V]
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hA : 0 < gatedAlignment X θ t) :
    ∃ eta : ℝ, eta > 0 ∧ Hagi.ceOneHot t (gatedForward X
      (θ + eta • gatedDirection X θ t)) <
      Hagi.ceOneHot t (gatedForward X θ) := by
  obtain ⟨eta, heta, hlt⟩ := exists_pos_lt_of_hasDerivAt_neg
    (hasDerivAt_gatedLineObjective X θ t) (neg_neg_of_pos hA)
  refine ⟨eta, heta, ?_⟩
  simpa only [zero_smul, add_zero] using hlt

end Hagi.Model.GatedCEDescent
