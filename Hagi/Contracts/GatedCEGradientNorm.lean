/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.GatedCETrajectory

set_option relaxedAutoImplicit false

/-!
# Gradient-norm identification for the gated trajectory

This file identifies the abstract gradient of the gated one-target
cross-entropy with the residual transpose of `GatedCEDescent` and
restates the feature-only trajectory budget of
`GatedCEUniformAlignmentBudget` in gradient-norm form.

Main results:

* `gatedGrad` is the gradient vector: `-gatedDirection`, i.e. the
  residual transpose `gatedResidualTranspose` on the Euclidean
  parameter carrier (`gatedGrad_ofLp`).
* `fderiv_gatedCE_apply` and `fderiv_gatedCE_apply_inner` express the
  Fréchet derivative as the action resp. real inner product against
  `gatedGrad`.
* `norm_gatedGrad_sq`: `‖gatedGrad‖² = gatedAlignment` — the
  alignment of the gated safe-step theory IS the squared gradient
  norm, definitionally (no assumptions beyond `Fintype`).
* `gated_grad_sum_fourth_le_uniform`: every finite sum of FOURTH
  powers of gradient norms along the canonical executed gated
  trajectory is at most `4 * gatedCurvatureUniformBound X * L₀`.

Honesty note: the executed safe step `η = A / (2C)` has exact drop
`A² / (4C)`, so the budget controls `∑ ‖∇L‖⁴`, not `∑ ‖∇L‖²`; the
squared-norm form would additionally need a feature-only bound
`gatedCurvature ≤ κ(X) * gatedAlignment`, which is not proved here.
No empirical (`h_emp`) premise appears anywhere; the only hypotheses
are `[Fintype V]`, `[Nonempty V]` / `[DecidableEq V]` where stated,
a fixed one-hot target `t`, and unconstrained reals.
-/

open Hagi.State Hagi.Model
open scoped InnerProductSpace
open Hagi.Model.GatedCEGradient Hagi.Model.GatedCEDescent
open Hagi.Model.GatedCEUniformCurvature
open Hagi.Contracts.CEStep Hagi.Contracts.GatedCEStep
open Hagi.Contracts.GatedCETrajectory Hagi.Contracts.GatedCEAlignmentBudget
open Hagi.Contracts.GatedCEUniformAlignmentBudget

namespace Hagi.Contracts.GatedCEGradientNorm

variable {V : Type} [Fintype V]
variable {d : ℕ}

/-- The gradient vector of the gated one-target CE: the residual transpose
on the Euclidean parameter carrier. -/
noncomputable def gatedGrad (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) : EuclideanSpace ℝ (Fin d) :=
  -gatedDirection X θ t

theorem gatedGrad_ofLp (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) (j : Fin d) :
    (gatedGrad X θ t).ofLp j = gatedResidualTranspose X θ t j := by
  show -(gatedDirection X θ t).ofLp j = gatedResidualTranspose X θ t j
  rw [gatedDirection_ofLp]
  ring

theorem fderiv_gatedCE_apply [Nonempty V] [DecidableEq V]
    (X : Matrix V (Fin d) ℝ) (θ D : EuclideanSpace ℝ (Fin d)) (t : V) :
    fderiv ℝ (fun w => Hagi.ceOneHot t (gatedForward X w)) θ D =
      ∑ j, (gatedGrad X θ t).ofLp j * D.ofLp j := by
  have hopen :
    fderiv ℝ (fun w => Hagi.ceOneHot t (gatedForward X w)) θ D =
      ∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
        if v = t then 1 else 0) * gatedAction X θ D v :=
      GatedCEGradient.fderiv_ceOneHot_gatedForward X θ D t
  rw [hopen]
  simp only [gatedAction, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _hj => ?_
  have hRT : gatedResidualTranspose X θ t j =
      ∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
        if v = t then 1 else 0) *
        (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2)) := by
    simp only [gatedResidualTranspose]
    apply Finset.sum_congr rfl
    intro x _hx
    have hdec : (‹DecidableEq V› x t) =
        Classical.propDecidable (x = t) := Subsingleton.elim _ _
    rw [hdec]
  have hpull : ∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
      if v = t then 1 else 0) *
      (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2 * D.ofLp j)) =
      (∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
        if v = t then 1 else 0) *
        (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2))) * D.ofLp j := by
    calc ∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
          if v = t then 1 else 0) *
          (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2 * D.ofLp j)) =
        ∑ v, ((Hagi.Prelude.softDef (gatedForward X θ) v -
          if v = t then 1 else 0) *
          (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2))) * D.ofLp j :=
          Finset.sum_congr rfl fun v _hv => by ring
      _ = (∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
          if v = t then 1 else 0) *
          (X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2))) * D.ofLp j :=
          (Finset.sum_mul _ _ _).symm
  rw [hpull, gatedGrad_ofLp, hRT]

theorem fderiv_gatedCE_apply_inner [Nonempty V] [DecidableEq V]
    (X : Matrix V (Fin d) ℝ) (θ D : EuclideanSpace ℝ (Fin d)) (t : V) :
    fderiv ℝ (fun w => Hagi.ceOneHot t (gatedForward X w)) θ D =
      ⟪gatedGrad X θ t, D⟫_ℝ := by
  rw [fderiv_gatedCE_apply X θ D t, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _hj => by
    rw [RCLike.inner_apply, conj_trivial]
    ring

theorem norm_gatedGrad_sq (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    ‖gatedGrad X θ t‖ ^ 2 = gatedAlignment X θ t := by
  have hn : 0 ≤ ∑ i, ‖(gatedGrad X θ t).ofLp i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt hn]
  unfold gatedGrad gatedAlignment
  refine Finset.sum_congr rfl fun j _hj => ?_
  simp [Real.norm_eq_abs, sq_abs]

variable {n a r c k : ℕ}

/-- End-to-end gated trajectory gradient budget with the feature-only
constant: every finite sum of FOURTH powers of gradient norms along the
canonical executed trajectory is at most
`4 * gatedCurvatureUniformBound X * gatedCEObjective X t S`.
This is the exact gradient-norm restatement of
`fixedGatedAlignment_sum_sq_le_uniform`. -/
theorem gated_grad_sum_fourth_le_uniform [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ s ∈ Finset.range T, ‖gatedGrad X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t‖ ^ 4 ≤
      4 * gatedCurvatureUniformBound X * gatedCEObjective X t S := by
  have hterm : ∀ s : ℕ,
      ‖gatedGrad X
        (coreParameters (fixedGatedState X t S opCost opRisk write s)) t‖ ^ 4 =
      (fixedGatedAlignment X t S opCost opRisk write s) ^ 2 := by
    intro s
    unfold fixedGatedAlignment
    rw [← norm_gatedGrad_sq]
    ring
  rw [Finset.sum_congr rfl (fun s _hs => hterm s)]
  exact fixedGatedAlignment_sum_sq_le_uniform X t S opCost opRisk write T

end Hagi.Contracts.GatedCEGradientNorm
