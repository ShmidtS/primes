/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEGradient

/-!
# A trainable nonlinear gated categorical head and its actual derivative

The forward computation is `X v j * tanh(θ.ofLp j)`.  It uses supplied
readout features and the actual trainable control parameters together.  It is
not the linear head, arbitrary resource table, or a general transformer.

The exact Fréchet derivative reuses `CEGradient`'s categorical composition
theorem.  One-Lipschitz `tanh` is proved from its derivative and the mean
value theorem; it is not assumed.  A later nonlinear safe-step theorem still
has to account for the nonlinear Taylor remainder: the linear CE update and
its logarithm displacement equality cannot simply be transplanted here.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.GatedCEGradient

open Hagi.Model Real

variable {V : Type} [Fintype V]
variable {d : ℕ}

/-- Tanh derivative constructed from the pinned real hyperbolic primitives. -/
theorem hasDerivAt_tanh_coshInvSq (x : ℝ) :
    HasDerivAt Real.tanh (1 / (Real.cosh x) ^ 2) x := by
  have hq := (hasDerivAt_sinh x).div (hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x))
  have hden : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
      (Real.cosh x) ^ 2 = 1 / (Real.cosh x) ^ 2 := by
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have heq : Real.sinh / Real.cosh = Real.tanh := by
    funext z
    exact (Real.tanh_eq_sinh_div_cosh z).symm
  rw [← heq]
  simpa only [Real.tanh_eq_sinh_div_cosh, hden] using hq

/-- Tanh is globally 1-Lipschitz, from a computed derivative bound. -/
theorem abs_tanh_sub_le (x y : ℝ) :
    |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  have hdiff : Differentiable ℝ Real.tanh := fun z =>
    (hasDerivAt_tanh_coshInvSq z).differentiableAt
  have hunit (z : ℝ) : ‖deriv Real.tanh z‖ ≤ (1 : ℝ) := by
    have hval := (hasDerivAt_tanh_coshInvSq z).deriv
    rw [hval, norm_of_nonneg (by positivity : 0 ≤ 1 / (Real.cosh z) ^ 2)]
    apply (div_le_one (by positivity : (0 : ℝ) < (Real.cosh z) ^ 2)).2
    nlinarith [Real.cosh_sq_sub_sinh_sq z, sq_nonneg (Real.sinh z)]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _hz => hdiff z) (fun z _hz => hunit z) convex_univ
    (Set.mem_univ x) (Set.mem_univ y)
  simpa [Real.norm_eq_abs, one_mul, abs_sub_comm] using h

/-- The actual forward logits of the gated control family. -/
noncomputable def gatedForward (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) : V → ℝ := fun v =>
  ∑ j, X v j * Real.tanh (θ.ofLp j)

/-- Actual action of the gated Jacobian on a supplied direction. -/
noncomputable def gatedAction (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) (v : V) : ℝ :=
  ∑ j, X v j * (1 / (Real.cosh (θ.ofLp j)) ^ 2 * D.ofLp j)

/-- Coordinate projection already supplied by the pinned Euclidean API. -/
private noncomputable def gatedProjection (j : Fin d) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => w.ofLp j
      map_add' := by intro w z; rfl
      map_smul' := by intro c w; rfl }

private theorem gatedProjection_apply (D : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    gatedProjection j D = D.ofLp j := rfl

/-- Full continuous-linear Jacobian, expressed as finite projections. -/
private noncomputable def gatedJacobian (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] (V → ℝ) :=
  ContinuousLinearMap.pi (fun v =>
    ∑ j, X v j • ((1 / (Real.cosh (θ.ofLp j)) ^ 2) • gatedProjection j))

private theorem gatedJacobian_apply (X : Matrix V (Fin d) ℝ)
    (θ D : EuclideanSpace ℝ (Fin d)) (v : V) :
    gatedJacobian X θ D v = gatedAction X θ D v := by
  simp [gatedJacobian, gatedAction, gatedProjection_apply]

/-- The forward map has the exact native parameter Jacobian above. -/
private theorem hasFDerivAt_gatedForward (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (gatedForward X) (gatedJacobian X θ) θ := by
  have hrow (v : V) : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) =>
      ∑ j, X v j * Real.tanh (w.ofLp j))
      (∑ j, X v j • ((1 / (Real.cosh (θ.ofLp j)) ^ 2) •
        gatedProjection j)) θ := by
    have hproj (j : Fin d) : HasFDerivAt
        (fun w : EuclideanSpace ℝ (Fin d) => w.ofLp j) (gatedProjection j) θ := by
      exact (gatedProjection j).hasFDerivAt
    have hcoord (j : Fin d) : HasFDerivAt
        (fun w : EuclideanSpace ℝ (Fin d) => Real.tanh (w.ofLp j))
        ((1 / (Real.cosh (θ.ofLp j)) ^ 2) • gatedProjection j) θ := by
      convert (hasDerivAt_tanh_coshInvSq (θ.ofLp j)).hasFDerivAt.comp θ (hproj j)
        using 1 <;> (ext D; simp [gatedProjection_apply]) <;> ring
    have hmul (j : Fin d) := (hcoord j).const_mul (X v j)
    have hsum := HasFDerivAt.sum (u := Finset.univ)
      (A := fun j (w : EuclideanSpace ℝ (Fin d)) =>
        X v j * Real.tanh (w.ofLp j))
      (A' := fun j => X v j • ((1 / (Real.cosh (θ.ofLp j)) ^ 2) •
        gatedProjection j))
      (fun j _hj => hmul j)
    convert hsum using 1 <;> (ext w; simp)
  exact hasFDerivAt_pi.2 hrow

/-- Exact categorical-CE action with respect to actual hidden controls. -/
theorem fderiv_ceOneHot_gatedForward [Nonempty V] [DecidableEq V]
    (X : Matrix V (Fin d) ℝ) (θ D : EuclideanSpace ℝ (Fin d)) (t : V) :
    fderiv ℝ (fun w => Hagi.ceOneHot t (gatedForward X w)) θ D =
      ∑ v, (Hagi.Prelude.softDef (gatedForward X θ) v -
        if v = t then 1 else 0) * gatedAction X θ D v := by
  rw [CEGradient.fderiv_ceOneHot_comp_apply
    (gatedForward X) (gatedJacobian X θ) θ D t
    (hasFDerivAt_gatedForward X θ)]
  exact Finset.sum_congr rfl fun v _hv => by rw [gatedJacobian_apply]

/-- The nonlinear forward map is differentiable in its controls everywhere. -/
theorem differentiable_gatedForward (X : Matrix V (Fin d) ℝ) :
    Differentiable ℝ (gatedForward X) := fun θ =>
  (hasFDerivAt_gatedForward X θ).differentiableAt

end Hagi.Model.GatedCEGradient
