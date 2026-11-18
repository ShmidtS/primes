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

/-!
# Global second-order control for the scalar hyperbolic tangent

This module defines `sechSq x = 1 - tanh(x)^2`, identifies it with the
reciprocal squared hyperbolic cosine, and bounds its derivative globally.
Two mean-value arguments then give a conservative second-order Taylor
remainder bound for `tanh`.  These are scalar analytic estimates only; no
optimizer safe-step or convergence claim is made.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.TanhTaylor

open Hagi.Model.GatedCEGradient

/-- The derivative of `Real.tanh`, written without a denominator. -/
noncomputable def sechSq (x : ℝ) : ℝ :=
  1 - Real.tanh x ^ 2

/-- `sechSq` agrees with the reciprocal squared hyperbolic cosine. -/
theorem sechSq_eq_coshInvSq (x : ℝ) :
    sechSq x = 1 / (Real.cosh x) ^ 2 := by
  unfold sechSq
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- The exact derivative of `sechSq`. -/
theorem hasDerivAt_sechSq (x : ℝ) :
    HasDerivAt sechSq (-2 * Real.tanh x * sechSq x) x := by
  change HasDerivAt (fun z => 1 - Real.tanh z ^ 2)
    (-2 * Real.tanh x * sechSq x) x
  rw [sechSq_eq_coshInvSq]
  convert (hasDerivAt_tanh_coshInvSq x).pow 2 |>.const_sub 1 using 1
  ring

/-- The derivative of `sechSq` has global norm bound `2`. -/
theorem norm_deriv_sechSq_le (x : ℝ) : ‖deriv sechSq x‖ ≤ (2 : ℝ) := by
  rw [(hasDerivAt_sechSq x).deriv, Real.norm_eq_abs, sechSq_eq_coshInvSq]
  have ht := Real.abs_tanh_lt_one x
  have hs0 : 0 ≤ 1 / (Real.cosh x) ^ 2 := by positivity
  have hs1 : 1 / (Real.cosh x) ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity : (0 : ℝ) < (Real.cosh x) ^ 2)).2
    nlinarith [Real.cosh_sq_sub_sinh_sq x, sq_nonneg (Real.sinh x)]
  have habs : |1 / (Real.cosh x) ^ 2| = 1 / (Real.cosh x) ^ 2 := abs_of_nonneg hs0
  rw [abs_mul, abs_mul, habs]
  norm_num
  calc
    2 * |Real.tanh x| * (Real.cosh x ^ 2)⁻¹
        ≤ 2 * 1 * (Real.cosh x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht.le (by norm_num)) (by simpa [one_div] using hs0)
    _ ≤ 2 * 1 * 1 :=
      mul_le_mul_of_nonneg_left (by simpa [one_div] using hs1) (by positivity)
    _ = 2 := by norm_num

/-- `sechSq` is globally `2`-Lipschitz. -/
theorem abs_sechSq_sub_le (x y : ℝ) :
    |sechSq x - sechSq y| ≤ 2 * |x - y| := by
  have hdiff (z : ℝ) : DifferentiableAt ℝ sechSq z :=
    (hasDerivAt_sechSq z).differentiableAt
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _hz => hdiff z) (fun z _hz => norm_deriv_sechSq_le z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa [Real.norm_eq_abs, abs_sub_comm, mul_comm] using h

/-- Second-order Taylor remainder for `tanh`, with global constant `2`. -/
theorem abs_tanh_taylor_sub_le (x y : ℝ) :
    |Real.tanh y - Real.tanh x - sechSq x * (y - x)| ≤ 2 * (y - x) ^ 2 := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · obtain ⟨c, hc, hmean⟩ := exists_hasDerivAt_eq_slope Real.tanh sechSq hxy
      (fun z _hz => (hasDerivAt_tanh_coshInvSq z).continuousAt.continuousWithinAt)
      (fun z _hz =>
        (hasDerivAt_tanh_coshInvSq z).congr_deriv (sechSq_eq_coshInvSq z).symm)
    have hyx : 0 < y - x := sub_pos.mpr hxy
    have htanh : Real.tanh y - Real.tanh x = sechSq c * (y - x) := by
      calc
        Real.tanh y - Real.tanh x =
            ((Real.tanh y - Real.tanh x) / (y - x)) * (y - x) :=
          (div_mul_cancel₀ _ (sub_ne_zero.mpr hxy.ne')).symm
        _ = sechSq c * (y - x) := by rw [← hmean]
    have hid : Real.tanh y - Real.tanh x - sechSq x * (y - x) =
        (sechSq c - sechSq x) * (y - x) := by
      rw [htanh]
      ring
    rw [hid, abs_mul]
    have hcx : |c - x| ≤ |y - x| := by
      rw [abs_of_pos (sub_pos.mpr hc.1), abs_of_pos hyx]
      exact sub_le_sub_right hc.2.le x
    calc
      |sechSq c - sechSq x| * |y - x| ≤ (2 * |c - x|) * |y - x| :=
        mul_le_mul_of_nonneg_right (abs_sechSq_sub_le c x) (abs_nonneg _)
      _ ≤ (2 * |y - x|) * |y - x| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcx (by norm_num)) (abs_nonneg _)
      _ = 2 * (y - x) ^ 2 := by
        calc
          (2 * |y - x|) * |y - x| = 2 * |y - x| ^ 2 := by ring
          _ = 2 * (y - x) ^ 2 := by rw [sq_abs]
  · subst y
    simp
  · obtain ⟨c, hc, hmean⟩ := exists_hasDerivAt_eq_slope Real.tanh sechSq hxy
      (fun z _hz => (hasDerivAt_tanh_coshInvSq z).continuousAt.continuousWithinAt)
      (fun z _hz =>
        (hasDerivAt_tanh_coshInvSq z).congr_deriv (sechSq_eq_coshInvSq z).symm)
    have hyx : 0 < x - y := sub_pos.mpr hxy
    have htanh : Real.tanh x - Real.tanh y = sechSq c * (x - y) := by
      calc
        Real.tanh x - Real.tanh y =
            ((Real.tanh x - Real.tanh y) / (x - y)) * (x - y) :=
          (div_mul_cancel₀ _ (sub_ne_zero.mpr hxy.ne')).symm
        _ = sechSq c * (x - y) := by rw [← hmean]
    have htanhyx : Real.tanh y - Real.tanh x = sechSq c * (y - x) := by
      calc
        Real.tanh y - Real.tanh x = -(Real.tanh x - Real.tanh y) := by ring
        _ = -(sechSq c * (x - y)) := by rw [← htanh]
        _ = sechSq c * (y - x) := by ring
    have hid : Real.tanh y - Real.tanh x - sechSq x * (y - x) =
        (sechSq c - sechSq x) * (y - x) := by
      rw [htanhyx]
      ring
    rw [hid, abs_mul]
    have hcx : |c - x| ≤ |y - x| := by
      rw [abs_of_neg (sub_neg.mpr hc.2), abs_of_neg (sub_neg.mpr hxy)]
      linarith [hc.1]
    calc
      |sechSq c - sechSq x| * |y - x| ≤ (2 * |c - x|) * |y - x| :=
        mul_le_mul_of_nonneg_right (abs_sechSq_sub_le c x) (abs_nonneg _)
      _ ≤ (2 * |y - x|) * |y - x| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcx (by norm_num)) (abs_nonneg _)
      _ = 2 * (y - x) ^ 2 := by
        calc
          (2 * |y - x|) * |y - x| = 2 * |y - x| ^ 2 := by ring
          _ = 2 * (y - x) ^ 2 := by rw [sq_abs]

end Hagi.Model.TanhTaylor

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
  rw [Hagi.Energy.smax_eq_softDef z] at hlse
  simp only [add_sub_cancel_left] at hlse
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
