/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Model.CEJacobianMajorizer
import Hagi.Model.TanhTaylor

/-!
# Nonlinear two-logit CE step from the local Jacobian majorizer

The model `x ↦ ![Real.tanh x, 0]` has an exact finite-Pi Fréchet derivative
and the proved Taylor remainder. Its actual CE directional derivative supplies
positive alignment, and a capped local majorizer gives a quantitative one-step
bound and strict decrease. This does not state exact actual drop equality,
a general optimizer, or global training/architecture optimality.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.TanhCEStep

open Hagi.Model.TanhTaylor

/-- The affine embedding `x ↦ ![x, 0]`, bundled as a continuous linear map.
The explicit finite-dimensional linear-map construction is bundled as a
continuous linear map. -/
private noncomputable def tanhEmbedding : ℝ →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ![x, 0]
      map_add' := by
        intro x z
        ext i
        fin_cases i <;> simp
      map_smul' := by
        intro a x
        ext i
        fin_cases i <;> simp }

/-- The concrete two-logit model using the ordinary finite-Pi sup norm. -/
private noncomputable def tanhModel (x : ℝ) : Fin 2 → ℝ :=
  tanhEmbedding (Real.tanh x)

/-- The scalar derivative at `θ`, viewed as the span of `sechSq θ`, followed
by the two-logit embedding. -/
private noncomputable def tanhJacobian (θ : ℝ) : ℝ →L[ℝ] (Fin 2 → ℝ) :=
  tanhEmbedding.comp (ContinuousLinearMap.toSpanSingleton ℝ (sechSq θ))

@[simp] private theorem tanhEmbedding_apply_zero (x : ℝ) :
    tanhEmbedding x 0 = x := rfl

@[simp] private theorem tanhEmbedding_apply_one (x : ℝ) :
    tanhEmbedding x 1 = 0 := rfl

/-- The Jacobian acts by `sechSq θ` in the first coordinate and by zero in
the second. -/
private theorem tanhJacobian_apply (θ h : ℝ) :
    tanhJacobian θ h = ![h * sechSq θ, 0] := by
  change tanhEmbedding (h * sechSq θ) = ![h * sechSq θ, 0]
  rfl

/-- Exact Fréchet derivative of the literal finite-Pi tanh model. -/
private theorem hasFDerivAt_tanhModel (θ : ℝ) :
    HasFDerivAt tanhModel (tanhJacobian θ) θ := by
  have hscalar : HasDerivAt Real.tanh (sechSq θ) θ :=
    (GatedCEGradient.hasDerivAt_tanh_coshInvSq θ).congr_deriv
      (sechSq_eq_coshInvSq θ).symm
  have hcomp := tanhEmbedding.hasFDerivAt.comp θ hscalar.hasFDerivAt
  change HasFDerivAt tanhModel (tanhJacobian θ) θ at hcomp
  exact hcomp

@[simp] private theorem sechSq_zero : sechSq 0 = 1 := by
  simp [sechSq]

/-- At zero the Jacobian is exactly the affine embedding, not merely an
extensionally equivalent scalar-coefficient formula. -/
private theorem tanhJacobian_zero : tanhJacobian 0 = tanhEmbedding := by
  apply ContinuousLinearMap.ext
  intro h
  change tanhEmbedding (h * sechSq 0) = tanhEmbedding h
  rw [sechSq_zero, mul_one]

/-- Literal evaluation requested for the later positive-alignment check. -/
private theorem tanhJacobian_zero_apply (x : ℝ) :
    tanhJacobian 0 x = ![x, 0] := by
  rw [tanhJacobian_zero]
  rfl

/-- In particular, the zero-point Jacobian sends direction `1` to `![1,0]`. -/
private theorem tanhJacobian_zero_one : tanhJacobian 0 1 = ![1, 0] := by
  exact tanhJacobian_zero_apply 1

/-- The model is literally `x ↦ ![tanh x, 0]`. -/
private theorem tanhModel_eq_literal (x : ℝ) :
    tanhModel x = ![Real.tanh x, 0] := rfl

/-- The zero-point remainder is the embedding of the scalar tanh Taylor
remainder. -/
private theorem tanhModel_remainder_eq (w : ℝ) :
    tanhModel w - tanhModel 0 - tanhJacobian 0 (w - 0) =
      tanhEmbedding
        (Real.tanh w - Real.tanh 0 - sechSq 0 * (w - 0)) := by
  rw [tanhJacobian_zero]
  change tanhEmbedding (Real.tanh w) - tanhEmbedding (Real.tanh 0) -
    tanhEmbedding (w - 0) =
      tanhEmbedding (Real.tanh w - Real.tanh 0 - sechSq 0 * (w - 0))
  rw [← map_sub, ← map_sub, sechSq_zero, one_mul]

/-- Local premise for the C153 application: `θ = 0`, radius `1`, and `ρ = 2`,
on the ordinary finite-Pi sup-normed space.  The scalar source estimate is
global, so closed-ball membership is intentionally unused. -/
private theorem tanhModel_local_remainder :
    ∀ w ∈ Metric.closedBall (0 : ℝ) 1,
      ‖tanhModel w - tanhModel 0 - tanhJacobian 0 (w - 0)‖ ≤
        2 * ‖w - 0‖ ^ 2 := by
  intro w _hw
  rw [tanhModel_remainder_eq]
  have hbound := abs_tanh_taylor_sub_le 0 w
  have hnonneg : 0 ≤ 2 * ‖w - 0‖ ^ 2 := by positivity
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro i
  fin_cases i
  · change ‖tanhEmbedding
      (Real.tanh w - Real.tanh 0 - sechSq 0 * (w - 0)) 0‖ ≤ _
    simpa only [tanhEmbedding_apply_zero, Real.norm_eq_abs, sq_abs] using hbound
  · change ‖tanhEmbedding
      (Real.tanh w - Real.tanh 0 - sechSq 0 * (w - 0)) 1‖ ≤ _
    rw [tanhEmbedding_apply_one, norm_zero]
    exact hnonneg



/-- The exact two-logit tanh step has at least the rational decrease
certified by the imported C153 local Jacobian majorizer. -/
theorem ceOneHot_tanh_step_le :
    Hagi.ceOneHot (0 : Fin 2) ![Real.tanh ((2 : ℝ) / 33), 0] ≤
      Hagi.ceOneHot (0 : Fin 2) ![0, 0] - 1 / 66 := by
  have hA : (1 / 2 : ℝ) =
      -(fderiv ℝ (fun w => Hagi.ceOneHot (0 : Fin 2) (tanhModel w)) 0 1) := by
    rw [CEGradient.fderiv_ceOneHot_comp_apply tanhModel (tanhJacobian 0)
      0 1 0 (hasFDerivAt_tanhModel 0)]
    norm_num [Hagi.Prelude.softDef, Fin.sum_univ_two, tanhModel_eq_literal,
      tanhJacobian_zero_apply]
  have hR : ∀ u v : Fin 2,
      (tanhJacobian 0 1) u - (tanhJacobian 0 1) v ≤ (1 : ℝ) := by
    intro u v
    rw [tanhJacobian_zero_one]
    fin_cases u <;> fin_cases v <;> norm_num
  have hη : (0 : ℝ) ≤ (2 : ℝ) / 33 := by norm_num
  have hcap : ((2 : ℝ) / 33) * ‖(1 : ℝ)‖ ≤ (1 : ℝ) := by
    rw [norm_one]
    norm_num
  have hmajor :=
    CEJacobianMajorizer.ceOneHot_local_line_majorize_of_jacobian_remainder
      (f := tanhModel) (J := tanhJacobian 0) (θ := (0 : ℝ))
      (d := (1 : ℝ)) (y := (0 : Fin 2)) (r := 1) (R := 1)
      (ρ := 2) (A := 1 / 2) (η := (2 : ℝ) / 33)
      (hf := hasFDerivAt_tanhModel 0) (hA := hA) (hR := hR)
      (hrem := tanhModel_local_remainder) (hη := hη) (hcap := hcap)
  calc
    Hagi.ceOneHot (0 : Fin 2) ![Real.tanh ((2 : ℝ) / 33), 0] ≤
        Hagi.ceOneHot (0 : Fin 2) ![0, 0] - ((2 : ℝ) / 33) * (1 / 2) +
          ((2 : ℝ) / 33) ^ 2 * (1 ^ 2 / 8 + 2 * 2 * ‖(1 : ℝ)‖ ^ 2) := by
      simpa only [zero_add, smul_eq_mul, mul_one, tanhModel_eq_literal,
        Real.tanh_zero] using hmajor
    _ = Hagi.ceOneHot (0 : Fin 2) ![0, 0] - 1 / 66 := by
      rw [norm_one]
      norm_num
      ring

/-- The quantitative bound yields strict CE decrease; no second majorizer
application and no claim that the actual decrease equals `1 / 66`. -/
theorem ceOneHot_tanh_step_lt :
    Hagi.ceOneHot (0 : Fin 2) ![Real.tanh ((2 : ℝ) / 33), 0] <
      Hagi.ceOneHot (0 : Fin 2) ![0, 0] := by
  have h := ceOneHot_tanh_step_le
  linarith


end Hagi.Model.TanhCEStep
