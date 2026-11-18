/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Model.CEJacobianMajorizer
import Hagi.Model.GatedCEDescent

/-!
# Nonlinear cross-entropy safe step via the Jacobian residual

For a smooth NONLINEAR logit map `f : E → V → ℝ` this module turns the
local Jacobian-remainder majorizer (`CEJacobianMajorizer`) into the
nonlinear analogue of the linear-head safe step (`CEDescent`): a
descent lemma with the explicit composite curvature constant and the
majorizer-minimizing safe step with guaranteed decrease.

The composite gradient identity is the existing chain rule
`CEGradient.fderiv_ceOneHot_comp_apply` (the alignment hypothesis
`A = -D(CE∘f)[d]` is closed by it); no duplicate is stated.

## The composite curvature constant

`nonlinearCurvature R ρ dn = R²/4 + 4ρ·dn` (with `dn = ‖d‖²`) is exactly the
factor behind `η²` in the proved majorizer endpoint
`η²·(R²/8 + 2ρ‖d‖²) = (L_total/2)·η²`; no cross terms are dropped.

## Premises (honest pins)

For a general head the following stay premise-form binders:
the Jacobian-remainder curvature `ρ` (the Taylor-form content of an
`M`-Lipschitz Jacobian bound `‖J θ − J θ'‖ ≤ M‖θ−θ'‖`), the local
ball radius `r`, the Jacobian-direction range `R`, the positive
alignment `0 < A`, and positivity of the curvature constant.  All are
instantiated with proved values for the saturating tanh head below
(`ρ = 2` global, `R = 1`, `A = 1/2`, `L_total = 33/4`, safe step
`2/33`).

No claim: the safe step is optimal for the true cross-entropy (it
minimizes only the computed majorizer), and no iterative convergence
statement is made.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.NonlinearCE

open scoped Matrix
open Hagi.Model.TanhTaylor (sechSq sechSq_eq_coshInvSq)

/-- Composite curvature constant `L_total := R²/4 + 4ρ·dn` (with `dn = ‖d‖²`). -/
noncomputable def nonlinearCurvature (R ρ dn : ℝ) : ℝ := R ^ 2 / 4 + 4 * ρ * dn

noncomputable def nonlinearSafeStep (A L : ℝ) : ℝ := A / L

theorem ceOneHot_nonlinear_descent_le
    {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype V] [Nonempty V]
    (f : E → V → ℝ) (J : E →L[ℝ] (V → ℝ)) (θ d : E) (y : V)
    (r R ρ A η : ℝ)
    (hf : HasFDerivAt f J θ)
    (hA : A = -(fderiv ℝ (fun w => Hagi.ceOneHot y (f w)) θ d))
    (hR : ∀ u v, (J d) u - (J d) v ≤ R)
    (hrem : ∀ w ∈ Metric.closedBall θ r,
      ‖f w - f θ - J (w - θ)‖ ≤ ρ * ‖w - θ‖ ^ 2)
    (hη : 0 ≤ η) (hcap : η * ‖d‖ ≤ r) :
    Hagi.ceOneHot y (f (θ + η • d)) ≤
      Hagi.ceOneHot y (f θ) - η * A + (nonlinearCurvature R ρ (‖d‖ ^ 2) / 2) * η ^ 2 := by
  have hm :=
    Hagi.Model.CEJacobianMajorizer.ceOneHot_local_line_majorize_of_jacobian_remainder
      f J θ d y r R ρ A η hf hA hR hrem hη hcap
  unfold nonlinearCurvature
  have hring : ((R ^ 2 / 4 + 4 * ρ * ‖d‖ ^ 2) / 2) * η ^ 2
      = η ^ 2 * (R ^ 2 / 8 + 2 * ρ * ‖d‖ ^ 2) := by
    ring
  linarith

theorem ceOneHot_nonlinear_safeStep_le
    {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype V] [Nonempty V]
    (f : E → V → ℝ) (J : E →L[ℝ] (V → ℝ)) (θ d : E) (y : V)
    (r R ρ A : ℝ)
    (hf : HasFDerivAt f J θ)
    (hA : A = -(fderiv ℝ (fun w => Hagi.ceOneHot y (f w)) θ d))
    (hR : ∀ u v, (J d) u - (J d) v ≤ R)
    (hrem : ∀ w ∈ Metric.closedBall θ r,
      ‖f w - f θ - J (w - θ)‖ ≤ ρ * ‖w - θ‖ ^ 2)
    (hApos : 0 < A)
    (hLpos : 0 < nonlinearCurvature R ρ (‖d‖ ^ 2))
    (hcap : nonlinearSafeStep A (nonlinearCurvature R ρ (‖d‖ ^ 2)) * ‖d‖ ≤ r) :
    Hagi.ceOneHot y
        (f (θ + nonlinearSafeStep A (nonlinearCurvature R ρ (‖d‖ ^ 2)) • d)) ≤
      Hagi.ceOneHot y (f θ)
        - A ^ 2 / (2 * nonlinearCurvature R ρ (‖d‖ ^ 2)) := by
  have hη : 0 ≤ nonlinearSafeStep A (nonlinearCurvature R ρ (‖d‖ ^ 2)) :=
    div_nonneg hApos.le hLpos.le
  have hmain := ceOneHot_nonlinear_descent_le f J θ d y r R ρ A
    (nonlinearSafeStep A (nonlinearCurvature R ρ (‖d‖ ^ 2))) hf hA hR hrem hη hcap
  have halg : (nonlinearSafeStep A (nonlinearCurvature R ρ (‖d‖ ^ 2)) : ℝ) * A
      = A ^ 2 / nonlinearCurvature R ρ (‖d‖ ^ 2) := by
    unfold nonlinearSafeStep
    field_simp
  have halg2 : (nonlinearCurvature R ρ (‖d‖ ^ 2) / 2)
        * (nonlinearSafeStep A (nonlinearCurvature R ρ (‖d‖ ^ 2))) ^ 2
      = A ^ 2 / nonlinearCurvature R ρ (‖d‖ ^ 2)
        - A ^ 2 / (2 * nonlinearCurvature R ρ (‖d‖ ^ 2)) := by
    unfold nonlinearSafeStep
    field_simp
    ring
  rw [halg, halg2] at hmain
  linarith

theorem ceOneHot_nonlinear_safeStep_lt
    {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype V] [Nonempty V]
    (f : E → V → ℝ) (J : E →L[ℝ] (V → ℝ)) (θ d : E) (y : V)
    (r R ρ A : ℝ)
    (hf : HasFDerivAt f J θ)
    (hA : A = -(fderiv ℝ (fun w => Hagi.ceOneHot y (f w)) θ d))
    (hR : ∀ u v, (J d) u - (J d) v ≤ R)
    (hrem : ∀ w ∈ Metric.closedBall θ r,
      ‖f w - f θ - J (w - θ)‖ ≤ ρ * ‖w - θ‖ ^ 2)
    (hApos : 0 < A)
    (hLpos : 0 < nonlinearCurvature R ρ (‖d‖ ^ 2))
    (hcap : nonlinearSafeStep A (nonlinearCurvature R ρ (‖d‖ ^ 2)) * ‖d‖ ≤ r) :
    Hagi.ceOneHot y (f (θ + nonlinearSafeStep A (nonlinearCurvature R ρ (‖d‖ ^ 2)) • d)) <
      Hagi.ceOneHot y (f θ) := by
  have h := ceOneHot_nonlinear_safeStep_le f J θ d y r R ρ A hf hA hR hrem hApos hLpos hcap
  have hpos : 0 < A ^ 2 / (2 * nonlinearCurvature R ρ (‖d‖ ^ 2)) :=
    div_pos (sq_pos_of_pos hApos) (by positivity)
  linarith

/-! ## Tanh head instantiation -/

noncomputable def tanhHead (x : ℝ) : Fin 2 → ℝ := ![Real.tanh x, 0]

theorem tanhHead_eq_literal (x : ℝ) :
    tanhHead x = ![Real.tanh x, 0] := rfl

noncomputable def tanhHeadEmbedding : ℝ →L[ℝ] (Fin 2 → ℝ) :=
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

theorem tanhHeadEmbedding_apply_zero (x : ℝ) :
    tanhHeadEmbedding x 0 = x := rfl

theorem tanhHeadEmbedding_apply_one (x : ℝ) :
    tanhHeadEmbedding x 1 = 0 := rfl

noncomputable def tanhHeadJ (θ : ℝ) : ℝ →L[ℝ] (Fin 2 → ℝ) :=
  tanhHeadEmbedding.comp (ContinuousLinearMap.toSpanSingleton ℝ (sechSq θ))

theorem hasFDerivAt_tanhHead (θ : ℝ) :
    HasFDerivAt tanhHead (tanhHeadJ θ) θ := by
  have hscalar : HasDerivAt Real.tanh (sechSq θ) θ :=
    (Hagi.Model.GatedCEGradient.hasDerivAt_tanh_coshInvSq θ).congr_deriv
      (sechSq_eq_coshInvSq θ).symm
  exact tanhHeadEmbedding.hasFDerivAt.comp θ hscalar.hasFDerivAt

theorem tanhHeadJ_zero : tanhHeadJ 0 = tanhHeadEmbedding := by
  apply ContinuousLinearMap.ext
  intro h
  change tanhHeadEmbedding (h * sechSq 0) = tanhHeadEmbedding h
  rw [show sechSq 0 = 1 by simp [sechSq], mul_one]

theorem tanhHeadJ_zero_one : tanhHeadJ 0 1 = ![1, 0] := by
  rw [tanhHeadJ_zero]
  rfl

theorem tanhHead_remainder_le :
    ∀ w ∈ Metric.closedBall (0 : ℝ) 1,
      ‖tanhHead w - tanhHead 0 - tanhHeadJ 0 (w - 0)‖ ≤
        2 * ‖w - 0‖ ^ 2 := by
  intro w _hw
  have hJ0 : tanhHeadJ 0 (w - 0) = tanhHeadEmbedding (w - 0) := by
    rw [tanhHeadJ_zero]
  have hemb : tanhHead w - tanhHead 0 - tanhHeadJ 0 (w - 0)
      = tanhHeadEmbedding (Real.tanh w - Real.tanh 0 - 1 * (w - 0)) := by
    rw [hJ0]
    change tanhHeadEmbedding (Real.tanh w) - tanhHeadEmbedding (Real.tanh 0)
      - tanhHeadEmbedding (w - 0) = _
    rw [← map_sub, ← map_sub]
    congr 1
    ring
  rw [hemb]
  have hbound := Hagi.Model.TanhTaylor.abs_tanh_taylor_sub_le 0 w
  have hbound' : |Real.tanh w - Real.tanh 0 - 1 * (w - 0)| ≤
      2 * |w - 0| ^ 2 := by
    have h1 : |w - 0| ^ 2 = (w - 0) ^ 2 := by
      rw [sq_abs]
    rw [h1]
    rw [show sechSq 0 = 1 by simp [sechSq]] at hbound
    simpa only [] using hbound
  have hnn : 0 ≤ 2 * ‖w - 0‖ ^ 2 := by positivity
  apply (pi_norm_le_iff_of_nonneg hnn).2
  intro i
  fin_cases i
  · show ‖tanhHeadEmbedding
        (Real.tanh w - Real.tanh 0 - 1 * (w - 0)) (0 : Fin 2)‖ ≤ _
    rw [tanhHeadEmbedding_apply_zero, Real.norm_eq_abs]
    exact hbound'
  · show ‖tanhHeadEmbedding
        (Real.tanh w - Real.tanh 0 - 1 * (w - 0)) (1 : Fin 2)‖ ≤ _
    rw [tanhHeadEmbedding_apply_one, norm_zero]
    exact hnn

theorem tanhHead_range_le (u v : Fin 2) :
    (tanhHeadJ 0 1) u - (tanhHeadJ 0 1) v ≤ (1 : ℝ) := by
  rw [tanhHeadJ_zero_one]
  fin_cases u <;> fin_cases v <;> norm_num

theorem tanhHead_alignment :
    (1 / 2 : ℝ) =
      -(fderiv ℝ (fun w => Hagi.ceOneHot (0 : Fin 2) (tanhHead w)) 0 1) := by
  rw [Hagi.Model.CEGradient.fderiv_ceOneHot_comp_apply tanhHead
    (tanhHeadJ 0) 0 1 0 (hasFDerivAt_tanhHead 0), tanhHeadJ_zero_one]
  norm_num [Hagi.Prelude.softDef, Fin.sum_univ_two, tanhHead_eq_literal,
    Real.tanh_zero]

theorem tanhHead_norm_one_sq : (‖(1 : ℝ)‖ ^ 2) = 1 := by
  rw [norm_one]
  norm_num

theorem tanhHead_safeStep_value :
    nonlinearSafeStep (1 / 2) (nonlinearCurvature 1 2 1) = 2 / 33 := by
  unfold nonlinearSafeStep nonlinearCurvature
  norm_num

theorem ceOneHot_tanhHead_safeStep_le :
    Hagi.ceOneHot (0 : Fin 2)
        (tanhHead (nonlinearSafeStep (1 / 2) (nonlinearCurvature 1 2 1))) ≤
      Hagi.ceOneHot (0 : Fin 2) (tanhHead 0)
        - (1 / 2) ^ 2 / (2 * nonlinearCurvature 1 2 1) := by
  have hLpos : 0 < nonlinearCurvature 1 2 (‖(1 : ℝ)‖ ^ 2) := by
    rw [tanhHead_norm_one_sq]
    unfold nonlinearCurvature
    norm_num
  have hcap : nonlinearSafeStep (1 / 2)
        (nonlinearCurvature 1 2 (‖(1 : ℝ)‖ ^ 2)) * ‖(1 : ℝ)‖ ≤ 1 := by
    rw [tanhHead_norm_one_sq, tanhHead_safeStep_value, norm_one]
    norm_num
  have hmain := ceOneHot_nonlinear_safeStep_le tanhHead (tanhHeadJ 0) 0 1 0 1 1 2 (1 / 2)
    (hasFDerivAt_tanhHead 0) tanhHead_alignment tanhHead_range_le
    tanhHead_remainder_le (by norm_num) hLpos hcap
  rwa [tanhHead_norm_one_sq, zero_add, smul_eq_mul, mul_one] at hmain

/-- Strict actual CE decrease for the tanh head at the general
nonlinear safe step; no claim that the true drop is optimal. -/
theorem ceOneHot_tanhHead_safeStep_lt :
    Hagi.ceOneHot (0 : Fin 2)
        (tanhHead (nonlinearSafeStep (1 / 2) (nonlinearCurvature 1 2 1))) <
      Hagi.ceOneHot (0 : Fin 2) (tanhHead 0) := by
  have hLpos : 0 < nonlinearCurvature 1 2 (‖(1 : ℝ)‖ ^ 2) := by
    rw [tanhHead_norm_one_sq]
    unfold nonlinearCurvature
    norm_num
  have hcap : nonlinearSafeStep (1 / 2)
        (nonlinearCurvature 1 2 (‖(1 : ℝ)‖ ^ 2)) * ‖(1 : ℝ)‖ ≤ 1 := by
    rw [tanhHead_norm_one_sq, tanhHead_safeStep_value, norm_one]
    norm_num
  have hmain := ceOneHot_nonlinear_safeStep_lt tanhHead (tanhHeadJ 0) 0 1 0 1 1 2 (1 / 2)
    (hasFDerivAt_tanhHead 0) tanhHead_alignment tanhHead_range_le
    tanhHead_remainder_le (by norm_num) hLpos hcap
  rwa [tanhHead_norm_one_sq, zero_add, smul_eq_mul, mul_one] at hmain

end Hagi.Model.NonlinearCE
