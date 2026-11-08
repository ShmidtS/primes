/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEDescent
import Hagi.Model.CEJacobianMajorizer
import Hagi.Model.GatedCEUniformCurvature

/-!
# One-coordinate latent/readout expansion of a finite categorical head

The appended latent feature can be arbitrary.  A zero appended readout
coefficient preserves every logit and every categorical cross-entropy loss.
The new coefficient remains available to an ordinary parameter update.
These equations concern the supplied finite model, not a Transformer,
held-out performance, native computation or universal architecture optimality.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.CEExpansion

open Hagi.Model

/-- Append one supplied latent feature to every finite categorical row. -/
def expandedFeatures {V : Type} {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (Z : V → ℝ) :
    Matrix V (Fin (d + 1)) ℝ :=
  fun v => Fin.snoc (X v) (Z v)

/-- Append one readout coefficient to the existing finite parameters. -/
noncomputable def expandedParameters {d : ℕ}
    (θ : EuclideanSpace ℝ (Fin d)) (gamma : ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.snoc θ.ofLp gamma)

/-- The exact enlarged logit is the old logit plus the new feature times
its readout coefficient. -/
theorem ceLogits_expandedParameters {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (Z : V → ℝ) (gamma : ℝ) (v : V) :
    ceLogits (expandedFeatures X Z) (expandedParameters θ gamma) v =
      ceLogits X θ v + Z v * gamma := by
  simp [ceLogits, Matrix.mulVec, dotProduct, expandedFeatures,
    expandedParameters, Fin.sum_univ_castSucc]

/-- A zero new readout coefficient preserves categorical cross-entropy.
The new latent feature need not vanish. -/
theorem ceOneHot_expandedParameters_zero {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (Z : V → ℝ) (t : V) :
    Hagi.ceOneHot t (ceLogits (expandedFeatures X Z)
      (expandedParameters θ 0)) = Hagi.ceOneHot t (ceLogits X θ) := by
  congr 1
  funext v
  simpa using ceLogits_expandedParameters X θ Z 0 v

/-- The exact Jacobian of appending and varying the scalar readout. -/
noncomputable def expandedReadoutJacobian {V : Type} [Fintype V]
    (Z : V → ℝ) : ℝ →L[ℝ] (V → ℝ) :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) Z

/-- Evaluation is the ordinary pointwise scalar action. -/
theorem expandedReadoutJacobian_apply {V : Type} [Fintype V]
    (Z : V → ℝ) (gamma : ℝ) :
    expandedReadoutJacobian Z gamma = gamma • Z := rfl

/-- The assembled enlarged logits are affine, with the exact readout
Jacobian.  No additional smoothness hypothesis is needed. -/
theorem hasFDerivAt_ceLogits_expandedParameters
    {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (Z : V → ℝ) (gamma : ℝ) :
    HasFDerivAt
      (fun eta => ceLogits (expandedFeatures X Z)
        (expandedParameters θ eta))
      (expandedReadoutJacobian Z) gamma := by
  have hfun : (fun eta : ℝ => ceLogits X θ +
      (expandedReadoutJacobian Z) eta) =
      (fun eta => ceLogits (expandedFeatures X Z)
        (expandedParameters θ eta)) := by
    funext eta v
    change ceLogits X θ v + eta * Z v =
      ceLogits (expandedFeatures X Z) (expandedParameters θ eta) v
    rw [ceLogits_expandedParameters]
    ring
  rw [← hfun]
  exact (expandedReadoutJacobian Z).hasFDerivAt.const_add (ceLogits X θ)

/-- A supervised residual feature gives a certified one-step enlarged
readout.  The residual is the target prediction minus the current softmax;
its finite second moment supplies the step, not an additional premise. -/
theorem ceOneHot_expandedParameters_residual_step_le
    {V : Type} [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (Z : V → ℝ) (t : V)
    (hZ : ∀ v, Z v = (if v = t then 1 else 0) -
      Hagi.Prelude.softDef (ceLogits X θ) v) :
    Hagi.ceOneHot t (ceLogits (expandedFeatures X Z)
      (expandedParameters θ (∑ v : V, Z v ^ 2))) ≤
      Hagi.ceOneHot t (ceLogits X θ) -
        (∑ v : V, Z v ^ 2) ^ 2 / 2 := by
  set D : ℝ := ∑ v : V, Z v ^ 2 with hD
  let g : ℝ → V → ℝ := fun eta => ceLogits (expandedFeatures X Z)
    (expandedParameters θ eta)
  let J : ℝ →L[ℝ] (V → ℝ) := expandedReadoutJacobian Z
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg (fun v _hv => sq_nonneg (Z v))
  have hf : HasFDerivAt g J 0 := by
    dsimp [g, J]
    exact hasFDerivAt_ceLogits_expandedParameters X θ Z 0
  have hzero : g 0 = ceLogits X θ := by
    funext v
    simp only [g, ceLogits_expandedParameters, mul_zero, add_zero]
  have hA : D * D =
      -(fderiv ℝ (fun w => Hagi.ceOneHot t (g w)) 0 D) := by
    rw [CEGradient.fderiv_ceOneHot_comp_apply g J 0 D t hf, hzero]
    simp only [J, expandedReadoutJacobian_apply, Pi.smul_apply, smul_eq_mul]
    calc
      D * D = D * ∑ v : V, Z v ^ 2 := rfl
      _ = ∑ v : V, D * (Z v * Z v) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun v _hv => by ring)
      _ = -(∑ v : V,
          (Hagi.Prelude.softDef (ceLogits X θ) v - if v = t then 1 else 0) *
            (D * Z v)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro v _hv
        rw [hZ v]
        ring
  have hZrange (v : V) : -1 ≤ Z v ∧ Z v ≤ 1 := by
    have hp0 := (Hagi.Prelude.softDef_pos (ceLogits X θ) v).le
    have hp1 := GatedCEUniformCurvature.softDef_le_one (ceLogits X θ) v
    rw [hZ v]
    split_ifs <;> constructor <;> linarith
  have hR : ∀ u v, (J D) u - (J D) v ≤ 2 * D := by
    intro u v
    simp only [J, expandedReadoutJacobian_apply, Pi.smul_apply, smul_eq_mul]
    have hu := mul_le_mul_of_nonneg_left (hZrange u).2 hD
    have hv := mul_le_mul_of_nonneg_left (hZrange v).1 hD
    linarith
  have hrepr (eta : ℝ) : g eta = g 0 + J eta := by
    rw [hzero]
    funext v
    simp only [g, J, ceLogits_expandedParameters,
      expandedReadoutJacobian_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hrem : ∀ w ∈ Metric.closedBall (0 : ℝ) D,
      ‖g w - g 0 - J (w - 0)‖ ≤ 0 * ‖w - 0‖ ^ 2 := by
    intro w _hw
    have hzero_rem : g w - g 0 - J (w - 0) = 0 := by
      rw [hrepr w, map_sub, map_zero, sub_zero, sub_sub, sub_self]
    rw [hzero_rem, norm_zero]
    norm_num
  have hcap : (1 : ℝ) * ‖D‖ ≤ D := by
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg hD]
  have hmajor :=
    Hagi.Model.CEJacobianMajorizer.ceOneHot_local_line_majorize_of_jacobian_remainder
      (f := g) (J := J) (θ := (0 : ℝ)) (d := D) (y := t)
      (r := D) (R := 2 * D) (ρ := 0) (A := D * D) (η := 1)
      hf hA hR hrem (by norm_num) hcap
  rw [zero_add, one_smul] at hmajor
  have hbase := ceOneHot_expandedParameters_zero X θ Z t
  change Hagi.ceOneHot t (g 0) = Hagi.ceOneHot t (ceLogits X θ) at hbase
  change Hagi.ceOneHot t (ceLogits (expandedFeatures X Z)
    (expandedParameters θ D)) ≤
      Hagi.ceOneHot t (ceLogits X θ) - D ^ 2 / 2
  calc
    Hagi.ceOneHot t (ceLogits (expandedFeatures X Z)
      (expandedParameters θ D)) = Hagi.ceOneHot t (g D) := rfl
    _ ≤ Hagi.ceOneHot t (g 0) - 1 * (D * D) +
        (1 : ℝ) ^ 2 * ((2 * D) ^ 2 / 8 + 2 * 0 * ‖D‖ ^ 2) := hmajor
    _ = Hagi.ceOneHot t (ceLogits X θ) - D ^ 2 / 2 := by
      rw [hbase]
      ring

/-- Declared operation-cell count for preparing the new finite batch /
vocabulary block, in the same abstract operation unit as supplied training
costs.  This is not physical FLOPs, RAM, bytes or execution time. -/
def expandedFeatureEvaluationCount (B : ℕ) (V : Type) [Fintype V] : ℕ :=
  B * Fintype.card V

end Hagi.Model.CEExpansion
