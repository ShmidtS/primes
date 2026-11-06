/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Core.Concat

/-!
# Finite-dimensional cross-entropy gradient

The derivative of one-hot cross-entropy on the logits `X *ᵥ θ` is the
transposed-feature residual `Xᵀ (softmax (Xθ) - oneHot t)`.  This file
proves its directional Fréchet-derivative form for arbitrary finite
vocabularies and finite feature dimensions.

Reference search found no existing one-hot CE derivative in the project
or in this Mathlib snapshot.  The construction uses the combinator APIs
in pinned Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`:
`FDeriv/Add.lean`, `FDeriv/Prod.lean`, `FDeriv/Linear.lean`,
`ExpDeriv.lean`, and `Log/Deriv.lean`.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.CEGradient

/-- `HasFDerivAt` with the canonical normed-space instances made
explicit.  The pin generalizes derivatives to topological vector spaces;
using this private abbreviation keeps all the normed-space combinators
on one definitional instance path. -/
private abbrev HasFDerivAtNormed
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (f' : E →L[𝕜] F) (x : E) : Prop :=
  @HasFDerivAt 𝕜 _ E NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
    NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
    F NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
    NormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
    f f' x

/-- The linear feature map `w ↦ X *ᵥ w.ofLp`, bundled as a continuous
linear map.  Continuity follows from finite dimensionality of the
parameter space, without assumptions on the entries of `X`. -/
private noncomputable def featureCLM {V : Type*} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] (V → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => X *ᵥ w.ofLp
      map_add' := by
        intro w₁ w₂
        change X *ᵥ (w₁.ofLp + w₂.ofLp) =
          X *ᵥ w₁.ofLp + X *ᵥ w₂.ofLp
        exact Matrix.mulVec_add X w₁.ofLp w₂.ofLp
      map_smul' := by
        intro c w
        change X *ᵥ (c • w.ofLp) = c • (X *ᵥ w.ofLp)
        exact Matrix.mulVec_smul X c w.ofLp }

private theorem featureCLM_apply {V : Type*} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    featureCLM X w = X *ᵥ w.ofLp := rfl

private theorem hasFDerivAt_feature {V : Type*} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAtNormed (fun w : EuclideanSpace ℝ (Fin d) => X *ᵥ w.ofLp)
      (featureCLM X) θ := by
  exact (featureCLM X).hasFDerivAt

/-- The derivative of log-sum-exp, as the inverse normalizer times the
sum of the exp-weighted coordinate functionals. -/
private noncomputable def lseDeriv {V : Type*} [Fintype V] (z : V → ℝ) :
    (V → ℝ) →L[ℝ] ℝ :=
  (∑ v, Real.exp (z v))⁻¹ •
    ∑ v, Real.exp (z v) •
      (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)

private theorem hasFDerivAt_lse {V : Type*} [Fintype V] [Nonempty V]
    (z : V → ℝ) : HasFDerivAtNormed Hagi.lse (lseDeriv z) z := by
  have hexp (v : V) : HasFDerivAtNormed (fun y : V → ℝ => Real.exp (y v))
      (Real.exp (z v) •
        (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ)) z :=
    (hasFDerivAt_apply v z).exp
  have hsum0 := HasFDerivAt.sum (u := Finset.univ)
    (A := fun v (y : V → ℝ) => Real.exp (y v))
    (A' := fun v => Real.exp (z v) •
      (ContinuousLinearMap.proj v : (V → ℝ) →L[ℝ] ℝ))
    (fun v _ => hexp v)
  have hfun : (∑ v, fun y : V → ℝ => Real.exp (y v)) =
      (fun y => ∑ v, Real.exp (y v)) := by
    ext y
    simp only [Finset.sum_apply]
  rw [hfun] at hsum0
  have hlog := hsum0.log (ne_of_gt (Hagi.Core.exp_sum_pos z))
  change HasFDerivAtNormed (fun y : V → ℝ => Real.log (∑ v, Real.exp (y v)))
    (lseDeriv z) z
  simpa only [lseDeriv] using hlog

private theorem hasFDerivAt_ceOneHot {V : Type*} [Fintype V] [Nonempty V]
    (t : V) (z : V → ℝ) :
    HasFDerivAtNormed (Hagi.ceOneHot t)
      (lseDeriv z -
        (ContinuousLinearMap.proj t : (V → ℝ) →L[ℝ] ℝ)) z := by
  have h := (hasFDerivAt_lse z).sub (hasFDerivAt_apply t z)
  change HasFDerivAtNormed (Hagi.lse - fun y : V → ℝ => y t)
    (lseDeriv z - (ContinuousLinearMap.proj t : (V → ℝ) →L[ℝ] ℝ)) z
  exact h

private theorem hasFDerivAt_ceOneHot_mulVec {V : Type*} [Fintype V]
    [Nonempty V] {d : ℕ} (X : Matrix V (Fin d) ℝ) (t : V)
    (θ : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAtNormed (fun w : EuclideanSpace ℝ (Fin d) =>
      Hagi.ceOneHot t (X *ᵥ w.ofLp))
      ((lseDeriv (X *ᵥ θ.ofLp) -
        (ContinuousLinearMap.proj t : (V → ℝ) →L[ℝ] ℝ)).comp
        (featureCLM X)) θ := by
  have h := (hasFDerivAt_ceOneHot t (X *ᵥ θ.ofLp)).comp θ
    (hasFDerivAt_feature X θ)
  simpa only [Function.comp_def] using h

private theorem ceDeriv_apply {V : Type*} [Fintype V] [DecidableEq V]
    (t : V) (z u : V → ℝ) :
    (lseDeriv z - (ContinuousLinearMap.proj t : (V → ℝ) →L[ℝ] ℝ)) u =
      ∑ v, (Hagi.Prelude.softDef z v - if v = t then 1 else 0) * u v := by
  have hnormalized : (∑ v, Real.exp (z v))⁻¹ * (∑ v, Real.exp (z v) * u v) =
      ∑ v, Hagi.Prelude.softDef z v * u v := by
    calc
      (∑ v, Real.exp (z v))⁻¹ * (∑ v, Real.exp (z v) * u v) =
          (∑ v, Real.exp (z v) * u v) / ∑ v, Real.exp (z v) := by
            rw [div_eq_inv_mul]
      _ = ∑ v, (Real.exp (z v) / ∑ b, Real.exp (z b)) * u v := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl (fun v _ => by ring)
      _ = ∑ v, Hagi.Prelude.softDef z v * u v := rfl
  have hone : u t = ∑ v, (if v = t then 1 else 0) * u v := by simp
  simp only [lseDeriv, sub_apply, smul_apply, sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [hnormalized, hone, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun v _ => by ring)

/-- Directional Fréchet derivative of finite one-hot cross-entropy on
linear features.  The right-hand side is the action of
`Xᵀ (softmax (Xθ) - oneHot t)` on `h`. -/
theorem fderiv_ceOneHot_mulVec
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (t : V)
    (θ h : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin d) =>
      Hagi.ceOneHot t (X *ᵥ w.ofLp)) θ h =
      ∑ v, (Hagi.Prelude.softDef (X *ᵥ θ.ofLp) v
        - if v = t then 1 else 0) * (X *ᵥ h.ofLp) v := by
  rw [(hasFDerivAt_ceOneHot_mulVec X t θ).fderiv]
  simp only [ContinuousLinearMap.comp_apply, featureCLM_apply]
  exact ceDeriv_apply t (X *ᵥ θ.ofLp) (X *ᵥ h.ofLp)

end Hagi.Model.CEGradient
