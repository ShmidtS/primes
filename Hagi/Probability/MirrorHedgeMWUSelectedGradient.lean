/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Probability.GibbsCore
import Hagi.Probability.GibbsCooling
import Hagi.Probability.EntropyConvexity
import Hagi.Probability.FannesPinsker
import Hagi.Probability.ChernoffCGF
import Hagi.Probability.MomentBounds
import Hagi.Probability.FreedmanTwoSided
import Hagi.Probability.MirrorHedgeMWUSelectedLoss

set_option linter.style.header false

/-!
# MirrorHedgeMWUSelectedGradient

Selected-gradient семейство: selectedGradientMSE/selectedMeanGradientMSE (включая приватные леммы trace и optimalPropensity_value), оценки через upper-bound propensity.
Split from `MirrorHedge` (C259).
-/

namespace Hagi.Probability

open Finset Real

open scoped Classical

/-- Expected squared Euclidean error of one inverse-propensity selected
vector for the fixed full-sum target.  This is a sum-target objective,
not an arithmetic-mean or covariance-matrix claim. -/
noncomputable def selectedGradientMSE {B I : Type*} [Fintype B] [Fintype I]
    (p : PMF B) (g : B → EuclideanSpace ℝ I) : ℝ :=
  pmfMean p (fun b => ‖(p b).toReal⁻¹ • g b - ∑ a, g a‖ ^ 2)

/-- Coordinate expansion of the selected-vector squared-error trace. -/
private theorem selectedGradientMSE_trace {B I : Type*}
    [Fintype B] [Fintype I] (p : PMF B) (m : B → EuclideanSpace ℝ I)
    (v : EuclideanSpace ℝ I) :
    pmfMean p (fun b => ‖(p b).toReal⁻¹ • m b - v‖ ^ 2) =
      ∑ i, pmfMean p (fun b =>
        ((p b).toReal⁻¹ * m b i - v i) ^ 2) := by
  unfold pmfMean
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ b, (p b).toReal *
        ∑ i, (((p b).toReal⁻¹ • m b - v) i) ^ 2) =
        ∑ b, ∑ i, (p b).toReal *
          ((p b).toReal⁻¹ * m b i - v i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [WithLp.ofLp_sub, Pi.sub_apply, WithLp.ofLp_smul,
        Pi.smul_apply, smul_eq_mul]
    _ = ∑ i, ∑ b, (p b).toReal *
          ((p b).toReal⁻¹ * m b i - v i) ^ 2 := Finset.sum_comm

/-- Exact selected-gradient MSE under target-wise support.  Zero gradients
may have zero propensity; without support there is no such closed form. -/
theorem selectedGradientMSE_eq_sum {B I : Type*} [Fintype B] [Fintype I]
    (p : PMF B) (g : B → EuclideanSpace ℝ I)
    (h_support : ∀ b, p b ≠ 0 ∨ g b = 0) :
    selectedGradientMSE p g =
      (∑ b, ‖g b‖ ^ 2 / (p b).toReal) - ‖∑ a, g a‖ ^ 2 := by
  have hmean (i : I) :
      pmfMean p (fun b => (p b).toReal⁻¹ * g b i) = (∑ a, g a) i := by
    unfold pmfMean
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : p b = 0
    · have hzero : g b = 0 := (h_support b).elim (fun hne => (hne hb).elim) (fun hzero => hzero)
      simp [hb, hzero]
    · have hbReal : (p b).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩
      field_simp
  have hmoment (i : I) :
      pmfMean p (fun b => ((p b).toReal⁻¹ * g b i) ^ 2) =
        ∑ b, (g b i) ^ 2 / (p b).toReal := by
    unfold pmfMean
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : p b = 0
    · have hzero : g b = 0 := (h_support b).elim (fun hne => (hne hb).elim) (fun hzero => hzero)
      simp [hb, hzero]
    · have hbReal : (p b).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩
      field_simp
  have hcomponent (i : I) :
      pmfMean p (fun b => ((p b).toReal⁻¹ * g b i - (∑ a, g a) i) ^ 2) =
        (∑ b, (g b i) ^ 2 / (p b).toReal) - ((∑ a, g a) i) ^ 2 := by
    rw [pmfMean_sq_sub, hmean, hmoment]
    ring
  unfold selectedGradientMSE
  rw [selectedGradientMSE_trace p g (∑ a, g a)]
  simp_rw [hcomponent]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  · calc
      (∑ b, ∑ i, (g b i) ^ 2 / (p b).toReal) =
          ∑ b, (∑ i, (g b i) ^ 2) / (p b).toReal := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.sum_div]
      _ = ∑ b, ‖g b‖ ^ 2 / (p b).toReal := by
        apply Finset.sum_congr rfl
        intro b _
        rw [EuclideanSpace.real_norm_sq_eq]
  · rw [EuclideanSpace.real_norm_sq_eq]

/-- Exact MSE attained by norm-proportional selected-gradient sampling. -/
private theorem selectedGradientMSE_optimalPropensity_value {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) :
    selectedGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)) g =
      (∑ b, ‖g b‖) ^ 2 - ‖∑ a, g a‖ ^ 2 := by
  have h_support : ∀ b,
      selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL) b ≠ 0 ∨ g b = 0 := by
    simpa only [abs_norm, norm_eq_zero] using
      selectedLoss_optimalPropensity_support (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)
  rw [selectedGradientMSE_eq_sum _ _ h_support]
  have hsecond : ∑ b, ‖g b‖ ^ 2 /
      (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL) b).toReal =
        ∑ b, ‖g b‖ * ∑ a, ‖g a‖ := by
    apply Finset.sum_congr rfl
    intro b _
    rw [selectedLoss_optimalPropensity_apply]
    simp only [abs_norm]
    by_cases hzero : g b = 0
    · simp [hzero]
    · field_simp [norm_eq_zero, hL.ne', hzero]
  rw [hsecond, ← Finset.sum_mul]
  ring

/-- The norm-proportional proposal minimizes selected-gradient MSE among
all target-wise supported finite PMFs. -/
theorem selectedGradientMSE_optimalPropensity_le {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) (q : PMF B)
    (h_support : ∀ b, q b ≠ 0 ∨ g b = 0) :
    selectedGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)) g ≤
      selectedGradientMSE q g := by
  have scalar_support : ∀ b, q b ≠ 0 ∨ ‖g b‖ = 0 := by
    simpa only [norm_eq_zero] using h_support
  rw [selectedGradientMSE_optimalPropensity_value g hL,
    selectedGradientMSE_eq_sum q g h_support]
  have scalar_le := selectedLoss_optimalPropensity_mse_le
    (fun b => ‖g b‖) (by simpa only [abs_norm] using hL) q scalar_support
  simp only [selectedLoss_optimalPropensity_mse,
    selectedLossMSE_eq_sum q (fun b => ‖g b‖) scalar_support,
    abs_norm] at scalar_le
  linarith

/-- Norm-proportional selection strictly improves on normalized uniform
selection exactly when some batch gradients have different Euclidean norms. -/
theorem selectedGradientMSE_optimalPropensity_lt_uniform_iff {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) (q : PMF B)
    (h_unit : ∀ b, (q b).toReal = 1 / (Fintype.card B : ℝ)) :
    selectedGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)) g <
      selectedGradientMSE q g ↔ ¬ (∀ i j, ‖g i‖ = ‖g j‖) := by
  obtain ⟨o, _, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (f := fun b => ‖g b‖) hL.ne'
  have hcard : (0 : ℝ) < (Fintype.card B : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨o⟩)
  have support_q : ∀ b, q b ≠ 0 ∨ g b = 0 := by
    intro b
    apply Or.inl
    apply (ENNReal.toReal_ne_zero.mp ?_).1
    rw [h_unit]
    exact one_div_ne_zero hcard.ne'
  have scalar_support : ∀ b, q b ≠ 0 ∨ ‖g b‖ = 0 := by
    simpa only [norm_eq_zero] using support_q
  calc
    selectedGradientMSE
          (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL)) g <
        selectedGradientMSE q g ↔
        selectedLossMSE
          (selectedLoss_optimalPropensity (fun b => ‖g b‖)
        (by simpa only [abs_norm] using hL))
          (fun b => ‖g b‖) < selectedLossMSE q (fun b => ‖g b‖) := by
      rw [selectedGradientMSE_optimalPropensity_value g hL,
        selectedGradientMSE_eq_sum q g support_q,
        selectedLoss_optimalPropensity_mse,
        selectedLossMSE_eq_sum q (fun b => ‖g b‖) scalar_support]
      simp only [abs_norm]
      constructor <;> intro h <;> linarith
    _ ↔ ¬ (∀ i j, |‖g i‖| = |‖g j‖|) :=
      selectedLoss_optimalPropensity_mse_lt_uniform_iff
        (fun b => ‖g b‖) (by simpa only [abs_norm] using hL) q h_unit
    _ ↔ ¬ (∀ i j, ‖g i‖ = ‖g j‖) := by simp only [abs_norm]


/-- Expected squared Euclidean error of the arithmetic-mean estimator
obtained from one inverse-propensity selected batch gradient. -/
noncomputable def selectedMeanGradientMSE {B I : Type*} [Fintype B] [Fintype I]
    (p : PMF B) (g : B → EuclideanSpace ℝ I) : ℝ :=
  (Fintype.card B : ℝ)⁻¹ ^ 2 * selectedGradientMSE p g

/-- On a nonempty finite batch, the scaled sum-gradient MSE is exactly the
expected squared error for the estimator `(n*q)⁻¹ • g` and target `n⁻¹ • G`.
No support hypothesis is needed: this is algebra, including zero masses. -/
theorem selectedMeanGradientMSE_eq_sum {B I : Type*} [Fintype B] [Fintype I]
    (p : PMF B) (g : B → EuclideanSpace ℝ I)
    (h_card : 0 < Fintype.card B) :
    selectedMeanGradientMSE p g =
      pmfMean p (fun b =>
        ‖((Fintype.card B : ℝ) * (p b).toReal)⁻¹ • g b -
          (Fintype.card B : ℝ)⁻¹ • ∑ a, g a‖ ^ 2) := by
  have h_card_real : (0 : ℝ) < (Fintype.card B : ℝ) :=
    Nat.cast_pos.mpr h_card
  have h_scale (b : B) :
      ‖((Fintype.card B : ℝ) * (p b).toReal)⁻¹ • g b -
          (Fintype.card B : ℝ)⁻¹ • ∑ a, g a‖ ^ 2 =
        (Fintype.card B : ℝ)⁻¹ ^ 2 *
          ‖(p b).toReal⁻¹ • g b - ∑ a, g a‖ ^ 2 := by
    have hvector :
        ((Fintype.card B : ℝ) * (p b).toReal)⁻¹ • g b -
            (Fintype.card B : ℝ)⁻¹ • ∑ a, g a =
          (Fintype.card B : ℝ)⁻¹ •
            ((p b).toReal⁻¹ • g b - ∑ a, g a) := by
      simp only [smul_sub, smul_smul]
      rw [mul_inv_rev, mul_comm ((p b).toReal⁻¹) ((Fintype.card B : ℝ)⁻¹)]
    rw [hvector, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos h_card_real]
    ring
  unfold selectedMeanGradientMSE selectedGradientMSE
  rw [← pmfMean_const_mul]
  apply congrArg (pmfMean p)
  funext b
  exact (h_scale b).symm

/-- Norm-proportional selection minimizes arithmetic-mean selected-gradient
MSE among every target-wise supported finite competitor. -/
theorem selectedMeanGradientMSE_optimalPropensity_le {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) (q : PMF B)
    (h_support : ∀ b, q b ≠ 0 ∨ g b = 0) :
    selectedMeanGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
          (by simpa only [abs_norm] using hL)) g ≤
      selectedMeanGradientMSE q g := by
  unfold selectedMeanGradientMSE
  exact mul_le_mul_of_nonneg_left
    (selectedGradientMSE_optimalPropensity_le g hL q h_support) (sq_nonneg _)

/-- Arithmetic-mean selection strictly improves on normalized uniform
selection exactly when batch-gradient Euclidean norms are not all equal. -/
theorem selectedMeanGradientMSE_optimalPropensity_lt_uniform_iff
    {B I : Type*} [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (hL : 0 < ∑ b, ‖g b‖) (q : PMF B)
    (h_unit : ∀ b, (q b).toReal = 1 / (Fintype.card B : ℝ)) :
    selectedMeanGradientMSE
        (selectedLoss_optimalPropensity (fun b => ‖g b‖)
          (by simpa only [abs_norm] using hL)) g <
      selectedMeanGradientMSE q g ↔ ¬ (∀ i j, ‖g i‖ = ‖g j‖) := by
  obtain ⟨o, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (f := fun b => ‖g b‖) hL.ne'
  have h_card : (0 : ℝ) < (Fintype.card B : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨o⟩)
  have hfactor : (0 : ℝ) < (Fintype.card B : ℝ)⁻¹ ^ 2 :=
    sq_pos_of_pos (inv_pos_of_pos h_card)
  unfold selectedMeanGradientMSE
  constructor
  · intro h
    apply (selectedGradientMSE_optimalPropensity_lt_uniform_iff
      g hL q h_unit).mp
    exact lt_of_mul_lt_mul_left h hfactor.le
  · intro h
    exact mul_lt_mul_of_pos_left
      ((selectedGradientMSE_optimalPropensity_lt_uniform_iff
        g hL q h_unit).mpr h) hfactor


open scoped Classical BigOperators
open Real

/-- Any norm upper bound gives a nonnegative allocation weight, and a zero
weight forces the corresponding gradient to vanish.  For the induced
propensity, the selected-gradient trace is at most the squared total norm
bound minus the squared norm of the target gradient sum. -/
theorem selectedGradientMSE_upperBoundPropensity_le {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (a : B → ℝ) (hA : 0 < ∑ b, |a b|) (h_bound : ∀ b, ‖g b‖ ≤ a b) :
    selectedGradientMSE (selectedLoss_optimalPropensity a hA) g ≤
      (∑ b, |a b|) ^ 2 - ‖∑ b, g b‖ ^ 2 := by
  let p := selectedLoss_optimalPropensity a hA
  have h_zero (b : B) (hb : |a b| = 0) : g b = 0 := by
    have ha : a b = 0 := abs_eq_zero.mp hb
    have hn : ‖g b‖ ≤ 0 := by simpa only [ha] using h_bound b
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  have h_support : ∀ b, p b ≠ 0 ∨ g b = 0 := by
    intro b
    by_cases hb : |a b| = 0
    · exact Or.inr (h_zero b hb)
    · apply Or.inl
      apply (ENNReal.toReal_ne_zero.mp ?_).1
      dsimp only [p]
      rw [selectedLoss_optimalPropensity_apply]
      exact div_ne_zero hb hA.ne'
  have hpoint (b : B) :
      ‖g b‖ ^ 2 / (p b).toReal ≤ (∑ c, |a c|) * |a b| := by
    dsimp only [p]
    rw [selectedLoss_optimalPropensity_apply]
    by_cases hb : |a b| = 0
    · simp [h_zero b hb, hb]
    · have hbpos : 0 < |a b| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hb)
      have hsquare : ‖g b‖ ^ 2 ≤ |a b| ^ 2 := by
        nlinarith [norm_nonneg (g b), h_bound b, sq_abs (a b)]
      rw [div_div_eq_mul_div]
      apply (div_le_iff₀ hbpos).2
      calc
        ‖g b‖ ^ 2 * (∑ c, |a c|) ≤ |a b| ^ 2 * (∑ c, |a c|) :=
          mul_le_mul_of_nonneg_right hsquare hA.le
        _ = (∑ c, |a c|) * |a b| * |a b| := by ring
  have hsum : (∑ b, ‖g b‖ ^ 2 / (p b).toReal) ≤ (∑ b, |a b|) ^ 2 := by
    calc
      (∑ b, ‖g b‖ ^ 2 / (p b).toReal) ≤ ∑ b, (∑ c, |a c|) * |a b| :=
        Finset.sum_le_sum (fun b _ => hpoint b)
      _ = (∑ c, |a c|) * ∑ b, |a b| := (Finset.mul_sum _ _ _).symm
      _ = (∑ b, |a b|) ^ 2 := by ring
  change selectedGradientMSE p g ≤ (∑ b, |a b|) ^ 2 - ‖∑ b, g b‖ ^ 2
  rw [selectedGradientMSE_eq_sum p g h_support]
  exact sub_le_sub_right hsum _

/-- The arithmetic-mean error inherits the propensity upper bound with the
exact squared inverse-cardinality scaling, without a separate
cardinal-positivity premise. -/
theorem selectedMeanGradientMSE_upperBoundPropensity_le {B I : Type*}
    [Fintype B] [Fintype I] (g : B → EuclideanSpace ℝ I)
    (a : B → ℝ) (hA : 0 < ∑ b, |a b|) (h_bound : ∀ b, ‖g b‖ ≤ a b) :
    selectedMeanGradientMSE (selectedLoss_optimalPropensity a hA) g ≤
      (Fintype.card B : ℝ)⁻¹ ^ 2 *
        ((∑ b, |a b|) ^ 2 - ‖∑ b, g b‖ ^ 2) := by
  unfold selectedMeanGradientMSE
  exact mul_le_mul_of_nonneg_left
    (selectedGradientMSE_upperBoundPropensity_le g a hA h_bound) (sq_nonneg _)


end Hagi.Probability

export Hagi.Probability (mwu_potential_step)
