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
import Hagi.Probability.MirrorHedgeMWU

set_option linter.style.header false

/-!
# MirrorHedgeMWUSelectedLoss

Selected-loss семейство: inverse-propensity выбранные потери, selectedLossMSE, оптимальная propensity и характеризация нуля MSE.
Split from `MirrorHedge` (C259).
-/

namespace Hagi.Probability

open Finset Real

open Classical in
/-- The selected inverse-weighted loss collapses to the fixed target loss by
finite-sum cancellation. This finite-sum identity uses no normalization,
nonnegativity or nonempty hypothesis. -/
theorem selectedLoss_sum_real {V : Type*} [Fintype V]
    (p ℓ : V → ℝ) (b : V) (hb : p b ≠ 0) :
    ∑ a, p a * (if a = b then ℓ a / p a else 0) = ℓ b := by
  classical
  simp_rw [mul_ite, mul_zero]
  rw [Fintype.sum_ite_eq' b]
  exact mul_div_cancel₀ (ℓ b) hb

open Classical in
/-- Under a PMF, observing only a selected action's loss with inverse
propensity yields exactly its expectation for each fixed arm with positive
selection probability.  This is not a variance or learning-regret claim. -/
theorem pmfMean_selectedLoss {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (b : V) (hb : p b ≠ 0) :
    pmfMean p (fun a => if a = b then ℓ a / (p a).toReal else 0) = ℓ b := by
  have hbReal : (p b).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩
  exact selectedLoss_sum_real (fun a => (p a).toReal) ℓ b hbReal


open scoped Classical in
/-- If a target loss is zero, its selected inverse-weighted estimator is zero
even when that target has zero propensity. Otherwise nonzero propensity
suffices: zero-loss arms need not be observed. -/
theorem selectedLoss_sum_real_support {V : Type*} [Fintype V]
    (p ℓ : V → ℝ) (b : V) (hb : p b ≠ 0 ∨ ℓ b = 0) :
    ∑ a, p a * (if a = b then ℓ a / p a else 0) = ℓ b := by
  classical
  rcases hb with hb | hzero
  · exact selectedLoss_sum_real p ℓ b hb
  · simp_rw [mul_ite, mul_zero]
    rw [Fintype.sum_ite_eq' b]
    simp [hzero]

open scoped Classical in
/-- Finite-PMF unbiasedness only needs the propensity required to recover
that fixed target. A zero target can have zero selection probability. -/
theorem pmfMean_selectedLoss_support {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (b : V) (hb : p b ≠ 0 ∨ ℓ b = 0) :
    pmfMean p (fun a => if a = b then ℓ a / (p a).toReal else 0) = ℓ b := by
  exact selectedLoss_sum_real_support (fun a => (p a).toReal) ℓ b
    (hb.imp (fun hb => ENNReal.toReal_ne_zero.mpr ⟨hb, p.apply_ne_top b⟩)
      (fun hzero => hzero))

open scoped Classical in
/-- Exact finite variance of one selected inverse-propensity observation.
At zero target loss, both sides are zero even at zero propensity. This is
not a variance upper bound or a claim of reduced computational cost. -/
theorem pmfMean_selectedLoss_variance {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (b : V) (hb : p b ≠ 0 ∨ ℓ b = 0) :
    pmfMean p (fun a => (if a = b then ℓ a / (p a).toReal else 0) ^ 2)
      - (pmfMean p (fun a => if a = b then ℓ a / (p a).toReal else 0)) ^ 2
      = (ℓ b) ^ 2 * (1 / (p b).toReal - 1) := by
  have hmean :
      pmfMean p (fun a =>
        if a = b then ℓ a / (p a).toReal else 0) = ℓ b :=
    pmfMean_selectedLoss_support p ℓ b hb
  rw [hmean]
  by_cases hpb : p b = 0
  · have hzeroLoss : ℓ b = 0 :=
      hb.elim (fun hne => (hne hpb).elim) (fun hzero => hzero)
    have hzero : ∀ a,
        (if a = b then ℓ a / (p a).toReal else 0) = 0 := by
      intro a
      split_ifs with ha
      · subst a
        simp [hzeroLoss]
      · rfl
    simp [pmfMean, hzero, hzeroLoss]
  · have hpbReal : (p b).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hpb, p.apply_ne_top b⟩
    have hmoment :
        pmfMean p (fun a =>
          (if a = b then ℓ a / (p a).toReal else 0) ^ 2)
          = (ℓ b) ^ 2 / (p b).toReal := by
      calc
        pmfMean p (fun a =>
            (if a = b then ℓ a / (p a).toReal else 0) ^ 2)
            = ∑ a, if a = b then
                (p a).toReal * (ℓ a / (p a).toReal) ^ 2 else 0 := by
          simp only [pmfMean]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp [div_pow]
        _ = (p b).toReal * (ℓ b / (p b).toReal) ^ 2 := by
          rw [Fintype.sum_ite_eq' b]
        _ = (ℓ b) ^ 2 / (p b).toReal := by
          rw [div_pow]
          field_simp [hpbReal]
    rw [hmoment]
    ring


open scoped Classical

/-- One selected observation's expected sum of coordinate-wise squared
errors for a fixed finite loss vector. PmfMean is linear, so this also
expresses its expected Euclidean squared error; no independence claim. -/
noncomputable def selectedLossMSE {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) : ℝ :=
  ∑ b, pmfMean p (fun a =>
    ((if a = b then ℓ a / (p a).toReal else 0) - ℓ b) ^ 2)

/-- Loss-magnitude-proportional propensity. The positive normalizer
ensures a genuine PMF, including zero propensity for zero losses.
This normalized construction is for one fixed finite loss vector. -/
noncomputable def selectedLoss_optimalPropensity {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|) : PMF V := by
  let q : V → ℝ := fun i => |ℓ i| / ∑ a, |ℓ a|
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    exact div_nonneg (abs_nonneg (ℓ i)) hL.le
  have hq_sum : ∑ i, q i = 1 := by
    dsimp [q]
    calc
      (∑ i, |ℓ i| / ∑ a, |ℓ a|) = (∑ i, |ℓ i|) / ∑ a, |ℓ a| :=
        (Finset.sum_div _ _ _).symm
      _ = 1 := div_self hL.ne'
  refine PMF.ofFintype (fun i => ENNReal.ofReal (q i)) ?_
  calc
    ∑ i, ENNReal.ofReal (q i) = ENNReal.ofReal (∑ i, q i) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => hq_nonneg i)).symm
    _ = 1 := by rw [hq_sum, ENNReal.ofReal_one]

@[simp] theorem selectedLoss_optimalPropensity_apply {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|) (b : V) :
    (selectedLoss_optimalPropensity ℓ hL b).toReal =
      |ℓ b| / ∑ i, |ℓ i| := by
  change (ENNReal.ofReal (|ℓ b| / ∑ i, |ℓ i|)).toReal =
    |ℓ b| / ∑ i, |ℓ i|
  exact ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (ℓ b)) hL.le)

/-- Exact objective under target-wise support. The formula identifies
sum-of-coordinate-error MSE with the trace of marginal variances;
there is no covariance-independence or scalar-total-variance claim. -/
theorem selectedLossMSE_eq_sum {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ)
    (h_support : ∀ b, p b ≠ 0 ∨ ℓ b = 0) :
    selectedLossMSE p ℓ =
      (∑ b, (ℓ b) ^ 2 / (p b).toReal) - ∑ b, (ℓ b) ^ 2 := by
  unfold selectedLossMSE
  calc
    ∑ b, pmfMean p (fun a =>
        ((if a = b then ℓ a / (p a).toReal else 0) - ℓ b) ^ 2)
        = ∑ b, (ℓ b) ^ 2 * (1 / (p b).toReal - 1) := by
      apply Finset.sum_congr rfl
      intro b _
      have hmean := pmfMean_selectedLoss_support p ℓ b (h_support b)
      have hvar := pmfMean_selectedLoss_variance p ℓ b (h_support b)
      rw [pmfMean_sq_sub, hmean]
      rw [hmean] at hvar
      linarith
    _ = (∑ b, (ℓ b) ^ 2 / (p b).toReal) - ∑ b, (ℓ b) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Exact MSE attained by loss-magnitude-proportional propensity.
Zero losses may have zero mass without losing unbiasedness. -/
theorem selectedLoss_optimalPropensity_mse {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|) :
    selectedLossMSE (selectedLoss_optimalPropensity ℓ hL) ℓ =
      (∑ i, |ℓ i|) ^ 2 - ∑ i, (ℓ i) ^ 2 := by
  have h_support : ∀ b,
      selectedLoss_optimalPropensity ℓ hL b ≠ 0 ∨ ℓ b = 0 := by
    intro b
    by_cases hzero : ℓ b = 0
    · exact Or.inr hzero
    · apply Or.inl
      have hne : (selectedLoss_optimalPropensity ℓ hL b).toReal ≠ 0 := by
        rw [selectedLoss_optimalPropensity_apply]
        exact div_ne_zero (abs_ne_zero.mpr hzero) hL.ne'
      exact (ENNReal.toReal_ne_zero.mp hne).1
  rw [selectedLossMSE_eq_sum _ _ h_support]
  have hsecond : ∑ b,
      (ℓ b) ^ 2 / (selectedLoss_optimalPropensity ℓ hL b).toReal =
        ∑ b, |ℓ b| * ∑ i, |ℓ i| := by
    apply Finset.sum_congr rfl
    intro b _
    rw [selectedLoss_optimalPropensity_apply]
    by_cases hzero : ℓ b = 0
    · simp [hzero]
    · rw [← sq_abs]
      field_simp [abs_ne_zero.mpr hzero, hL.ne']
  rw [hsecond, ← Finset.sum_mul]
  ring

/-- Global finite MSE optimum among supported PMFs, proved using
zero-safe finite Cauchy-Schwarz, not stationary-point optimality. -/
theorem selectedLoss_optimalPropensity_mse_le {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|)
    (q : PMF V) (h_support : ∀ b, q b ≠ 0 ∨ ℓ b = 0) :
    selectedLossMSE (selectedLoss_optimalPropensity ℓ hL) ℓ ≤
      selectedLossMSE q ℓ := by
  have hCS : (∑ i, |ℓ i|) ^ 2 ≤
      (∑ i, (ℓ i) ^ 2 / (q i).toReal) * ∑ i, (q i).toReal := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _
      exact div_nonneg (sq_nonneg (ℓ i)) ENNReal.toReal_nonneg
    · intro i _
      exact ENNReal.toReal_nonneg
    · intro i _
      by_cases hzero : (q i).toReal = 0
      · have hqi : q i = 0 := by
          have hz : q i = 0 ∨ q i = ⊤ :=
            (ENNReal.toReal_eq_zero_iff (q i)).mp hzero
          exact hz.resolve_right (q.apply_ne_top i)
        have hloss : ℓ i = 0 := (h_support i).elim
          (fun hne => (hne hqi).elim) (fun hzero => hzero)
        simp [hzero, hloss]
      · rw [sq_abs]
        exact le_of_eq (div_mul_cancel₀ ((ℓ i) ^ 2) hzero).symm
  have hbound : (∑ i, |ℓ i|) ^ 2 ≤
      ∑ i, (ℓ i) ^ 2 / (q i).toReal := by
    simpa only [pmf_weight_sum q, mul_one] using hCS
  rw [selectedLoss_optimalPropensity_mse,
    selectedLossMSE_eq_sum q ℓ h_support]
  linarith


open scoped Classical

/-- Selected-coordinate MSE is a sum of expectations of nonnegative
squared errors, so it is nonnegative for every finite PMF and loss. -/
theorem selectedLossMSE_nonneg {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) : 0 ≤ selectedLossMSE p ℓ := by
  unfold selectedLossMSE
  apply Finset.sum_nonneg
  intro b _
  apply pmfMean_nonneg
  intro a _
  exact sq_nonneg _

/-- Zero total absolute loss means every fixed loss is zero. There is
no normalization need and no nonzero selected coordinate can occur. -/
theorem selectedLossMSE_eq_zero_of_abs_sum_eq_zero {V : Type*} [Fintype V]
    (p : PMF V) (ℓ : V → ℝ) (hL : ∑ i, |ℓ i| = 0) :
    selectedLossMSE p ℓ = 0 := by
  have hzero (b : V) : ℓ b = 0 := by
    have habs : |ℓ b| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => abs_nonneg (ℓ i))).mp hL b (Finset.mem_univ b)
    exact abs_eq_zero.mp habs
  simp [selectedLossMSE, hzero]

/-- In the zero-normalizer branch, every supplied PMF has zero MSE and
is therefore a minimizer. This explicitly avoids a uniqueness claim. -/
theorem selectedLossMSE_le_of_abs_sum_eq_zero {V : Type*} [Fintype V]
    (p q : PMF V) (ℓ : V → ℝ)
    (hL : ∑ i, |ℓ i| = 0) :
    selectedLossMSE p ℓ ≤ selectedLossMSE q ℓ := by
  rw [selectedLossMSE_eq_zero_of_abs_sum_eq_zero p ℓ hL]
  exact selectedLossMSE_nonneg q ℓ

/-- With positive total loss magnitude, the loss-proportional PMF is the
unique supported least-MSE proposal. The proof recovers the constant
nonzero-weight ratios using strict Jensen, with zero-weight losses
handled by the given support rather than an all-positive-assumption. -/
theorem selectedLoss_optimalPropensity_eq_of_mse_eq {V : Type*} [Fintype V]
    (ℓ : V → ℝ) (hL : 0 < ∑ i, |ℓ i|)
    (q : PMF V) (h_support : ∀ b, q b ≠ 0 ∨ ℓ b = 0)
    (h_mse : selectedLossMSE (selectedLoss_optimalPropensity ℓ hL) ℓ =
      selectedLossMSE q ℓ) :
    selectedLoss_optimalPropensity ℓ hL = q := by
  have hmul (i : V) :
      (q i).toReal * (|ℓ i| / (q i).toReal) = |ℓ i| := by
    by_cases hzero : (q i).toReal = 0
    · have hqi : q i = 0 :=
        ((ENNReal.toReal_eq_zero_iff (q i)).mp hzero).resolve_right
          (q.apply_ne_top i)
      have hloss : ℓ i = 0 := (h_support i).elim
        (fun hne => (hne hqi).elim) (fun hz => hz)
      simp [hzero, hloss]
    · calc
        (q i).toReal * (|ℓ i| / (q i).toReal) =
            |ℓ i| / (q i).toReal * (q i).toReal := mul_comm _ _
        _ = |ℓ i| := div_mul_cancel₀ _ hzero
  have hsq (i : V) :
      (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 =
        (ℓ i) ^ 2 / (q i).toReal := by
    by_cases hzero : (q i).toReal = 0
    · have hqi : q i = 0 :=
        ((ENNReal.toReal_eq_zero_iff (q i)).mp hzero).resolve_right
          (q.apply_ne_top i)
      have hloss : ℓ i = 0 := (h_support i).elim
        (fun hne => (hne hqi).elim) (fun hz => hz)
      simp [hzero, hloss]
    · calc
        (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 =
            ((q i).toReal * (|ℓ i| / (q i).toReal)) *
              (|ℓ i| / (q i).toReal) := by ring
        _ = |ℓ i| * (|ℓ i| / (q i).toReal) := by rw [hmul i]
        _ = |ℓ i| ^ 2 / (q i).toReal := by ring
        _ = (ℓ i) ^ 2 / (q i).toReal := by rw [sq_abs]
  have hmean : ∑ i, (q i).toReal * (|ℓ i| / (q i).toReal) =
      ∑ i, |ℓ i| := by
    apply Finset.sum_congr rfl
    intro i _
    exact hmul i
  have hsecond : ∑ i, (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 =
      ∑ i, (ℓ i) ^ 2 / (q i).toReal := by
    apply Finset.sum_congr rfl
    intro i _
    exact hsq i
  rw [selectedLoss_optimalPropensity_mse] at h_mse
  have hobjective := selectedLossMSE_eq_sum q ℓ h_support
  have hvalue : (∑ i, (ℓ i) ^ 2 / (q i).toReal) =
      (∑ i, |ℓ i|) ^ 2 := by
    linarith
  have hjensen := (strictConvexOn_pow (n := 2) (by norm_num)).map_sum_eq_iff'
    (t := Finset.univ)
    (w := fun i => (q i).toReal)
    (p := fun i => |ℓ i| / (q i).toReal)
    (fun i _ => ENNReal.toReal_nonneg)
    (pmf_weight_sum q)
    (fun i _ => div_nonneg (abs_nonneg (ℓ i)) ENNReal.toReal_nonneg)
  have hw_eq : ∀ b, (q b).toReal ≠ 0 →
      |ℓ b| / (q b).toReal = ∑ i, |ℓ i| := by
    have hsquare : (∑ i, (q i).toReal * (|ℓ i| / (q i).toReal)) ^ 2 =
        ∑ i, (q i).toReal * (|ℓ i| / (q i).toReal) ^ 2 := by
      rw [hmean, hsecond, hvalue]
    have hj := hjensen.mp hsquare
    intro b hb
    have hb_eq := hj b (Finset.mem_univ b) hb
    simpa only [smul_eq_mul, hmean] using hb_eq
  apply PMF.ext
  intro b
  apply (ENNReal.toReal_eq_toReal_iff'
    ((selectedLoss_optimalPropensity ℓ hL).apply_ne_top b)
    (q.apply_ne_top b)).mp
  rw [selectedLoss_optimalPropensity_apply]
  by_cases hzero : (q b).toReal = 0
  · have hqi : q b = 0 :=
      ((ENNReal.toReal_eq_zero_iff (q b)).mp hzero).resolve_right
        (q.apply_ne_top b)
    have hloss : ℓ b = 0 := (h_support b).elim
      (fun hne => (hne hqi).elim) (fun hz => hz)
    simp [hzero, hloss]
  · apply (div_eq_iff hL.ne').mpr
    calc
      |ℓ b| = (∑ i, |ℓ i|) * (q b).toReal :=
        (div_eq_iff hzero).mp (hw_eq b hzero)
      _ = (q b).toReal * ∑ i, |ℓ i| := mul_comm _ _

/-- Positive-normalizer optimal propensity supports every nonzero target
coordinate. Zero propensity forces that coordinate's target loss to vanish. -/
theorem selectedLoss_optimalPropensity_support {V : Type*} [Fintype V]
    (ell : V → ℝ) (hL : 0 < ∑ i, |ell i|) :
    ∀ b, selectedLoss_optimalPropensity ell hL b ≠ 0 ∨ ell b = 0 := by
  intro b
  by_cases hzero : ell b = 0
  · exact Or.inr hzero
  · apply Or.inl
    have hne : (selectedLoss_optimalPropensity ell hL b).toReal ≠ 0 := by
      rw [selectedLoss_optimalPropensity_apply]
      exact div_ne_zero (abs_ne_zero.mpr hzero) hL.ne'
    exact (ENNReal.toReal_ne_zero.mp hne).1

/-- For positive total absolute loss, the optimal supported estimator has
zero MSE exactly when its propensity is a singleton mass. This finite trace
criterion does not assert determinism of real-valued losses generally, nor
that the losses used to construct the normalized distribution are cheap. -/
theorem selectedLoss_optimalPropensity_mse_eq_zero_iff_apply_eq_one
    {V : Type*} [Fintype V] (ell : V → ℝ) (hL : 0 < ∑ i, |ell i|) :
    selectedLossMSE (selectedLoss_optimalPropensity ell hL) ell = 0 ↔
      ∃ b, selectedLoss_optimalPropensity ell hL b = 1 := by
  classical
  let q : V → ℝ := fun b =>
    (selectedLoss_optimalPropensity ell hL b).toReal
  have hq_apply (b : V) : q b = |ell b| / ∑ i, |ell i| := by
    dsimp [q]
    rw [selectedLoss_optimalPropensity_apply]
  have hq_nonneg (b : V) : 0 ≤ q b := ENNReal.toReal_nonneg
  have hq_sum : ∑ b, q b = 1 := by
    simpa only [q] using pmf_weight_sum (selectedLoss_optimalPropensity ell hL)
  have hq_le_one (b : V) : q b ≤ 1 := by
    calc
      q b ≤ ∑ a, q a := Finset.single_le_sum
        (fun a _ => hq_nonneg a) (Finset.mem_univ b)
      _ = 1 := hq_sum
  have hmul (b : V) : q b * (∑ i, |ell i|) = |ell b| := by
    rw [hq_apply]
    exact div_mul_cancel₀ _ hL.ne'
  have hsq (b : V) :
      (ell b) ^ 2 = (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by
    calc
      (ell b) ^ 2 = |ell b| ^ 2 := (sq_abs _).symm
      _ = (q b * (∑ i, |ell i|)) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) (hmul b).symm
      _ = (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by ring
  have hsquares : ∑ b, (ell b) ^ 2 =
      ∑ b, (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by
    exact Finset.sum_congr rfl (fun b _ => hsq b)
  have hmse : selectedLossMSE (selectedLoss_optimalPropensity ell hL) ell =
      (∑ i, |ell i|) ^ 2 * ∑ b, q b * (1 - q b) := by
    rw [selectedLoss_optimalPropensity_mse]
    calc
      (∑ i, |ell i|) ^ 2 - ∑ b, (ell b) ^ 2 =
          (∑ i, |ell i|) ^ 2 * (∑ b, q b) -
            ∑ b, (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by
        rw [hq_sum, mul_one, hsquares]
      _ = (∑ b, (∑ i, |ell i|) ^ 2 * q b) -
            ∑ b, (∑ i, |ell i|) ^ 2 * (q b) ^ 2 := by
        rw [Finset.mul_sum]
      _ = ∑ b, ((∑ i, |ell i|) ^ 2 * q b -
            (∑ i, |ell i|) ^ 2 * (q b) ^ 2) :=
        (Finset.sum_sub_distrib _ _).symm
      _ = ∑ b, (∑ i, |ell i|) ^ 2 * (q b * (1 - q b)) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = (∑ i, |ell i|) ^ 2 * ∑ b, q b * (1 - q b) :=
        (Finset.mul_sum _ _ _).symm
  constructor
  · intro hmse_zero
    have hsum_zero : ∑ b, q b * (1 - q b) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 2 hL.ne')
      rwa [← hmse]
    have hterm_zero (b : V) : q b * (1 - q b) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
        mul_nonneg (hq_nonneg a) (sub_nonneg.mpr (hq_le_one a)))).mp
          hsum_zero b (Finset.mem_univ b)
    have hq_zero_or_one (b : V) : q b = 0 ∨ q b = 1 := by
      rcases mul_eq_zero.mp (hterm_zero b) with hb | hb
      · exact Or.inl hb
      · exact Or.inr (sub_eq_zero.mp hb).symm
    obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) (f := q) (by rw [hq_sum]; exact one_ne_zero)
    have hbq : q b = 1 := (hq_zero_or_one b).resolve_left hb
    refine ⟨b, ?_⟩
    apply (ENNReal.toReal_eq_toReal_iff'
      ((selectedLoss_optimalPropensity ell hL).apply_ne_top b)
      ENNReal.one_ne_top).mp
    change q b = (1 : ENNReal).toReal
    rw [hbq, ENNReal.toReal_one]
  · rintro ⟨b, hb⟩
    have hbq : q b = 1 := by
      change (selectedLoss_optimalPropensity ell hL b).toReal = 1
      rw [hb, ENNReal.toReal_one]
    have hothers : ∀ a, a ≠ b → q a = 0 := by
      intro a ha
      have hadd := Finset.add_sum_erase Finset.univ q (Finset.mem_univ b)
      rw [hbq, hq_sum] at hadd
      have hzero : ∑ x ∈ Finset.univ.erase b, q x = 0 := by linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => hq_nonneg x)).mp hzero a
          (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩)
    rw [hmse]
    have hzero : ∀ a, q a * (1 - q a) = 0 := by
      intro a
      by_cases ha : a = b
      · subst a
        rw [hbq]
        ring
      · rw [hothers a ha]
        ring
    rw [Finset.sum_eq_zero (fun a _ => hzero a), mul_zero]


/-- For positive total absolute loss, the optimal supported estimator
has zero MSE exactly when there is one genuinely nonzero loss
coordinate (all other coordinates are zero). -/
theorem selectedLoss_optimalPropensity_mse_eq_zero_iff_single_nonzero
    {V : Type*} [Fintype V] (ell : V → ℝ) (hL : 0 < ∑ i, |ell i|) :
    selectedLossMSE (selectedLoss_optimalPropensity ell hL) ell = 0 ↔
      ∃ b, ell b ≠ 0 ∧ ∀ a, a ≠ b → ell a = 0 := by
  classical
  rw [selectedLoss_optimalPropensity_mse_eq_zero_iff_apply_eq_one]
  constructor
  · rintro ⟨b, hb⟩
    have hbne : ell b ≠ 0 := by
      intro hzero
      have hbreal : (selectedLoss_optimalPropensity ell hL b).toReal = 1 :=
        (ENNReal.toReal_eq_one_iff _).mpr hb
      rw [selectedLoss_optimalPropensity_apply, hzero, abs_zero, zero_div] at hbreal
      exact zero_ne_one hbreal
    refine ⟨b, hbne, ?_⟩
    intro a ha
    have hnot : a ∉ (selectedLoss_optimalPropensity ell hL).support := by
      rw [((selectedLoss_optimalPropensity ell hL).apply_eq_one_iff b).mp hb]
      simp [ha]
    have ha0 : selectedLoss_optimalPropensity ell hL a = 0 :=
      ((selectedLoss_optimalPropensity ell hL).apply_eq_zero_iff a).mpr hnot
    have hareal : (selectedLoss_optimalPropensity ell hL a).toReal = 0 := by
      rw [ha0, ENNReal.toReal_zero]
    rw [selectedLoss_optimalPropensity_apply] at hareal
    exact abs_eq_zero.mp ((div_eq_zero_iff.mp hareal).resolve_right (ne_of_gt hL))
  · rintro ⟨b, hb, hothers⟩
    refine ⟨b, ?_⟩
    apply (ENNReal.toReal_eq_one_iff _).mp
    have hsum : ∑ i, |ell i| = |ell b| := by
      apply Fintype.sum_eq_single b
      intro a ha
      rw [hothers a ha, abs_zero]
    rw [selectedLoss_optimalPropensity_apply, hsum]
    exact div_self (abs_ne_zero.mpr hb)


/-- For positive total absolute loss, the optimal supported estimator
strictly beats a normalized uniform reference exactly when not all loss
magnitudes are equal. -/
theorem selectedLoss_optimalPropensity_mse_lt_uniform_iff
    {V : Type*} [Fintype V] (ell : V → ℝ)
    (hL : 0 < ∑ i, |ell i|) (q : PMF V)
    (h_unit : ∀ b, (q b).toReal = 1 / (Fintype.card V : ℝ)) :
    selectedLossMSE (selectedLoss_optimalPropensity ell hL) ell <
      selectedLossMSE q ell ↔ ¬ (∀ i j, |ell i| = |ell j|) := by
  obtain ⟨o, _, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (f := fun i => |ell i|) hL.ne'
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨o⟩)
  have hq (b : V) : q b ≠ 0 := by
    apply (ENNReal.toReal_ne_zero.mp ?_).1
    rw [h_unit]
    exact one_div_ne_zero hcard.ne'
  have h_support : ∀ b, q b ≠ 0 ∨ ell b = 0 :=
    fun b => Or.inl (hq b)
  have hle := selectedLoss_optimalPropensity_mse_le ell hL q h_support
  constructor
  · intro hlt hconst
    have hL_const : (∑ i, |ell i|) =
        (Fintype.card V : ℝ) * |ell o| := by
      calc
        (∑ i, |ell i|) = ∑ _i : V, |ell o| :=
          Finset.sum_congr rfl (fun i _ => hconst i o)
        _ = (Fintype.card V : ℝ) * |ell o| := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hpq : selectedLoss_optimalPropensity ell hL = q := by
      apply PMF.ext
      intro b
      apply (ENNReal.toReal_eq_toReal_iff'
        ((selectedLoss_optimalPropensity ell hL).apply_ne_top b)
        (q.apply_ne_top b)).mp
      rw [selectedLoss_optimalPropensity_apply, h_unit,
        hconst b o, hL_const]
      field_simp [hcard.ne', ho]
    exact (ne_of_lt hlt) (congrArg (fun p => selectedLossMSE p ell) hpq)
  · intro hnot
    apply lt_of_le_of_ne hle
    intro heq
    apply hnot
    have hpq := selectedLoss_optimalPropensity_eq_of_mse_eq
      ell hL q h_support heq
    have hnorm (i : V) : |ell i| / (∑ j, |ell j|) =
        1 / (Fintype.card V : ℝ) := by
      rw [← selectedLoss_optimalPropensity_apply ell hL i, hpq, h_unit]
    intro i j
    apply mul_right_cancel₀ hL.ne'
    exact (div_eq_div_iff hL.ne' hL.ne').mp
      ((hnorm i).trans (hnorm j).symm)



end Hagi.Probability
