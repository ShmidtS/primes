/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEHeldout

/-!
# Raw cross-entropy confidence and sample budgets

This module only rescales the fixed-codebook held-out theorem from
`Hagi.Model.CEHeldout`.  The normalized loss is raw `Hagi.ceOneHot` divided
by the strictly positive `ceBound X`; every raw conclusion below actually
contains that cross-entropy, not a renamed upper bound.  The exponential
budget calculation follows the established `sample_size_adequate` pattern,
using the real identities `Finset.mul_sum`, `Real.exp_le_exp`,
`Real.exp_neg`, and `Real.exp_log` rather than another concentration proof.

The probability is for fresh independent finite categorical labels at fixed
features and a fixed decoded family.  The sufficient sample condition is not
an optimality, deployment, training, or external-data representativeness
claim.
-/

set_option relaxedAutoImplicit false
set_option linter.style.openClassical false

open Finset Real

namespace Hagi.Model.CEConfidenceScale

open scoped Matrix
open Hagi.Model Hagi.Runtime
open Hagi.Probability Hagi.Probability.FiniteFamilyConfidence
open Hagi.Model.CEHeldout

/-- Population means commute with multiplication by an arbitrary real
constant.  No probability or nonzero-sample assumption is needed for this
algebraic identity. -/
alias populationMean_const_mul :=
  _root_.Hagi.Probability.FiniteFamilyConfidence.populationMean_const_mul

/-- Empirical means commute with multiplication by an arbitrary real
constant, including when the finite sample is empty. -/
alias empiricalMean_const_mul :=
  _root_.Hagi.Probability.FiniteFamilyConfidence.empiricalMean_const_mul

/-- A normalized mean comparison implies the corresponding comparison for
any genuine pointwise positive rescaling.  The raw loss is an explicit
argument, so the premise cannot silently substitute another loss. -/
alias populationMean_le_empiricalMean_of_scale :=
  _root_.Hagi.Probability.FiniteFamilyConfidence.populationMean_le_empiricalMean_of_scale

/-- The CE normalizer is nonzero, by its proved strict positivity. -/
theorem ceBound_ne {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) : ceBound X ≠ 0 :=
  ne_of_gt (ceBound_pos X)

/-- Multiplying actual normalized joint CE by its positive bound recovers
exactly the original `Hagi.ceOneHot` loss. -/
theorem ceBound_mul_joint_normalizedCE {G : ℕ} {V : Type}
    [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → DyadicScaleCode) (t : V) :
    ceBound X *
        (Hagi.ceOneHot t
          (ceLogits X (CEGroupedScale.jointParameters e w scales)) / ceBound X) =
      Hagi.ceOneHot t
        (ceLogits X (CEGroupedScale.jointParameters e w scales)) :=
  mul_div_cancel₀ _ (ceBound_ne X)

/-- Raw joint CE confidence at a supplied normalized margin.  The
`∀ scales` event is obtained from `joint_upper_confidence` by positive
rescaling and `prodPq_mono`; the union penalty `61965 ^ G` is unchanged. -/
theorem joint_raw_upper_confidence {G n : ℕ} {V : Type}
    [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    1 - (61965 ^ G : ℕ) * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      prodPq p (fun ω => ∀ scales : Fin G → DyadicScaleCode,
        populationMean p (fun _i t =>
          Hagi.ceOneHot t
            (ceLogits X (CEGroupedScale.jointParameters e w scales))) ≤
          empiricalMean (fun _i t =>
            Hagi.ceOneHot t
              (ceLogits X (CEGroupedScale.jointParameters e w scales))) ω +
            ceBound X * eps) := by
  classical
  refine le_trans (CEHeldout.joint_upper_confidence e X w p hp hn eps heps) ?_
  apply prodPq_mono p hp
  intro ω hω scales
  exact populationMean_le_empiricalMean_of_scale p
    (fun _i t =>
      Hagi.ceOneHot t
        (ceLogits X (CEGroupedScale.jointParameters e w scales)) / ceBound X)
    (fun _i t =>
      Hagi.ceOneHot t
        (ceLogits X (CEGroupedScale.jointParameters e w scales)))
    ω (ceBound X) eps (ceBound_pos X)
    (fun _i t => ceBound_mul_joint_normalizedCE e X w scales t) (hω scales)

/-- Exact conversion between normalized and raw sample budgets.  Here `N`
is retained inside the logarithm; no union factor is replaced by one. -/
theorem sample_budget_normalized_eq_raw (N delta B eps : ℝ)
    (hB : B ≠ 0) (heps : eps ≠ 0) :
    Real.log (N / delta) / (2 * (eps / B) ^ 2) =
      B ^ 2 * Real.log (N / delta) / (2 * eps ^ 2) := by
  field_simp

/-- The sufficient normalized sample budget implies the full union-factor
exponential bound.  This is the `sample_size_adequate` argument with an
arbitrary positive `N`, including the actual `61965 ^ G`. -/
theorem mul_exp_neg_sq_le_of_sample_budget {n : ℕ} (N delta eps : ℝ)
    (hN : 0 < N) (hdelta : 0 < delta) (heps : 0 < eps)
    (hbudget : Real.log (N / delta) / (2 * eps ^ 2) ≤ (n : ℝ)) :
    N * Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤ delta := by
  have hratio : 0 < N / delta := div_pos hN hdelta
  have hden : 0 < (2 : ℝ) * eps ^ 2 := by positivity
  have hlog : Real.log (N / delta) ≤ 2 * (n : ℝ) * eps ^ 2 := by
    have h := (div_le_iff₀ hden).mp hbudget
    calc
      Real.log (N / delta) ≤ (n : ℝ) * (2 * eps ^ 2) := h
      _ = 2 * (n : ℝ) * eps ^ 2 := by ring
  have hanti : Real.exp (-2 * (n : ℝ) * eps ^ 2) ≤
      Real.exp (-Real.log (N / delta)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexp : Real.exp (-Real.log (N / delta)) = delta / N := by
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp
  rw [hexp] at hanti
  have hmul := mul_le_mul_of_nonneg_left hanti hN.le
  have hcancel : N * (delta / N) = delta := by field_simp
  rw [hcancel] at hmul
  exact hmul

/-- Delta-oriented raw joint CE confidence.  A raw margin `eps` corresponds
exactly to normalized margin `eps / ceBound X`, and the stated raw budget
is exactly the normalized budget at that margin. -/
theorem joint_raw_upper_confidence_delta {G n : ℕ} {V : Type}
    [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hbudget : (ceBound X) ^ 2 *
        Real.log ((61965 ^ G : ℕ) / delta) / (2 * eps ^ 2) ≤ (n : ℝ)) :
    1 - delta ≤
      prodPq p (fun ω => ∀ scales : Fin G → DyadicScaleCode,
        populationMean p (fun _i t =>
          Hagi.ceOneHot t
            (ceLogits X (CEGroupedScale.jointParameters e w scales))) ≤
          empiricalMean (fun _i t =>
            Hagi.ceOneHot t
              (ceLogits X (CEGroupedScale.jointParameters e w scales))) ω + eps) := by
  classical
  have hB : 0 < ceBound X := ceBound_pos X
  have hN : 0 < ((61965 ^ G : ℕ) : ℝ) := by positivity
  have hN1Nat : 1 ≤ 61965 ^ G := by
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hN1 : (1 : ℝ) ≤ ((61965 ^ G : ℕ) : ℝ) := by exact_mod_cast hN1Nat
  have _hlog_nonneg : 0 ≤ Real.log (((61965 ^ G : ℕ) : ℝ) / delta) :=
    Real.log_nonneg ((le_div_iff₀ hdelta).mpr (by nlinarith))
  have hnormalizedBudget :
      Real.log (((61965 ^ G : ℕ) : ℝ) / delta) /
          (2 * (eps / ceBound X) ^ 2) ≤ (n : ℝ) := by
    rw [sample_budget_normalized_eq_raw _ _ _ _
      (ceBound_ne X) (ne_of_gt heps)]
    exact hbudget
  have hexp : ((61965 ^ G : ℕ) : ℝ) *
      Real.exp (-2 * (n : ℝ) * (eps / ceBound X) ^ 2) ≤ delta :=
    mul_exp_neg_sq_le_of_sample_budget _ _ _ hN hdelta
      (div_pos heps hB) hnormalizedBudget
  have hconfidence := CEHeldout.joint_upper_confidence e X w p hp hn
    (eps / ceBound X) (div_pos heps hB)
  refine le_trans (le_trans (sub_le_sub_left hexp 1) hconfidence) ?_
  apply prodPq_mono p hp
  intro ω hω scales
  have h := populationMean_le_empiricalMean_of_scale p
    (fun _i t =>
      Hagi.ceOneHot t
        (ceLogits X (CEGroupedScale.jointParameters e w scales)) / ceBound X)
    (fun _i t =>
      Hagi.ceOneHot t
        (ceLogits X (CEGroupedScale.jointParameters e w scales)))
    ω (ceBound X) (eps / ceBound X) hB
    (fun _i t => ceBound_mul_joint_normalizedCE e X w scales t) (hω scales)
  simpa only [mul_div_cancel₀ eps (ceBound_ne X)] using h

/-! ## Numerical check on the existing nondegenerate finite product

`twoModelLoss` is the established unit-interval loss on two independent
nonconstant labels.  Scaling it by two and using raw margin `2 * (1 / 2)`
does not alter the normalized comparison.  The exact good-event mass is
`15 / 16`; in particular, this is not a proof that assigns zero mass to the
bad all-zero sample. -/

/-- Exact nondegenerate probability after numerical scale and margin
normalization by `B = 2`. -/
theorem twoModel_scaled_probability :
    prodPq twoModelP (fun ω => ∀ m,
      populationMean twoModelP (fun i v => 2 * twoModelLoss m i v) ≤
        empiricalMean (fun i v => 2 * twoModelLoss m i v) ω + 2 * (1 / 2)) =
      15 / 16 := by
  classical
  calc
    prodPq twoModelP (fun ω => ∀ m,
        populationMean twoModelP (fun i v => 2 * twoModelLoss m i v) ≤
          empiricalMean (fun i v => 2 * twoModelLoss m i v) ω + 2 * (1 / 2)) =
        prodPq twoModelP twoModelGood := by
      apply prodPq_iff
      intro ω
      unfold twoModelGood
      constructor
      · intro h m
        have hm := h m
        rw [populationMean_const_mul, empiricalMean_const_mul] at hm
        linarith
      · intro h m
        exact populationMean_le_empiricalMean_of_scale twoModelP
          (twoModelLoss m) (fun i v => 2 * twoModelLoss m i v) ω 2 (1 / 2)
          (by norm_num) (fun _i _v => rfl) (h m)
    _ = 15 / 16 := twoModelGood_probability

/-- The numerical union-bound confidence is strictly positive and is
simultaneously certified by the exact scaled-event probability. -/
theorem twoModel_scaled_confidence :
    0 < 1 - 2 * Real.exp (-1) ∧
      1 - 2 * Real.exp (-1) ≤
        prodPq twoModelP (fun ω => ∀ m,
          populationMean twoModelP (fun i v => 2 * twoModelLoss m i v) ≤
            empiricalMean (fun i v => 2 * twoModelLoss m i v) ω + 2 * (1 / 2)) := by
  constructor
  · exact twoModel_confidence_pos
  · rw [twoModel_scaled_probability]
    exact twoModel_confidence.trans_eq twoModelGood_probability

/-- Delta-oriented raw-CE lower confidence after sample-adaptive selection
inside the fixed decoded codebook.  The raw sample budget accounts for the
full factor `2 * 61965 ^ G`; the good event is exactly the parent raw-selected
event, with no further rescaling or additional union bound. -/
theorem codebook_raw_selected_population_mean_gap_lower_confidence_delta {G n : ℕ}
    {V : Type} [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (delta : ℝ) (hdelta : 0 < delta)
    (hbudget : ceBound X ^ 2 *
        Real.log ((2 * (61965 ^ G : ℕ) : ℝ) / delta) /
          (2 * eps ^ 2) ≤ (n : ℝ))
    (baseline candidate : (Fin n → V) → JointCode G) :
    1 - delta ≤
      prodPq p (fun ω =>
        empiricalMean (fun _i t =>
          Hagi.ceOneHot t (ceLogits X (decodeJoint e (baseline ω)))) ω -
        empiricalMean (fun _i t =>
          Hagi.ceOneHot t (ceLogits X (decodeJoint e (candidate ω)))) ω - 2 * eps ≤
          populationMean p (fun _i t =>
            Hagi.ceOneHot t (ceLogits X (decodeJoint e (baseline ω)))) -
          populationMean p (fun _i t =>
            Hagi.ceOneHot t (ceLogits X (decodeJoint e (candidate ω))))) := by
  have hB : 0 < ceBound X := ceBound_pos X
  have hN : 0 < (2 * (61965 ^ G : ℕ) : ℝ) := by positivity
  have hnormalizedBudget :
      Real.log ((2 * (61965 ^ G : ℕ) : ℝ) / delta) /
          (2 * (eps / ceBound X) ^ 2) ≤ (n : ℝ) := by
    rw [sample_budget_normalized_eq_raw _ _ _ _
      (ceBound_ne X) (ne_of_gt heps)]
    exact hbudget
  have hexp : (2 * (61965 ^ G : ℕ) : ℝ) *
      Real.exp (-2 * (n : ℝ) * (eps / ceBound X) ^ 2) ≤ delta :=
    mul_exp_neg_sq_le_of_sample_budget _ _ _ hN hdelta
      (div_pos heps hB) hnormalizedBudget
  exact le_trans (sub_le_sub_left hexp 1)
    (CEHeldout.codebook_raw_selected_population_mean_gap_lower_confidence
      e X p hp hn eps heps baseline candidate)

end Hagi.Model.CEConfidenceScale
