/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat
import Hagi.Model.CEHeldout
import Hagi.Model.CEQuantized
import Hagi.Model.CEPadding
import Hagi.Model.BatchCEDescent
import Hagi.Model.BatchCEDescentHalfEta

/-!
# Parametric softmax head core

The cross-entropy family (gated, tanh, packed, grouped/joint scale,
padding, held-out confidence, batch descent) consists of variants of one theory whose
definitional axes are the pointwise logit transform and the batch
aggregation.  This module is the migration seed: those axes become an
inductive configuration, the CE functional is defined by recursion on
it, and the common theorem classes (floor, Lipschitz estimate) are
proved once, parametric in the configuration.

The single source of truth for the CE functional stays
`Hagi.ceOneHot`; the configuration only reparametrizes its argument.
Existing statements about `Hagi.ceOneHot` are instances at
`LogitMap.ident`.  No statement of an existing module changes.

The scale/quantizer axis is deliberately not a constructor here: it
alters penalty constants, not the CE functional, and an inductive
there would force re-proving the penalty bounds per constructor.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.SoftmaxHead

/-! ## Axis (a): the pointwise logit transform -/

/-- The pointwise transform applied to raw logits before the softmax.
`ident` is the classical linear head; `tanh` is the saturating head of
the gated family. -/
inductive LogitMap where
  | ident
  | tanh
  deriving Repr

/-- `LogitMap.apply` is the recursion defining the transform; it is
the only recursion point of the configuration. -/
noncomputable def LogitMap.apply : LogitMap → ℝ → ℝ
  | .ident, x => x
  | .tanh, x => Real.tanh x

/-! ## Axis (b): the batch aggregation -/

/-- The per-example aggregation of the batch reduction: uniform
weights or an explicit weight vector. -/
inductive Reduction (ι : Type) where
  | uniform : Reduction ι
  | weighted (w : ι → ℝ) : Reduction ι

/-- `Reduction.weight` is the weight of one example, by recursion on
the reduction; the aggregation is the weighted sum. -/
def Reduction.weight : Reduction ι → ι → ℝ
  | .uniform => fun _ => 1
  | .weighted w => w

/-- The full head configuration: a logit map and a reduction. -/
structure HeadConfig (ι : Type) where
  /-- Pointwise logit transform. -/
  logitMap : LogitMap
  /-- Batch aggregation. -/
  reduction : Reduction ι

/-! ## The CE functional by recursion on the configuration -/

variable {V : Type} [Fintype V] [Nonempty V] {ι : Type} [Fintype ι]

/-- One-hot cross-entropy of the mapped logits; `Hagi.ceOneHot` is
applied to `LogitMap.apply` composed with the raw logit vector. -/
noncomputable def headCE (m : LogitMap) (t : V) (z : V → ℝ) : ℝ :=
  Hagi.ceOneHot t (fun v => m.apply (z v))

/-- Batch CE functional: the `Reduction.weight`-weighted sum of the
per-example `headCE`. -/
noncomputable def headLoss (cfg : HeadConfig ι) (t : ι → V)
    (z : ι → V → ℝ) : ℝ :=
  ∑ i, cfg.reduction.weight i * headCE cfg.logitMap (t i) (z i)

/-! ## The definitional bridge to the existing machinery -/

/-- At the identity logit map, `headCE` is literally `Hagi.ceOneHot`:
every existing CE statement is the `LogitMap.ident` instance. -/
theorem headCE_ident (t : V) (z : V → ℝ) :
    headCE .ident t z = Hagi.ceOneHot t z := rfl

/-! ## P-FLOOR: the parametric floor -/

/-- Nonnegativity of the parametric CE, for every logit map.  This is
the config-generic form of the floor statements of the held-out and
penalty families. -/
theorem headCE_nonneg (m : LogitMap) (t : V) (z : V → ℝ) :
    0 ≤ headCE m t z :=
  Hagi.Model.CEHeldout.ceOneHot_nonneg t _

/-! ## P-LIPSCHITZ: the parametric two-Lipschitz estimate -/

/-- A uniform bound on the change of the mapped logits bounds the
parametric CE by twice that bound, for every logit map.  The
`LogitMap.ident` instance is
`Hagi.Model.CEQuantized.ceOneHot_le_of_abs_sub_le`, which is used,
not restated. -/
theorem headCE_le_of_abs_sub_le (m : LogitMap) (t : V) (y z : V → ℝ)
    (r : ℝ) (h : ∀ v, |m.apply (y v) - m.apply (z v)| ≤ r) :
    headCE m t y ≤ headCE m t z + 2 * r :=
  Hagi.Model.CEQuantized.ceOneHot_le_of_abs_sub_le t _ _ r h

/-! ## Bridge demo: a variant as a one-line instantiation -/

/-- The tanh variant of the two-Lipschitz estimate, in one line from
the parametric form: what used to be a new variant file is now a
configuration plus an instantiation. -/
theorem headCE_tanh_le_of_abs_tanh_sub_le (t : V) (y z : V → ℝ)
    (r : ℝ) (h : ∀ v, |Real.tanh (y v) - Real.tanh (z v)| ≤ r) :
    headCE .tanh t y ≤ headCE .tanh t z + 2 * r :=
  headCE_le_of_abs_sub_le _ t y z r h

/-- For the tanh map the hypothesis of the Lipschitz estimate always
holds with `r = 2`, because `|tanh| < 1`; this is a genuinely new
constant bound of the saturating family. -/
theorem headCE_tanh_le_add_four (t : V) (y z : V → ℝ) :
    headCE .tanh t y ≤ headCE .tanh t z + 4 := by
  have h2 : headCE .tanh t y ≤ headCE .tanh t z + 2 * 2 := by
    refine headCE_le_of_abs_sub_le _ t y z 2 ?_
    intro v
    simp only [LogitMap.apply]
    have h1 : |Real.tanh (y v)| < 1 := Real.abs_tanh_lt_one _
    have h2' : |Real.tanh (z v)| < 1 := Real.abs_tanh_lt_one _
    have h3 : |Real.tanh (y v) - Real.tanh (z v)| ≤
        |Real.tanh (y v)| + |Real.tanh (z v)| := abs_sub _ _
    linarith
  linarith

/-! ## The reduction-agnostic floor -/

/-- The batch floor: nonnegative weights give a nonnegative
`headLoss`, for every logit map and every reduction. -/
theorem headLoss_nonneg_of_nonneg_weight
    (cfg : HeadConfig ι) (t : ι → V) (z : ι → V → ℝ)
    (hw : ∀ i, 0 ≤ cfg.reduction.weight i) :
    0 ≤ headLoss cfg t z := by
  refine Finset.sum_nonneg ?_
  intro i _hi
  exact mul_nonneg (hw i) (headCE_nonneg _ _ _)

/-- The uniform reduction carries nonnegative weights, so the batch
floor holds for it unconditionally. -/
theorem headLoss_nonneg_uniform (m : LogitMap) (t : ι → V)
    (z : ι → V → ℝ) :
    0 ≤ headLoss ⟨m, .uniform⟩ t z := by
  refine headLoss_nonneg_of_nonneg_weight _ t z ?_
  intro i
  simp [Reduction.weight]

/-!
## tranche one: the parametric range bound and ident bridges

Migration tranche one: the range-bound class
and the `LogitMap.ident` bridges for the floor, Lipschitz and padding
statements of the variant files, each derived from the parametric core
above.  The original statements in `CEHeldout`, `CEQuantized` and
`CEPadding` are unchanged and remain the frozen originals; the bridges
carry the same conclusion constants, with `headCE .ident` in place of
`Hagi.ceOneHot` (definitionally equal by `headCE_ident`).
-/

/-- P-RANGE-BOUND, parametric in the logit map: a uniform bound on the
mapped logits bounds the parametric CE by twice that bound plus the
log-cardinality, for every `LogitMap`.  Proved by one application of
the `CEHeldout` statement to the mapped logit vector. -/
theorem headCE_le_two_add_log_card (m : LogitMap) (t : V) (z : V → ℝ)
    (r : ℝ) (h : ∀ v, |m.apply (z v)| ≤ r) :
    headCE m t z ≤ 2 * r + Real.log (Fintype.card V : ℝ) :=
  Hagi.Model.CEHeldout.ceOneHot_le_two_add_log_card t _ r h

/-- Parametric instance (core): the saturating `tanh` head always
satisfies the range-bound hypothesis at `r = 1`, because
`|tanh| < 1`; this is the constant-`2` special case of the saturating
family (a NEW constant bound, not a bridge of an existing statement). -/
theorem headCE_tanh_le_two_add_log_card (t : V) (z : V → ℝ) :
    headCE .tanh t z ≤ 2 * 1 + Real.log (Fintype.card V : ℝ) := by
  refine headCE_le_two_add_log_card _ t z 1 ?_
  intro v
  exact le_of_lt (Real.abs_tanh_lt_one _)

/-- Parametric instance (core) of P-FLOOR at `LogitMap.ident`:
the bridge form of `CEHeldout.ceOneHot_nonneg`, with the identical
conclusion constant `0`, derived from `headCE_nonneg`. -/
theorem ceOneHot_nonneg_param (t : V) (z : V → ℝ) :
    0 ≤ headCE .ident t z :=
  headCE_nonneg .ident t z

/-- Parametric instance (core) of P-LIPSCHITZ at
`LogitMap.ident`: the bridge form of
`CEQuantized.ceOneHot_le_of_abs_sub_le`, with the identical conclusion
constant `2 * r` and the identical hypothesis pattern, derived from
`headCE_le_of_abs_sub_le`. -/
theorem ceOneHot_le_of_abs_sub_le_param (t : V) (z y : V → ℝ) (r : ℝ)
    (h : ∀ v, |z v - y v| ≤ r) :
    headCE .ident t z ≤ headCE .ident t y + 2 * r :=
  headCE_le_of_abs_sub_le .ident t z y r h

/-- Parametric instance (core) of P-RANGE-BOUND at
`LogitMap.ident`: the bridge form of
`CEHeldout.ceOneHot_le_two_add_log_card`, with the identical conclusion
constant `2 * r + log card`, derived from `headCE_le_two_add_log_card`.
-/
theorem ceOneHot_le_two_add_log_card_param (t : V) (z : V → ℝ) (r : ℝ)
    (hz : ∀ v, |z v| ≤ r) :
    headCE .ident t z ≤ 2 * r + Real.log (Fintype.card V : ℝ) :=
  headCE_le_two_add_log_card .ident t z r hz

/-- Parametric instance (core) of P-LIPSCHITZ at radius zero:
the bridge form of `CEPadding.ceOneHot_padVector`, the equality of the
cross-entropy before and after zero padding, derived from two
applications of `headCE_le_of_abs_sub_le` at `r = 0` (the pad-specific
content `CEPadding.ceLogits_padVector_fun` supplies the hypothesis).
-/
theorem ceOneHot_padVector_param {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) (t : V) :
    headCE .ident t (Hagi.Model.ceLogits X w) =
      headCE .ident t (Hagi.Model.ceLogits
        (CEPadding.padFeatures X) (CEPadding.padVector w)) := by
  have hfun : Hagi.Model.ceLogits X w =
      Hagi.Model.ceLogits (CEPadding.padFeatures X)
        (CEPadding.padVector w) :=
    CEPadding.ceLogits_padVector_fun X w
  have hrw : ∀ v, |Hagi.Model.ceLogits X w v -
      Hagi.Model.ceLogits (CEPadding.padFeatures X)
        (CEPadding.padVector w) v| ≤ 0 := by
    intro v
    rw [hfun]
    simp
  have h1 : headCE .ident t (Hagi.Model.ceLogits X w) ≤
      headCE .ident t (Hagi.Model.ceLogits
        (CEPadding.padFeatures X) (CEPadding.padVector w)) + 2 * 0 :=
    headCE_le_of_abs_sub_le .ident t _ _ 0 hrw
  have h2 : headCE .ident t (Hagi.Model.ceLogits
        (CEPadding.padFeatures X) (CEPadding.padVector w)) ≤
      headCE .ident t (Hagi.Model.ceLogits X w) + 2 * 0 :=
    headCE_le_of_abs_sub_le .ident t _ _ 0
      (fun v => by rw [abs_sub_comm]; exact hrw v)
  simp only [mul_zero, add_zero] at h1 h2
  exact le_antisymm h1 h2

/-!
## tranche two: the batch aggregation core theorem and the C4/C5
bridges

Migration tranche two: batch descent (priority 2) and confidence/held-out (priority 5).
One new batch parametric core theorem (the `Finset.sum` composition
every C5 file repeats inline), the definitional bridge from
`BatchCEDescent.batchLoss` to `headLoss` at the inverse-card weighted
reduction, a P-FLOOR batch corollary, the bridge of the batch margin
sum theorem, and the C4 decoded-codebook range-bound bridges (closing
the ledger row-7 partial).  The original statements in
`BatchCEDescent*` and `CEHeldout` are unchanged and remain the frozen
originals; the bridges carry the same conclusion constants.
-/

/-- P-AGGREGATE (batch parametric core, task item 2): nonnegative
weights lift a per-example CE bound to the batch loss.  This is the
`Finset.sum_le_sum` composition the batch descent family repeats
inline in every file; the parametric form states it once, for every
logit map and every reduction. -/
theorem headLoss_le_of_forall_headCE_le
    (cfg : HeadConfig ι) (t : ι → V) (z z' : ι → V → ℝ) (F : ι → ℝ)
    (hw : ∀ i, 0 ≤ cfg.reduction.weight i)
    (h : ∀ i, headCE cfg.logitMap (t i) (z i) ≤
      headCE cfg.logitMap (t i) (z' i) + F i) :
    headLoss cfg t z ≤ headLoss cfg t z' +
      ∑ i, cfg.reduction.weight i * F i := by
  unfold headLoss
  have hsum : ∑ i, cfg.reduction.weight i *
      headCE cfg.logitMap (t i) (z i) ≤
      ∑ i, (cfg.reduction.weight i *
        headCE cfg.logitMap (t i) (z' i) +
        cfg.reduction.weight i * F i) :=
    Finset.sum_le_sum (fun i _hi => by
      have hb := mul_le_mul_of_nonneg_left (h i) (hw i)
      linarith)
  rw [Finset.sum_add_distrib] at hsum
  exact hsum

/-- Definitional bridge (C5): the batch family's `batchLoss` IS the
parametric `headLoss` at `LogitMap.ident` with the inverse-card
weighted reduction.  Unconditional, including the empty batch (both
sides are `0` there). -/
theorem batchLoss_param {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) :
    headLoss ⟨.ident, .weighted fun _ => (B : ℝ)⁻¹⟩ y
        (fun b => Hagi.Model.ceLogits (X b) θ) =
      Hagi.Model.BatchCEDescent.batchLoss X θ y := by
  unfold headLoss Hagi.Model.BatchCEDescent.batchLoss
    Hagi.Probability.FiniteFamilyConfidence.empiricalMean headCE
    Reduction.weight
  rw [div_eq_inv_mul, ← Finset.mul_sum]
  rfl

/-- P-FLOOR at batch level (new-constant corollary, no original
restated): the batch family's loss is nonnegative
parametric batch floor. -/
theorem batchLoss_nonneg_param {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) :
    0 ≤ Hagi.Model.BatchCEDescent.batchLoss X θ y := by
  rw [← batchLoss_param X θ y]
  refine headLoss_nonneg_of_nonneg_weight
    ⟨.ident, .weighted fun _ => (B : ℝ)⁻¹⟩ y _ ?_
  intro i
  exact inv_nonneg.mpr (Nat.cast_nonneg B)

/-- P-AGGREGATE descent template, once: any next parameter
point whose per-example CE is bounded by `ceOneHot (y b) θ - m b`
has batch loss bounded by `batchLoss θ - (∑ m)/B`.  The three
`*_le_*_sum_param` bridges below are one-line instances; previously
each carried a byte-identical copy of this proof. -/
theorem batchLoss_next_le_of_forall_ceOneHot_le {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ)
    (θ θ' : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (m : Fin B → ℝ)
    (h : ∀ b, Hagi.ceOneHot (y b) (Hagi.Model.ceLogits (X b) θ') ≤
      Hagi.ceOneHot (y b) (Hagi.Model.ceLogits (X b) θ) - m b) :
    Hagi.Model.BatchCEDescent.batchLoss X θ' y ≤
      Hagi.Model.BatchCEDescent.batchLoss X θ y -
        (∑ b, m b) / (B : ℝ) := by
  have hcore :=
    headLoss_le_of_forall_headCE_le
      (⟨.ident, .weighted fun _ => (B : ℝ)⁻¹⟩ : HeadConfig (Fin B)) y
      (fun b => Hagi.Model.ceLogits (X b) θ')
      (fun b => Hagi.Model.ceLogits (X b) θ)
      (fun b => -m b)
      (fun i => inv_nonneg.mpr (Nat.cast_nonneg B))
      (fun b => h b)
  rw [batchLoss_param X θ' y,
    batchLoss_param X θ y] at hcore
  have hsum : ∑ i : Fin B, (B : ℝ)⁻¹ * (-m i) =
      -((∑ b, m b) / (B : ℝ)) := by
    rw [← Finset.mul_sum, Finset.sum_neg_distrib, ← neg_div,
      div_eq_inv_mul]
  simp only [Reduction.weight] at hcore
  rw [hsum] at hcore
  rw [sub_eq_add_neg]
  exact hcore

/-- Parametric instance of P-AGGREGATE at the batch family's
margin bound: the bridge form of
`BatchCEDescent.batchLoss_batchDirectionNextParameters_le_margin_sum`,
with the identical conclusion constants (`- (∑ margin) / ↑B`); the
per-example hypothesis is the frozen original margin theorem, used,
not restated. -/
theorem batchLoss_batchDirectionNextParameters_le_margin_sum_param
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (D : EuclideanSpace ℝ (Fin d)) :
    Hagi.Model.BatchCEDescent.batchLoss X
        (Hagi.Model.BatchCEDescent.batchDirectionNextParameters X θ y D) y ≤
      Hagi.Model.BatchCEDescent.batchLoss X θ y -
        (∑ b, Hagi.Model.BatchCEDescent.batchDirectionMargin X θ y D b) /
          (B : ℝ) :=
  batchLoss_next_le_of_forall_ceOneHot_le X θ _ y
    (fun b => Hagi.Model.BatchCEDescent.batchDirectionMargin X θ y D b)
    (fun b =>
      Hagi.Model.BatchCEDescent.ceOneHot_batchDirectionNextParameters_le_margin X θ y D b)

/-- Parametric instance of P-RANGE-BOUND over decoded codebook
logits: the bridge form of
`CEHeldout.ceOneHot_decodeJoint_le_log_card_add`, with the identical
conclusion constants (`log card + 4 * featureAbsSum`); the
range-bound hypothesis is the frozen `abs_ceLogits_decodeJoint_le`
at radius `2 * featureAbsSum`.  Closes the ledger row-7 partial.
-/
theorem ceOneHot_decodeJoint_le_log_card_add_param {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V)
    (c : Hagi.Model.CEHeldout.JointCode G) :
    headCE .ident t
        (Hagi.Model.ceLogits X (Hagi.Model.CEHeldout.decodeJoint e c)) ≤
      Real.log (Fintype.card V : ℝ) +
        4 * Hagi.Model.CEGroupedScale.featureAbsSum X := by
  have h := headCE_le_two_add_log_card .ident t
      (fun v => Hagi.Model.ceLogits X (Hagi.Model.CEHeldout.decodeJoint e c) v)
      (2 * Hagi.Model.CEGroupedScale.featureAbsSum X)
      (fun v => Hagi.Model.CEHeldout.abs_ceLogits_decodeJoint_le e X c v)
  refine le_trans h ?_
  linarith

/-- Parametric instance: the ceBound corollary, bridge form of
`CEHeldout.ceOneHot_decodeJoint_le_ceBound`, with the identical
conclusion constant `ceBound X`, derived from the range-bound bridge
above plus nonnegativity of the feature mass. -/
theorem ceOneHot_decodeJoint_le_ceBound_param {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V)
    (c : Hagi.Model.CEHeldout.JointCode G) :
    headCE .ident t
        (Hagi.Model.ceLogits X (Hagi.Model.CEHeldout.decodeJoint e c)) ≤
      Hagi.Model.CEHeldout.ceBound X := by
  have h := ceOneHot_decodeJoint_le_log_card_add_param e X t c
  have hmass := Hagi.Model.CEHeldout.featureAbsSum_nonneg X
  unfold Hagi.Model.CEHeldout.ceBound at *
  linarith

/-!
## tranche four: the C1 single-example descent bridge

Migration tranche four: the C1 one-step
descent certificate `CEDescent.ceOneHot_next_le` lives entirely on the
pointwise CE functional, so it bridges to `headCE` at `LogitMap.ident`
definitionally (constants verbatim), and the batch axis composes
trivially through the P-AGGREGATE core at `Reduction.uniform`
over the singleton batch — the only tranche exercising `.uniform`.
The frozen original is used, not restated; `ce_first_order_eq` (the
row-9 companion) is proof-level machinery consumed inside the frozen
proof, used as-is.
-/

/-- Parametric instance of P-DESCENT at the C1 single-example
certificate: the bridge form of `CEDescent.ceOneHot_next_le`, with the
identical conclusion constants (`- eta * ceAlignment +
(eta * ceStepRange) ^ 2 / 8`); proved by the frozen original through
the definitional `headCE_ident`. -/
theorem ceOneHot_next_le_param {V : Type} [Fintype V] [Nonempty V]
    {d : ℕ} (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (t : V) {eta : ℝ} (heta : 0 ≤ eta) :
    headCE .ident t (Hagi.Model.ceNextLogits X θ t eta) ≤
      headCE .ident t (Hagi.Model.ceLogits X θ) -
        eta * Hagi.Model.ceAlignment X θ t
        + (eta * Hagi.Model.ceStepRange X θ t) ^ 2 / 8 :=
  Hagi.Model.ceOneHot_next_le X θ t heta

/-- Parametric instance: the single-example descent composed
through the batch aggregation core at `Reduction.uniform` +
`LogitMap.ident` over the singleton batch, conclusion in collapsed
constant form (same constants as the frozen original). -/
theorem headLoss_uniform_next_le_param {V : Type} [Fintype V]
    [Nonempty V] {d : ℕ} (X : Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (t : V) {eta : ℝ} (heta : 0 ≤ eta) :
    headLoss (⟨.ident, .uniform⟩ : HeadConfig (Fin 1)) (fun _ => t)
        (fun _ => Hagi.Model.ceNextLogits X θ t eta) ≤
      headLoss (⟨.ident, .uniform⟩ : HeadConfig (Fin 1)) (fun _ => t)
        (fun _ => Hagi.Model.ceLogits X θ) -
        eta * Hagi.Model.ceAlignment X θ t
        + (eta * Hagi.Model.ceStepRange X θ t) ^ 2 / 8 := by
  have h := headLoss_le_of_forall_headCE_le
    (⟨.ident, .uniform⟩ : HeadConfig (Fin 1)) (fun _ => t)
    (fun _ => Hagi.Model.ceNextLogits X θ t eta)
    (fun _ => Hagi.Model.ceLogits X θ)
    (fun _ => -eta * Hagi.Model.ceAlignment X θ t
      + (eta * Hagi.Model.ceStepRange X θ t) ^ 2 / 8)
    (fun i => by simp [Reduction.weight])
    (fun i => by
      show headCE LogitMap.ident t (Hagi.Model.ceNextLogits X θ t eta) ≤
        headCE LogitMap.ident t (Hagi.Model.ceLogits X θ) +
        (-eta * Hagi.Model.ceAlignment X θ t
          + (eta * Hagi.Model.ceStepRange X θ t) ^ 2 / 8)
      linarith [ceOneHot_next_le_param X θ t heta])
  simp only [headLoss, Reduction.weight, Fin.sum_univ_one, one_mul]
    at h ⊢
  linarith

/-!
## tranche three: the remaining C5 P-DESCENT margin-sum pair and
the C6 contracts wrapper bridges

Migration tranche three: the eta-adaptive half-window margin-sum theorems of
`BatchCEDescentHalfEta`, bridged through the P-AGGREGATE core
composed with the frozen per-example descent facts (the parametric
descent template IS the aggregation theorem; no new core needed). The
C6 contracts wrapper bridges (P-FLOOR wrappers of
`Hagi.Contracts.BatchCEBudgetGuard`) live in that Contracts file, this
side of the layer boundary. The majorizer-aggregate descent statements
(`batchLoss_alongNext_le_batchMajorizer` etc.) are recorded
not-parametric-with-reason in the ledger: their RHS is a
Jensen-gap aggregate, not a `∑ w * F` composition.
-/

/-- Parametric instance of P-DESCENT at the eta-adaptive half
window: the bridge form of `BatchCEDescentHalfEta.
batchLoss_batchDirectionHalfNextParameters_le_quadraticMargin_sum`, with
the identical conclusion constants (`- (∑ quadraticMargin (halfEta)) /
↑B`, eta application verbatim); the per-example hypothesis is the
frozen per-example quadratic-margin theorem, used, not restated. -/
theorem batchLoss_batchDirectionHalfNextParameters_le_quadraticMargin_sum_param
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (D : EuclideanSpace ℝ (Fin d)) :
    Hagi.Model.BatchCEDescent.batchLoss X
        (Hagi.Model.BatchCEDescent.batchDirectionHalfNextParameters X θ y D) y ≤
      Hagi.Model.BatchCEDescent.batchLoss X θ y -
        (∑ b, Hagi.Model.BatchCEDescent.batchDirectionQuadraticMargin X θ y D
          (Hagi.Model.BatchCEDescent.batchDirectionHalfEta X θ y D) b) /
          (B : ℝ) :=
  batchLoss_next_le_of_forall_ceOneHot_le X θ _ y
    (fun b => Hagi.Model.BatchCEDescent.batchDirectionQuadraticMargin X θ y D
      (Hagi.Model.BatchCEDescent.batchDirectionHalfEta X θ y D) b)
    (fun b =>
      Hagi.Model.BatchCEDescent.ceOneHot_batchDirectionHalfNextParameters_le_quadraticMargin
          X θ y D b)

/-- Parametric instance of P-DESCENT at the eta-adaptive half
window: the bridge form of `BatchCEDescentHalfEta.
batchLoss_batchDirectionHalfNextParameters_le_margin_sum`, with the
identical conclusion constants (`- (∑ batchDirectionMargin) / ↑B`);
the per-example hypothesis is the frozen per-example margin theorem,
used, not restated. -/
theorem batchLoss_batchDirectionHalfNextParameters_le_margin_sum_param
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (D : EuclideanSpace ℝ (Fin d)) :
    Hagi.Model.BatchCEDescent.batchLoss X
        (Hagi.Model.BatchCEDescent.batchDirectionHalfNextParameters X θ y D) y ≤
      Hagi.Model.BatchCEDescent.batchLoss X θ y -
        (∑ b, Hagi.Model.BatchCEDescent.batchDirectionMargin X θ y D b) /
          (B : ℝ) :=
  batchLoss_next_le_of_forall_ceOneHot_le X θ _ y
    (fun b => Hagi.Model.BatchCEDescent.batchDirectionMargin X θ y D b)
    (fun b =>
      Hagi.Model.BatchCEDescent.ceOneHot_batchDirectionHalfNextParameters_le_margin
          X θ y D b)
