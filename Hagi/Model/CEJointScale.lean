/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEGroupedScale

/-!
# Coupled finite dyadic-scale certification

For the complete-five-cell carrier of `CEGroupedScale`, this module minimizes
`min (Σg blockPenalty_g, jointObservedPenalty)` over the complete finite
function space `Fin G → DyadicScaleCode`.  The joint observed branch exposes
possible cancellation between blocks; the separable branch retains the proved
Cycle84 certificate.  Neither branch is an exact cross-entropy change, and the
selected assignment is not claimed to minimize actual cross-entropy.

The complete logical search has `CEGroupedScale.jointCandidateCount G = 255 ^ G`
assignments.  This is neither a `255 * G` optimizer nor a native execution,
storage, or timing claim.  The fixed-width codec result concerns only the
existing finite family.  Nothing here asserts out-of-sample quality, arbitrary
dimension padding, entropy-optimal storage, or a universal architecture optimum.

The proof shapes adapt `CEQuantized.ceOneHot_le_of_abs_sub_le`, the exact joint
decomposition and finite selector of `CEGroupedScale`, and the actual packed
successor conventions of `CEPackedStep`.
-/

set_option relaxedAutoImplicit false
set_option linter.style.openClassical false

open scoped Matrix

namespace Hagi.Model.CEJointScale

open Hagi.Model
open Hagi.Model.CEGroupedScale

/-- Twice the actual total absolute logit displacement of one joint update. -/
noncomputable def jointObservedPenalty {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) : ℝ :=
  2 * ∑ v, |ceLogits X (jointParameters e w scales) v - ceLogits X w v|

/-- The exact joint observed penalty is nonnegative for arbitrary real data. -/
theorem jointObservedPenalty_nonneg {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) :
    0 ≤ jointObservedPenalty e X w scales := by
  unfold jointObservedPenalty
  positivity

/-- Each joint logit displacement is bounded by the observed penalty's
singleton summand; no nonempty-vocabulary premise is needed. -/
theorem abs_ceLogits_joint_sub_le_jointObservedPenalty_half {G : ℕ}
    {V : Type} [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) (v : V) :
    |ceLogits X (jointParameters e w scales) v - ceLogits X w v| ≤
      jointObservedPenalty e X w scales / 2 := by
  have h := Finset.single_le_sum
    (fun u _hu => abs_nonneg
      (ceLogits X (jointParameters e w scales) u - ceLogits X w u))
    (Finset.mem_univ v)
  unfold jointObservedPenalty
  linarith

/-- Actual one-hot CE increases by at most the exact joint observed score. -/
theorem ceOneHot_joint_le_jointObservedPenalty {G : ℕ} {V : Type} [Fintype V]
    [Nonempty V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) :
    Hagi.ceOneHot t (ceLogits X (jointParameters e w scales)) ≤
      Hagi.ceOneHot t (ceLogits X w) + jointObservedPenalty e X w scales := by
  have hce := CEQuantized.ceOneHot_le_of_abs_sub_le t
    (ceLogits X (jointParameters e w scales)) (ceLogits X w)
    (jointObservedPenalty e X w scales / 2)
    (abs_ceLogits_joint_sub_le_jointObservedPenalty_half e X w scales)
  have htwice : 2 * (jointObservedPenalty e X w scales / 2) =
      jointObservedPenalty e X w scales := by ring
  rw [htwice] at hce
  exact hce

/-- The coupled observed displacement is no larger than the sum of the local
observed displacements.  Local CE values are never added. -/
theorem jointObservedPenalty_le_sum_groupObservedPenalty {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) :
    jointObservedPenalty e X w scales ≤
      ∑ g, groupObservedPenalty e X w g (scales g) := by
  unfold jointObservedPenalty groupObservedPenalty
  calc
    2 * ∑ v, |ceLogits X (jointParameters e w scales) v - ceLogits X w v| ≤
        2 * ∑ v, ∑ g,
          |ceLogits X (blockParameters e w g (scales g)) v - ceLogits X w v| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Finset.sum_le_sum
      intro v _hv
      rw [ceLogits_joint_sub_eq_sum_blocks]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = 2 * ∑ g, ∑ v,
          |ceLogits X (blockParameters e w g (scales g)) v - ceLogits X w v| := by
      rw [Finset.sum_comm]
    _ = ∑ g, 2 * ∑ v,
          |ceLogits X (blockParameters e w g (scales g)) v - ceLogits X w v| := by
      rw [Finset.mul_sum]

/-- A reusable pointwise bound by the total separable certificate.  It follows
from Cycle84's exact decomposition and its independently certified local bound. -/
theorem abs_ceLogits_joint_sub_le_sum_blockPenalties_half {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) (v : V) :
    |ceLogits X (jointParameters e w scales) v - ceLogits X w v| ≤
      (∑ g, blockPenalty e X w g (scales g)) / 2 := by
  rw [ceLogits_joint_sub_eq_sum_blocks]
  calc
    |∑ g, (ceLogits X (blockParameters e w g (scales g)) v - ceLogits X w v)| ≤
        ∑ g, |ceLogits X (blockParameters e w g (scales g)) v - ceLogits X w v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g, blockPenalty e X w g (scales g) / 2 := by
      apply Finset.sum_le_sum
      intro g _hg
      exact abs_blockLogit_le_blockPenalty_half e X w g (scales g) v
    _ = (∑ g, blockPenalty e X w g (scales g)) / 2 := by
      rw [Finset.sum_div]

/-- The certified coupled objective, taking the better of two independently
proved upper bounds.  It is not a signed exact CE change. -/
noncomputable def coupledPenalty {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) : ℝ :=
  min (∑ g, blockPenalty e X w g (scales g)) (jointObservedPenalty e X w scales)

/-- Both branches, and hence their minimum, are nonnegative. -/
theorem coupledPenalty_nonneg {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) :
    0 ≤ coupledPenalty e X w scales := by
  apply le_min
  · apply Finset.sum_nonneg
    intro g _hg
    exact blockPenalty_nonneg e X w g (scales g)
  · exact jointObservedPenalty_nonneg e X w scales

/-- The coupled objective retains the complete separable upper-bound branch. -/
theorem coupledPenalty_le_sum_blockPenalties {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) :
    coupledPenalty e X w scales ≤ ∑ g, blockPenalty e X w g (scales g) := by
  exact min_le_left _ _

/-- Actual joint CE is bounded by raw CE plus the coupled certificate.  The
separable and observed branches are selected only after their own proofs. -/
theorem ceOneHot_joint_le_coupledPenalty {G : ℕ} {V : Type} [Fintype V]
    [Nonempty V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) :
    Hagi.ceOneHot t (ceLogits X (jointParameters e w scales)) ≤
      Hagi.ceOneHot t (ceLogits X w) + coupledPenalty e X w scales := by
  by_cases h : (∑ g, blockPenalty e X w g (scales g)) ≤
      jointObservedPenalty e X w scales
  · rw [coupledPenalty, min_eq_left h]
    exact CEGroupedScale.ceOneHot_joint_le_blockPenalties e X t w scales
  · have h' : jointObservedPenalty e X w scales ≤
        ∑ g, blockPenalty e X w g (scales g) := le_of_not_ge h
    rw [coupledPenalty, min_eq_right h']
    exact ceOneHot_joint_le_jointObservedPenalty e X t w scales

/-- Exact finite minimizer of the coupled certificate over every assignment.
The constant known-code function witnesses nonemptiness only; it does not
restrict the full `255 ^ G`-assignment search space. -/
noncomputable def selectedCoupledScales {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) :
    Fin G → Hagi.Runtime.DyadicScaleCode :=
  Classical.choose
    (Finset.exists_min_image
      (Finset.univ : Finset (Fin G → Hagi.Runtime.DyadicScaleCode))
      (coupledPenalty e X w)
      ⟨fun _ => Hagi.Runtime.knownSampleScale, Finset.mem_univ _⟩)

/-- The selected complete assignment belongs to the full finite function space
and minimizes the declared coupled objective there. -/
theorem selectedCoupledScales_spec {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) :
    selectedCoupledScales e X w ∈
        (Finset.univ : Finset (Fin G → Hagi.Runtime.DyadicScaleCode)) ∧
      ∀ scales ∈ (Finset.univ : Finset (Fin G → Hagi.Runtime.DyadicScaleCode)),
        coupledPenalty e X w (selectedCoupledScales e X w) ≤
          coupledPenalty e X w scales := by
  exact Classical.choose_spec
    (Finset.exists_min_image
      (Finset.univ : Finset (Fin G → Hagi.Runtime.DyadicScaleCode))
      (coupledPenalty e X w)
      ⟨fun _ => Hagi.Runtime.knownSampleScale, Finset.mem_univ _⟩)

/-- The selected coupled score is no larger than any complete alternative's. -/
theorem selectedCoupledScales_score_le {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (alternative : Fin G → Hagi.Runtime.DyadicScaleCode) :
    coupledPenalty e X w (selectedCoupledScales e X w) ≤
      coupledPenalty e X w alternative :=
  (selectedCoupledScales_spec e X w).2 alternative (Finset.mem_univ alternative)

/-- Every level of the selected complete assignment is positive. -/
theorem selectedCoupledScales_level_pos {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G) :
    0 < Hagi.Runtime.dyadicLevel (selectedCoupledScales e X w g) :=
  Hagi.Runtime.dyadicLevel_pos _

/-- The full coupled minimum is no larger than Cycle84's selected separable
score.  The latter is used as one complete candidate, not as a constant-only
restriction, and this does not order the two actual CE values. -/
theorem selectedCoupledScales_le_selectedGroupScales_total {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G))) :
    coupledPenalty e X w (selectedCoupledScales e X w) ≤
      ∑ g, blockPenalty e X w g (selectedGroupScales e X w g) := by
  calc
    coupledPenalty e X w (selectedCoupledScales e X w) ≤
        coupledPenalty e X w (selectedGroupScales e X w) :=
      selectedCoupledScales_score_le e X w (selectedGroupScales e X w)
    _ ≤ ∑ g, blockPenalty e X w g (selectedGroupScales e X w g) :=
      coupledPenalty_le_sum_blockPenalties e X w (selectedGroupScales e X w)

/-- Any coupled-eligible complete assignment makes the complete selected
minimum eligible for the exact Cycle81 safe-step residual. -/
theorem selectedCoupledScales_strict_margin_of_exists {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (θ : EuclideanSpace ℝ (Fin (5 * G)))
    (t : V)
    (h : ∃ scales : Fin G → Hagi.Runtime.DyadicScaleCode,
      coupledPenalty e X (ceNextParameters X θ t (safeStepSize X θ t)) scales <
        2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2) :
    coupledPenalty e X (ceNextParameters X θ t (safeStepSize X θ t))
        (selectedCoupledScales e X
          (ceNextParameters X θ t (safeStepSize X θ t))) <
      2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2 := by
  obtain ⟨scales, hscales⟩ := h
  exact lt_of_le_of_lt
    (selectedCoupledScales_score_le e X
      (ceNextParameters X θ t (safeStepSize X θ t)) scales) hscales

/-- Conditional strict actual CE descent of the selected coupled successor at
the actual safe step.  One safe residual and one certification increase are
used; no empirical transition or unconditional descent is asserted. -/
theorem selectedCoupledScales_strict_descent_of_exists {G : ℕ} {V : Type}
    [Fintype V] [Nonempty V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (θ : EuclideanSpace ℝ (Fin (5 * G)))
    (t : V) (hr : 0 < ceStepRange X θ t)
    (h : ∃ scales : Fin G → Hagi.Runtime.DyadicScaleCode,
      coupledPenalty e X (ceNextParameters X θ t (safeStepSize X θ t)) scales <
        2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2) :
    Hagi.ceOneHot t (ceLogits X
        (jointParameters e (ceNextParameters X θ t (safeStepSize X θ t))
          (selectedCoupledScales e X
            (ceNextParameters X θ t (safeStepSize X θ t))))) <
      Hagi.ceOneHot t (ceLogits X θ) := by
  have hquant := ceOneHot_joint_le_coupledPenalty e X t
    (ceNextParameters X θ t (safeStepSize X θ t))
    (selectedCoupledScales e X
      (ceNextParameters X θ t (safeStepSize X θ t)))
  have hmargin := selectedCoupledScales_strict_margin_of_exists e X θ t h
  have hsafe := ceOneHot_safeStep_le_residual X θ t hr
  change Hagi.ceOneHot t (ceLogits X
      (ceNextParameters X θ t (safeStepSize X θ t))) ≤ _ at hsafe
  linarith

/-- Zero joint observed penalty implies exact pointwise equality of joint and
raw logits.  This remains a statement about the supplied features and scores. -/
theorem ceLogits_joint_eq_of_jointObservedPenalty_eq_zero {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode)
    (h : jointObservedPenalty e X w scales = 0) (v : V) :
    ceLogits X (jointParameters e w scales) v = ceLogits X w v := by
  have hsum : ∑ u, |ceLogits X (jointParameters e w scales) u - ceLogits X w u| =
      0 := by
    have hnonneg : 0 ≤
        ∑ u, |ceLogits X (jointParameters e w scales) u - ceLogits X w u| :=
      Finset.sum_nonneg (fun u _hu => abs_nonneg _)
    unfold jointObservedPenalty at h
    linarith
  have hv := (Finset.sum_eq_zero_iff_of_nonneg
    (fun u _hu => abs_nonneg
      (ceLogits X (jointParameters e w scales) u - ceLogits X w u))).mp
    hsum v (Finset.mem_univ v)
  exact sub_eq_zero.mp (abs_eq_zero.mp hv)

/-- Zero coupled penalty forces zero joint observed penalty.  If the minimum is
the separable branch, the pointwise structural bound is essential: zero of a
minimum alone does not imply that its other branch is zero. -/
theorem jointObservedPenalty_eq_zero_of_coupledPenalty_eq_zero {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode)
    (h : coupledPenalty e X w scales = 0) :
    jointObservedPenalty e X w scales = 0 := by
  by_cases hmin : (∑ g, blockPenalty e X w g (scales g)) ≤
      jointObservedPenalty e X w scales
  · rw [coupledPenalty, min_eq_left hmin] at h
    have habs : ∀ v,
        |ceLogits X (jointParameters e w scales) v - ceLogits X w v| = 0 := by
      intro v
      have hv := abs_ceLogits_joint_sub_le_sum_blockPenalties_half e X w scales v
      rw [h] at hv
      exact le_antisymm (by simpa using hv) (abs_nonneg _)
    unfold jointObservedPenalty
    have hsum : ∑ v, |ceLogits X (jointParameters e w scales) v - ceLogits X w v| =
        0 := by
      apply Finset.sum_eq_zero
      intro v _hv
      exact habs v
    rw [hsum]
    norm_num
  · have h' : jointObservedPenalty e X w scales ≤
        ∑ g, blockPenalty e X w g (scales g) := le_of_not_ge hmin
    rw [coupledPenalty, min_eq_right h'] at h
    exact h

/-- Zero coupled penalty gives exact selected-score logit equality, including
when the zero came from the separable branch. -/
theorem ceLogits_joint_eq_of_coupledPenalty_eq_zero {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode)
    (h : coupledPenalty e X w scales = 0) (v : V) :
    ceLogits X (jointParameters e w scales) v = ceLogits X w v := by
  exact ceLogits_joint_eq_of_jointObservedPenalty_eq_zero e X w scales
    (jointObservedPenalty_eq_zero_of_coupledPenalty_eq_zero e X w scales h) v

/-- Zero coupled penalty gives actual one-hot CE equality on nonempty vocabularies. -/
theorem ceOneHot_joint_eq_of_coupledPenalty_eq_zero {G : ℕ} {V : Type} [Fintype V]
    [Nonempty V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode)
    (h : coupledPenalty e X w scales = 0) :
    Hagi.ceOneHot t (ceLogits X (jointParameters e w scales)) =
      Hagi.ceOneHot t (ceLogits X w) := by
  have hlogits : ceLogits X (jointParameters e w scales) = ceLogits X w := by
    funext v
    exact ceLogits_joint_eq_of_coupledPenalty_eq_zero e X w scales h v
  rw [hlogits]

/-- The actual packed payload for each group uses the selected coupled scale
and the actual raw five-cell block at that same scale. -/
noncomputable def packedCoupledScales {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) : Fin G → BitVec 16 := fun g =>
  Hagi.Runtime.dyadicBlock (selectedCoupledScales e X w g) (fun i =>
    Hagi.Runtime.ternaryValueEncode
      (Hagi.Runtime.dyadicLevel (selectedCoupledScales e X w g))
      (blockWeights e w g i))

/-- Decoding the new selector's actual payload returns exactly its selected
quantized block; no selector or scale is borrowed from Cycle84's pack proof. -/
theorem decodeStep_packedCoupledScales {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G) :
    CEPackedStep.decodeStep (packedCoupledScales e X w g) =
      some (quantizedBlock e w g (selectedCoupledScales e X w g)) := by
  unfold CEPackedStep.decodeStep packedCoupledScales quantizedBlock
  rw [Hagi.Runtime.dyadicBlockDecode_encode]
  simp only [Option.map_some]
  congr 1
  ext i
  exact Hagi.Runtime.ternaryValueDecode_encode _ _

/-- The decoded selected block agrees coordinatewise with the complete selected
joint vector through the supplied equivalence. -/
theorem jointParameters_selectedCoupled_eq_quantizedBlock {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (g : Fin G) (i : Fin 5) :
    (jointParameters e w (selectedCoupledScales e X w)).ofLp (e (g, i)) =
      (quantizedBlock e w g (selectedCoupledScales e X w g)).ofLp i := by
  rw [jointParameters_own]
  rfl

/-- On the canonical one-block carrier, any joint assignment is exactly the
existing common-scale quantizer at its only selected level. -/
theorem jointParameters_one_eq_ternaryCEParameters
    (w : EuclideanSpace ℝ (Fin (5 * 1)))
    (scales : Fin 1 → Hagi.Runtime.DyadicScaleCode) :
    jointParameters (canonicalBlockEquiv 1) w scales =
      CEQuantized.ternaryCEParameters
        (Hagi.Runtime.dyadicLevel (scales 0)) w := by
  ext j
  obtain ⟨⟨g, i⟩, rfl⟩ := (canonicalBlockEquiv 1).surjective j
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  rw [jointParameters_own, canonicalBlockEquiv_one_apply]
  rfl

/-- The constant known-code assignment fixes the actual raw safe successor on
the nondegenerate one-block witness. -/
theorem ceQuantWitness_jointParameters_knownSample :
    jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
        (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale) =
      CEPackedStep.rawSuccessor := by
  rw [jointParameters_one_eq_ternaryCEParameters,
    Hagi.Runtime.knownSampleScale_level]
  change CEQuantized.ternaryCEParameters (1 / 4)
    (ceNextParameters CEQuantized.ceQuantWitnessFeatures 0 0
      (safeStepSize CEQuantized.ceQuantWitnessFeatures 0 0)) = _
  exact CEQuantized.ceQuantWitness_ternaryCEParameters

/-- The joint observed branch is zero at the actual quarter-scale assignment. -/
theorem ceQuantWitness_knownSample_jointObservedPenalty :
    jointObservedPenalty (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor
      (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale) = 0 := by
  unfold jointObservedPenalty
  rw [ceQuantWitness_jointParameters_knownSample]
  simp

/-- The old separable score is also zero at that complete assignment. -/
theorem ceQuantWitness_knownSample_separablePenalty :
    (∑ g, blockPenalty (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor g
      ((fun _ : Fin 1 => Hagi.Runtime.knownSampleScale) g)) = 0 := by
  rw [Fin.sum_univ_one]
  exact CEGroupedScale.ceQuantWitness_knownSample_blockPenalty 0

/-- Both zero branches give the actual known-assignment coupled certificate zero. -/
theorem ceQuantWitness_knownSample_coupledPenalty :
    coupledPenalty (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor
      (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale) = 0 := by
  rw [coupledPenalty, ceQuantWitness_knownSample_separablePenalty,
    ceQuantWitness_knownSample_jointObservedPenalty, min_self]

/-- Complete-function minimization and nonnegativity force the selected coupled
certificate to zero; the selected assignment itself is deliberately unidentified. -/
theorem ceQuantWitness_selectedCoupledScales_score :
    coupledPenalty (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor
      (selectedCoupledScales (canonicalBlockEquiv 1)
        CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor) = 0 := by
  apply le_antisymm
  · exact (selectedCoupledScales_score_le (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor
      (fun _ => Hagi.Runtime.knownSampleScale)).trans_eq
      ceQuantWitness_knownSample_coupledPenalty
  · exact coupledPenalty_nonneg _ _ _ _

/-- The selected one-block joint logits equal the actual raw-safe logits. -/
theorem ceQuantWitness_selectedCoupledScales_ceLogits :
    ceLogits CEQuantized.ceQuantWitnessFeatures
      (jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
        (selectedCoupledScales (canonicalBlockEquiv 1)
          CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor)) =
      ceLogits CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor := by
  funext v
  exact ceLogits_joint_eq_of_coupledPenalty_eq_zero (canonicalBlockEquiv 1)
    CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor _
    ceQuantWitness_selectedCoupledScales_score v

/-- The selected one-block joint scores equal the actual raw-safe scores. -/
theorem ceQuantWitness_selectedCoupledScales_ce :
    Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures
      (jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
        (selectedCoupledScales (canonicalBlockEquiv 1)
          CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor))) =
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures
        CEPackedStep.rawSuccessor) := by
  rw [ceQuantWitness_selectedCoupledScales_ceLogits]

/-- Whichever complete assignment is selected, its actual joint CE strictly
decreases below the zero-parameter CE on the nondegenerate witness. -/
theorem ceQuantWitness_selectedCoupledScales_strict_descent :
    Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures
      (jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
        (selectedCoupledScales (canonicalBlockEquiv 1)
          CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor))) <
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures 0) := by
  rw [ceQuantWitness_selectedCoupledScales_ce]
  have hstrict := CEQuantized.ceQuantWitness_strict_descent
  rw [CEQuantized.ceQuantWitness_ternaryCEParameters] at hstrict
  change Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures
    CEPackedStep.rawSuccessor) < _ at hstrict
  exact hstrict

/-- On one block the selected complete joint vector is exactly the vector
represented by its actual packed coupled payload. -/
theorem ceQuantWitness_joint_selectedCoupled_eq_quantizedBlock (g : Fin 1) :
    jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
        (selectedCoupledScales (canonicalBlockEquiv 1)
          CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor) =
      quantizedBlock (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor g
        (selectedCoupledScales (canonicalBlockEquiv 1)
          CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor g) := by
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  ext j
  obtain ⟨⟨h, i⟩, rfl⟩ := (canonicalBlockEquiv 1).surjective j
  have hh : h = 0 := Subsingleton.elim _ _
  subst h
  rw [jointParameters_selectedCoupled_eq_quantizedBlock,
    canonicalBlockEquiv_one_apply]

/-- A real coupled packed block supplies a decoded vector with the actual strict
CE descent of the selected joint successor. -/
theorem ceQuantWitness_decoded_packedCoupledScales_strict_descent :
    ∃ decoded_w : EuclideanSpace ℝ (Fin 5),
      CEPackedStep.decodeStep
          (packedCoupledScales (canonicalBlockEquiv 1)
            CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor 0) =
        some decoded_w ∧
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures decoded_w) <
        Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures 0) := by
  refine ⟨jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
    (selectedCoupledScales (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor), ?_, ?_⟩
  · rw [decodeStep_packedCoupledScales,
      ceQuantWitness_joint_selectedCoupled_eq_quantizedBlock]
  · exact ceQuantWitness_selectedCoupledScales_strict_descent

end Hagi.Model.CEJointScale
