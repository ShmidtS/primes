/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEScaleSelection

/-!
# Independent finite scales for disjoint five-weight blocks

For an explicit equivalence between `Fin G × Fin 5` and `Fin (5 * G)`,
each block gets one of the 255 existing positive dyadic levels.  Every
local score uses the same raw baseline.  Their sum is a certified upper
bound for one actual joint update, not an exact global observed error and
not the minimum of true cross-entropy.

The finite selector follows `Model/CEScaleSelection.lean`; the two error
views adapt `Model/CEQuantized.lean` to disjoint blocks.  Reindexing uses
Mathlib's verified `finProdFinEquiv` (`Logic/Equiv/Fin/Basic.lean`) and
`Equiv.sum_comp`.  `localEvaluationCount` counts mathematical score
calls, not FLOPs or time; `groupPayloadBits` counts the logical fixed-width
codec payload, not physical memory or an entropy-optimal aggregate code.
The carrier consists only of complete multiples of five.
-/

set_option relaxedAutoImplicit false
set_option linter.style.openClassical false

open scoped Matrix

namespace Hagi.Model.CEGroupedScale

open Hagi.Model

/-- The explicit indexing convention: product coordinates are group first
and within-block coordinate second.  No identity-index assumption is made. -/
noncomputable def blockParameters {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) : EuclideanSpace ℝ (Fin (5 * G)) :=
  WithLp.toLp 2 (fun j =>
    if (e.symm j).1 = g then
      Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (w.ofLp j)
    else w.ofLp j)

/-- The joint update quantizes every coordinate at its own group's level. -/
noncomputable def jointParameters {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) :
    EuclideanSpace ℝ (Fin (5 * G)) :=
  WithLp.toLp 2 (fun j =>
    Hagi.Runtime.qTern
      (Hagi.Runtime.dyadicLevel (scales (e.symm j).1)) (w.ofLp j))

/-- On its own block, `blockParameters` applies the advertised quantizer. -/
@[simp] theorem blockParameters_own {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) (i : Fin 5) :
    (blockParameters e w g k).ofLp (e (g, i)) =
      Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (w.ofLp (e (g, i))) := by
  simp [blockParameters]

/-- A block update leaves every coordinate of every other block unchanged. -/
@[simp] theorem blockParameters_other {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g h : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) (i : Fin 5) (hgh : h ≠ g) :
    (blockParameters e w g k).ofLp (e (h, i)) = w.ofLp (e (h, i)) := by
  simp [blockParameters, hgh]

/-- A joint update uses exactly the scale assigned to the coordinate's
block, including when other blocks have different scales. -/
@[simp] theorem jointParameters_own {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode)
    (g : Fin G) (i : Fin 5) :
    (jointParameters e w scales).ofLp (e (g, i)) =
      Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel (scales g))
        (w.ofLp (e (g, i))) := by
  simp [jointParameters]

/-- Exact noninterference at each raw coordinate: all local displacements,
computed from the same `w`, add to the joint displacement. -/
theorem joint_sub_eq_sum_blocks {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) (j : Fin (5 * G)) :
    (jointParameters e w scales).ofLp j - w.ofLp j =
      ∑ g, ((blockParameters e w g (scales g)).ofLp j - w.ofLp j) := by
  classical
  obtain ⟨⟨g, i⟩, rfl⟩ := e.surjective j
  rw [jointParameters_own, Finset.sum_eq_single g]
  · rw [blockParameters_own]
  · intro h _hh hne
    rw [blockParameters_other e w h g (scales h) i hne.symm]
    ring
  · simp

/-- Logit change as a finite feature-weighted coordinate displacement. -/
theorem ceLogits_sub_eq_sum {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (p q : EuclideanSpace ℝ (Fin d)) (v : V) :
    ceLogits X p v - ceLogits X q v =
      ∑ j, X v j * (p.ofLp j - q.ofLp j) := by
  change (∑ j, X v j * p.ofLp j) - (∑ j, X v j * q.ofLp j) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- The complete joint logit displacement is exactly the sum of the block
logit displacements; this identity precedes and does not use CE estimates. -/
theorem ceLogits_joint_sub_eq_sum_blocks {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) (v : V) :
    ceLogits X (jointParameters e w scales) v - ceLogits X w v =
      ∑ g, (ceLogits X (blockParameters e w g (scales g)) v - ceLogits X w v) := by
  simp_rw [ceLogits_sub_eq_sum]
  calc
    (∑ j, X v j * ((jointParameters e w scales).ofLp j - w.ofLp j)) =
        ∑ j, X v j * ∑ g,
          ((blockParameters e w g (scales g)).ofLp j - w.ofLp j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [joint_sub_eq_sum_blocks]
    _ = ∑ j, ∑ g, X v j *
        ((blockParameters e w g (scales g)).ofLp j - w.ofLp j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
    _ = ∑ g, ∑ j, X v j *
        ((blockParameters e w g (scales g)).ofLp j - w.ofLp j) :=
      Finset.sum_comm

/-- The actual raw five-vector of one block, in the supplied equivalence. -/
noncomputable def blockWeights {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G) : Fin 5 → ℝ :=
  fun i => w.ofLp (e (g, i))

/-- Full absolute feature mass.  No within-block factor is substituted
for the full sum over all feature columns and all logits. -/
noncomputable def featureAbsSum {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) : ℝ :=
  ∑ v, ∑ j, |X v j|

/-- Twice the actual sum of absolute logit changes of one block. -/
noncomputable def groupObservedPenalty {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) : ℝ :=
  2 * ∑ v, |ceLogits X (blockParameters e w g k) v - ceLogits X w v|

/-- Saturation-aware structural score of the actual five raw weights. -/
noncomputable def groupStructuralPenalty {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) : ℝ :=
  2 * featureAbsSum X *
    Real.sqrt (5 * (Hagi.Runtime.dyadicLevel k / 2) ^ 2 +
      Hagi.Runtime.satTail (Hagi.Runtime.dyadicLevel k) (blockWeights e w g))

/-- The certified local objective: the minimum of two independently
proved upper bounds, not an exact local CE change. -/
noncomputable def blockPenalty {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) : ℝ :=
  min (groupObservedPenalty e X w g k) (groupStructuralPenalty e X w g k)

/-- Reindex a block logit difference to exactly five matrix products. -/
theorem ceLogits_block_sub_eq_five {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) (v : V) :
    ceLogits X (blockParameters e w g k) v - ceLogits X w v =
      ∑ i, X v (e (g, i)) *
        (Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g i) -
          blockWeights e w g i) := by
  classical
  rw [ceLogits_sub_eq_sum]
  calc
    (∑ j, X v j * ((blockParameters e w g k).ofLp j - w.ofLp j)) =
        ∑ p : Fin G × Fin 5, X v (e p) *
          ((blockParameters e w g k).ofLp (e p) - w.ofLp (e p)) :=
      (Equiv.sum_comp e (fun j => X v j *
        ((blockParameters e w g k).ofLp j - w.ofLp j))).symm
    _ = ∑ h, ∑ i, X v (e (h, i)) *
        ((blockParameters e w g k).ofLp (e (h, i)) - w.ofLp (e (h, i))) :=
      Fintype.sum_prod_type _
    _ = ∑ i, X v (e (g, i)) *
        ((blockParameters e w g k).ofLp (e (g, i)) - w.ofLp (e (g, i))) := by
      rw [Finset.sum_eq_single g]
      · intro h _hh hne
        apply Finset.sum_eq_zero
        intro i _hi
        rw [blockParameters_other e w g h k i hne]
        ring
      · simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [blockParameters_own]
      rfl

/-- One actual coordinate error is bounded by the five-dimensional
squared-error budget; saturation has not yet been idealized away. -/
theorem abs_qTern_block_le_sqrt {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G) (s : ℝ) (i : Fin 5) :
    |Hagi.Runtime.qTern s (blockWeights e w g i) - blockWeights e w g i| ≤
      Real.sqrt (∑ j, (blockWeights e w g j -
        Hagi.Runtime.qTern s (blockWeights e w g j)) ^ 2) := by
  rw [abs_sub_comm, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (blockWeights e w g j -
      Hagi.Runtime.qTern s (blockWeights e w g j)))
    (Finset.mem_univ i)

/-- Five block features are dominated by the full absolute feature mass. -/
theorem blockFeatureAbs_le {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (g : Fin G) (v : V) :
    (∑ i, |X v (e (g, i))|) ≤ featureAbsSum X := by
  have hrow : (∑ i, |X v (e (g, i))|) ≤ ∑ j, |X v j| := by
    rw [← Equiv.sum_comp e (fun j => |X v j|), Fintype.sum_prod_type]
    exact Finset.single_le_sum
      (fun h _hh => Finset.sum_nonneg (fun i _hi => abs_nonneg (X v (e (h, i)))))
      (Finset.mem_univ g)
  exact hrow.trans (Finset.single_le_sum
    (fun u _hu => Finset.sum_nonneg (fun j _hj => abs_nonneg (X u j)))
    (Finset.mem_univ v))

/-- Pointwise structural error before applying `ternary_split_le`. -/
theorem abs_blockLogit_le_sqrt {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) (v : V) :
    |ceLogits X (blockParameters e w g k) v - ceLogits X w v| ≤
      featureAbsSum X * Real.sqrt (∑ i, (blockWeights e w g i -
        Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g i)) ^ 2) := by
  rw [ceLogits_block_sub_eq_five]
  calc
    |∑ i, X v (e (g, i)) *
        (Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g i) -
          blockWeights e w g i)| ≤
        ∑ i, |X v (e (g, i)) *
          (Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g i) -
            blockWeights e w g i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |X v (e (g, i))| *
        |Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g i) -
          blockWeights e w g i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul]
    _ ≤ ∑ i, |X v (e (g, i))| *
        Real.sqrt (∑ j, (blockWeights e w g j -
          Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g j)) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left (abs_qTern_block_le_sqrt e w g _ i)
        (abs_nonneg (X v (e (g, i))))
    _ = (∑ i, |X v (e (g, i))|) *
        Real.sqrt (∑ j, (blockWeights e w g j -
          Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g j)) ^ 2) := by
      rw [Finset.sum_mul]
    _ ≤ featureAbsSum X * Real.sqrt (∑ j, (blockWeights e w g j -
        Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g j)) ^ 2) :=
      mul_le_mul_of_nonneg_right (blockFeatureAbs_le e X g v) (Real.sqrt_nonneg _)

/-- Both actual error views yield the same certified structural score with
the five-cell factor, using the proved saturating-quantizer split. -/
theorem abs_blockLogit_le_structural_half {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) (v : V) :
    |ceLogits X (blockParameters e w g k) v - ceLogits X w v| ≤
      groupStructuralPenalty e X w g k / 2 := by
  have hs := Hagi.Runtime.dyadicLevel_pos k
  have hsplit := Hagi.Runtime.ternary_split_le
    (Hagi.Runtime.dyadicLevel k) hs (blockWeights e w g)
  norm_num at hsplit
  have hmass : 0 ≤ featureAbsSum X := by
    unfold featureAbsSum
    positivity
  calc
    |ceLogits X (blockParameters e w g k) v - ceLogits X w v| ≤
        featureAbsSum X * Real.sqrt (∑ i, (blockWeights e w g i -
          Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g i)) ^ 2) :=
      abs_blockLogit_le_sqrt e X w g k v
    _ ≤ featureAbsSum X * Real.sqrt (5 * (Hagi.Runtime.dyadicLevel k / 2) ^ 2 +
        Hagi.Runtime.satTail (Hagi.Runtime.dyadicLevel k) (blockWeights e w g)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsplit) hmass
    _ = groupStructuralPenalty e X w g k / 2 := by
      unfold groupStructuralPenalty
      ring

/-- The observed branch directly bounds each logit displacement. -/
theorem abs_blockLogit_le_observed_half {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) (v : V) :
    |ceLogits X (blockParameters e w g k) v - ceLogits X w v| ≤
      groupObservedPenalty e X w g k / 2 := by
  have h := Finset.single_le_sum
    (fun u _hu => abs_nonneg
      (ceLogits X (blockParameters e w g k) u - ceLogits X w u))
    (Finset.mem_univ v)
  unfold groupObservedPenalty
  linarith

/-- The observed score is nonnegative for arbitrary real data. -/
theorem groupObservedPenalty_nonneg {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) : 0 ≤ groupObservedPenalty e X w g k := by
  unfold groupObservedPenalty
  positivity

/-- The structural score is nonnegative, including saturated weights. -/
theorem groupStructuralPenalty_nonneg {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) : 0 ≤ groupStructuralPenalty e X w g k := by
  unfold groupStructuralPenalty featureAbsSum
  positivity

/-- Taking the minimum preserves nonnegativity because both branches are
nonnegative; this is not a signed exact-error calculation. -/
theorem blockPenalty_nonneg {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) : 0 ≤ blockPenalty e X w g k :=
  le_min (groupObservedPenalty_nonneg e X w g k)
    (groupStructuralPenalty_nonneg e X w g k)

/-- Crucial pointwise bound for the local certified objective. -/
theorem abs_blockLogit_le_blockPenalty_half {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) (v : V) :
    |ceLogits X (blockParameters e w g k) v - ceLogits X w v| ≤
      blockPenalty e X w g k / 2 := by
  rcases le_total (groupObservedPenalty e X w g k)
      (groupStructuralPenalty e X w g k) with h | h
  · rw [blockPenalty, min_eq_left h]
    exact abs_blockLogit_le_observed_half e X w g k v
  · rw [blockPenalty, min_eq_right h]
    exact abs_blockLogit_le_structural_half e X w g k v

/-- Full one-hot CE bound for the actual joint update.  The proof is the
exact global logit identity, the triangle inequality and the existing
`ceOneHot_le_of_abs_sub_le`; local CE values are never added. -/
theorem ceOneHot_joint_le_blockPenalties {G : ℕ} {V : Type} [Fintype V]
    [Nonempty V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (scales : Fin G → Hagi.Runtime.DyadicScaleCode) :
    Hagi.ceOneHot t (ceLogits X (jointParameters e w scales)) ≤
      Hagi.ceOneHot t (ceLogits X w) +
        ∑ g, blockPenalty e X w g (scales g) := by
  have hpoint : ∀ v,
      |ceLogits X (jointParameters e w scales) v - ceLogits X w v| ≤
        ∑ g, blockPenalty e X w g (scales g) / 2 := by
    intro v
    rw [ceLogits_joint_sub_eq_sum_blocks]
    calc
      |∑ g, (ceLogits X (blockParameters e w g (scales g)) v - ceLogits X w v)| ≤
          ∑ g, |ceLogits X (blockParameters e w g (scales g)) v - ceLogits X w v| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ g, blockPenalty e X w g (scales g) / 2 := by
        apply Finset.sum_le_sum
        intro g _hg
        exact abs_blockLogit_le_blockPenalty_half e X w g (scales g) v
  have hce := CEQuantized.ceOneHot_le_of_abs_sub_le t
    (ceLogits X (jointParameters e w scales)) (ceLogits X w)
    (∑ g, blockPenalty e X w g (scales g) / 2) hpoint
  have htwice : 2 * (∑ g, blockPenalty e X w g (scales g) / 2) =
      ∑ g, blockPenalty e X w g (scales g) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _hg
    ring
  rw [htwice] at hce
  exact hce

/-- Independently choose one exact finite minimizer per block.  The
universal finite set is all 255 codes; the sample is nonemptiness only. -/
noncomputable def selectedGroupScales {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) :
    Fin G → Hagi.Runtime.DyadicScaleCode := fun g =>
  Classical.choose
    (Finset.exists_min_image (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode)
      (blockPenalty e X w g)
      ⟨Hagi.Runtime.knownSampleScale, Finset.mem_univ _⟩)

/-- Every selected code belongs to the full 255-element code family and
attains that block's minimum declared certified objective. -/
theorem selectedGroupScales_spec {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G) :
    selectedGroupScales e X w g ∈
        (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode) ∧
      ∀ k ∈ (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode),
        blockPenalty e X w g (selectedGroupScales e X w g) ≤
          blockPenalty e X w g k := by
  exact Classical.choose_spec
    (Finset.exists_min_image (Finset.univ : Finset Hagi.Runtime.DyadicScaleCode)
      (blockPenalty e X w g)
      ⟨Hagi.Runtime.knownSampleScale, Finset.mem_univ _⟩)

/-- The selected block score is no larger than any candidate block score. -/
theorem selectedGroupScales_score_le {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) :
    blockPenalty e X w g (selectedGroupScales e X w g) ≤
      blockPenalty e X w g k :=
  (selectedGroupScales_spec e X w g).2 k (Finset.mem_univ k)

/-- Exact minimization of the separable certificate over every assignment.
This is not a claim that true CE or the best joint structural bound is
minimized, and no enumeration of the joint family is performed. -/
theorem selectedGroupScales_total_le {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (alternative : Fin G → Hagi.Runtime.DyadicScaleCode) :
    (∑ g, blockPenalty e X w g (selectedGroupScales e X w g)) ≤
      ∑ g, blockPenalty e X w g (alternative g) := by
  apply Finset.sum_le_sum
  intro g _hg
  exact selectedGroupScales_score_le e X w g (alternative g)

/-- Every independently selected level remains positive. -/
theorem selectedGroupScales_level_pos {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G) :
    0 < Hagi.Runtime.dyadicLevel (selectedGroupScales e X w g) :=
  Hagi.Runtime.dyadicLevel_pos _

/-- The nonnegative selected separable certificate. -/
theorem selectedGroupScales_total_nonneg {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) :
    0 ≤ ∑ g, blockPenalty e X w g (selectedGroupScales e X w g) := by
  apply Finset.sum_nonneg
  intro g _hg
  exact blockPenalty_nonneg e X w g _

/-- Number of mathematical joint scale assignments in the complete finite
family.  The selection algorithm does not enumerate this many objects. -/
def jointCandidateCount (G : ℕ) : ℕ := 255 ^ G

/-- The joint count is the cardinality of all code assignments. -/
theorem jointCandidateCount_eq_card (G : ℕ) :
    jointCandidateCount G =
      Fintype.card (Fin G → Hagi.Runtime.DyadicScaleCode) := by
  simp [jointCandidateCount]

/-- Number of local score evaluations in the explicit independent search
model: one per group and code, not a FLOP, instruction or timing claim. -/
def localEvaluationCount (G : ℕ) : ℕ := G * 255

/-- The evaluation count is the cardinality of all group/code pairs. -/
theorem localEvaluationCount_eq_card (G : ℕ) :
    localEvaluationCount G =
      Fintype.card (Fin G × Hagi.Runtime.DyadicScaleCode) := by
  simp [localEvaluationCount]

/-- There is exactly one empty joint assignment. -/
theorem jointCandidateCount_zero : jointCandidateCount 0 = 1 := by
  norm_num [jointCandidateCount]

/-- The empty carrier requires no local score calls. -/
theorem localEvaluationCount_zero : localEvaluationCount 0 = 0 := by
  norm_num [localEvaluationCount]

private lemma le_twoFiftyFive_pow {G : ℕ} (hG : 0 < G) : G ≤ 255 ^ (G - 1) := by
  induction G with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simp
    · have hi := ih (Nat.pos_of_ne_zero hn)
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hp : 255 ^ n = 255 ^ (n - 1) * 255 := by
        calc
          255 ^ n = 255 ^ (n - 1 + 1) := by congr 1; omega
          _ = 255 ^ (n - 1) * 255 := Nat.pow_succ _ _
      have hpow1 : 1 ≤ 255 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
      simp only [Nat.add_sub_cancel]
      omega

/-- Independent local searches use no more mathematical score evaluations
than there are assignments in the complete joint candidate family. -/
theorem localEvaluationCount_le_jointCandidateCount {G : ℕ} (hG : 0 < G) :
    localEvaluationCount G ≤ jointCandidateCount G := by
  unfold localEvaluationCount jointCandidateCount
  calc
    G * 255 ≤ 255 ^ (G - 1) * 255 :=
      Nat.mul_le_mul_right 255 (le_twoFiftyFive_pow hG)
    _ = 255 ^ (G - 1 + 1) := (Nat.pow_succ _ _).symm
    _ = 255 ^ G := by
      congr 1
      exact Nat.sub_add_cancel hG

private lemma succ_add_three_le_twoFiftyFive_pow (n : ℕ) : n + 3 ≤ 255 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 255 ^ (n + 1) ≤ 255 ^ (n + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- With at least two groups, independent local searches use strictly fewer
mathematical score evaluations than the complete joint candidate count. -/
theorem localEvaluationCount_lt_jointCandidateCount {G : ℕ} (hG : 2 ≤ G) :
    localEvaluationCount G < jointCandidateCount G := by
  unfold localEvaluationCount jointCandidateCount
  have hn : ∃ n : ℕ, G = n + 2 := ⟨G - 2, by omega⟩
  obtain ⟨n, rfl⟩ := hn
  have hs : n + 3 ≤ 255 ^ (n + 1) := succ_add_three_le_twoFiftyFive_pow n
  calc
    (n + 2) * 255 < (n + 3) * 255 := by omega
    _ ≤ 255 ^ (n + 1) * 255 := Nat.mul_le_mul_right 255 hs
    _ = 255 ^ (n + 2) := (Nat.pow_succ _ _).symm

/-- A named bit counter for `5 * G` reference weights, each charged 64
bits.  It is not a model of native storage or total training memory. -/
def groupReference64BitCounter (G : ℕ) : ℕ := (5 * G) * 64

/-- One actual 16-bit word per group in the fixed-width block codec. -/
def groupPayloadBits (G : ℕ) : ℕ := 16 * G

/-- The logical block payload is smaller than the separately named
64-bit-per-weight reference counter for every nonempty block family. -/
theorem groupPayloadBits_lt_groupReference64BitCounter {G : ℕ} (hG : 0 < G) :
    groupPayloadBits G < groupReference64BitCounter G := by
  unfold groupPayloadBits groupReference64BitCounter
  omega

/-- The empty carrier has zero logical payload bits. -/
theorem groupPayloadBits_zero : groupPayloadBits 0 = 0 := by
  norm_num [groupPayloadBits]

/-- Any eligible full assignment makes the independently selected total
certified penalty eligible by the proved total minimum. -/
theorem selectedGroupScales_strict_margin_of_exists {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (θ : EuclideanSpace ℝ (Fin (5 * G)))
    (t : V)
    (h : ∃ scales : Fin G → Hagi.Runtime.DyadicScaleCode,
      (∑ g, blockPenalty e X
          (ceNextParameters X θ t (safeStepSize X θ t)) g (scales g)) <
        2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2) :
    (∑ g, blockPenalty e X
        (ceNextParameters X θ t (safeStepSize X θ t)) g
        (selectedGroupScales e X
          (ceNextParameters X θ t (safeStepSize X θ t)) g)) <
      2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2 := by
  obtain ⟨scales, hscales⟩ := h
  exact lt_of_le_of_lt
    (selectedGroupScales_total_le e X
      (ceNextParameters X θ t (safeStepSize X θ t)) scales) hscales

/-- Conditional strict CE descent of the actual selected joint successor.
Without the existence premise there is no strict descent claim, and no
converse or raw-CE minimization is asserted. -/
theorem selectedGroupScales_strict_descent_of_exists {G : ℕ} {V : Type}
    [Fintype V] [Nonempty V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (θ : EuclideanSpace ℝ (Fin (5 * G)))
    (t : V) (hr : 0 < ceStepRange X θ t)
    (h : ∃ scales : Fin G → Hagi.Runtime.DyadicScaleCode,
      (∑ g, blockPenalty e X
          (ceNextParameters X θ t (safeStepSize X θ t)) g (scales g)) <
        2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2) :
    Hagi.ceOneHot t (ceLogits X
        (jointParameters e (ceNextParameters X θ t (safeStepSize X θ t))
          (selectedGroupScales e X
            (ceNextParameters X θ t (safeStepSize X θ t))))) <
      Hagi.ceOneHot t (ceLogits X θ) := by
  have hquant := ceOneHot_joint_le_blockPenalties e X t
    (ceNextParameters X θ t (safeStepSize X θ t))
    (selectedGroupScales e X
      (ceNextParameters X θ t (safeStepSize X θ t)))
  have hmargin := selectedGroupScales_strict_margin_of_exists e X θ t h
  have hsafe := ceOneHot_safeStep_le_residual X θ t hr
  change Hagi.ceOneHot t (ceLogits X
      (ceNextParameters X θ t (safeStepSize X θ t))) ≤ _ at hsafe
  linarith

/-- The actual five-cell quantized block at a specified common level. -/
noncomputable def quantizedBlock {G : ℕ}
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : Hagi.Runtime.DyadicScaleCode) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (fun i =>
    Hagi.Runtime.qTern (Hagi.Runtime.dyadicLevel k) (blockWeights e w g i))

/-- Each selected scale is packed together with the word obtained from
the same raw block and the same selected level, via the existing codec. -/
noncomputable def packedBlocks {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) : Fin G → BitVec 16 := fun g =>
  Hagi.Runtime.dyadicBlock (selectedGroupScales e X w g) (fun i =>
    Hagi.Runtime.ternaryValueEncode
      (Hagi.Runtime.dyadicLevel (selectedGroupScales e X w g))
      (blockWeights e w g i))

/-- Every packed group decodes through `CEPackedStep.decodeStep` to
exactly the actual selected quantized five-cell parameters, or to `none`
only for invalid external inputs not produced by this encoder. -/
theorem decodeStep_packedBlocks {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G) :
    CEPackedStep.decodeStep (packedBlocks e X w g) =
      some (quantizedBlock e w g (selectedGroupScales e X w g)) := by
  unfold CEPackedStep.decodeStep packedBlocks quantizedBlock
  rw [Hagi.Runtime.dyadicBlockDecode_encode]
  simp only [Option.map_some]
  congr 1
  ext i
  exact Hagi.Runtime.ternaryValueDecode_encode _ _

/-- Equivalence-coordinate compatibility: decoded/real block value `i`
is exactly the joint update at `e (g, i)`, with no scale or payload
reassociation between different groups. -/
theorem jointParameters_selected_eq_quantizedBlock {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G) (i : Fin 5) :
    (jointParameters e w (selectedGroupScales e X w)).ofLp (e (g, i)) =
      (quantizedBlock e w g (selectedGroupScales e X w g)).ofLp i := by
  rw [jointParameters_own]
  rfl

/-- The canonical group-first equivalence.  Mathlib's product equivalence
lands in `Fin (G * 5)` and maps `(g,i)` to `i + 5*g`; `finCongr` performs
only the required commutativity cast to the primary `Fin (5 * G)` carrier. -/
def canonicalBlockEquiv (G : ℕ) : (Fin G × Fin 5) ≃ Fin (5 * G) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm G 5))

/-- On one block the canonical equivalence is literally coordinate `i`. -/
theorem canonicalBlockEquiv_one_apply (i : Fin 5) :
    canonicalBlockEquiv 1 (0, i) = i := by
  rfl

/-- For one block the local update is exactly the existing common-scale
quantizer, under the canonical equivalence. -/
theorem blockParameters_one_eq_ternaryCEParameters
    (w : EuclideanSpace ℝ (Fin (5 * 1))) (g : Fin 1)
    (k : Hagi.Runtime.DyadicScaleCode) :
    blockParameters (canonicalBlockEquiv 1) w g k =
      CEQuantized.ternaryCEParameters (Hagi.Runtime.dyadicLevel k) w := by
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  ext j
  obtain ⟨⟨h, i⟩, rfl⟩ := (canonicalBlockEquiv 1).surjective j
  have hh : h = 0 := Subsingleton.elim _ _
  subst h
  rw [blockParameters_own, canonicalBlockEquiv_one_apply]
  rfl

/-- The known code fixes the actual Cycle82/83 raw successor on the
one-block witness. -/
theorem ceQuantWitness_blockParameters_knownSample (g : Fin 1) :
    blockParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor g
      Hagi.Runtime.knownSampleScale = CEPackedStep.rawSuccessor := by
  rw [blockParameters_one_eq_ternaryCEParameters,
    Hagi.Runtime.knownSampleScale_level]
  exact CEQuantized.ceQuantWitness_ternaryCEParameters

/-- Code 31 has zero declared local certificate through its actual
observed branch.  The selected code is deliberately not identified. -/
theorem ceQuantWitness_knownSample_blockPenalty (g : Fin 1) :
    blockPenalty (canonicalBlockEquiv 1) CEQuantized.ceQuantWitnessFeatures
      CEPackedStep.rawSuccessor g Hagi.Runtime.knownSampleScale = 0 := by
  have hobs : groupObservedPenalty (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor g
      Hagi.Runtime.knownSampleScale = 0 := by
    unfold groupObservedPenalty
    rw [ceQuantWitness_blockParameters_knownSample]
    simp
  rw [blockPenalty, hobs, min_eq_left
    (groupStructuralPenalty_nonneg (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor g
      Hagi.Runtime.knownSampleScale)]

/-- Whichever code the exact finite selector chooses, its local witness
penalty is zero by the minimum bound and nonnegativity. -/
theorem ceQuantWitness_selectedGroupScale_score (g : Fin 1) :
    blockPenalty (canonicalBlockEquiv 1) CEQuantized.ceQuantWitnessFeatures
      CEPackedStep.rawSuccessor g
      (selectedGroupScales (canonicalBlockEquiv 1)
        CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor g) = 0 := by
  apply le_antisymm
  · exact (selectedGroupScales_score_le (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor g
      Hagi.Runtime.knownSampleScale).trans_eq
      (ceQuantWitness_knownSample_blockPenalty g)
  · exact blockPenalty_nonneg _ _ _ _ _

/-- The actual one-block joint selected successor strictly decreases CE.
The eligible assignment is the constant known-sample assignment; no claim
is made that the minimizer returns that assignment. -/
theorem ceQuantWitness_selectedGroupScales_strict_descent :
    Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures
        (jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
          (selectedGroupScales (canonicalBlockEquiv 1)
            CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor))) <
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures 0) := by
  apply selectedGroupScales_strict_descent_of_exists (canonicalBlockEquiv 1)
    CEQuantized.ceQuantWitnessFeatures 0 0
  · rw [CEQuantized.ceQuantWitness_range]
    norm_num
  · refine ⟨fun _ => Hagi.Runtime.knownSampleScale, ?_⟩
    rw [Fin.sum_univ_one]
    change blockPenalty (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor 0
      Hagi.Runtime.knownSampleScale < _
    rw [ceQuantWitness_knownSample_blockPenalty,
      CEQuantized.ceQuantWitness_alignment, CEQuantized.ceQuantWitness_range]
    norm_num

/-- On one block the full selected joint parameter vector is exactly the
quantized block represented by its packed payload. -/
theorem ceQuantWitness_joint_selected_eq_quantizedBlock (g : Fin 1) :
    jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
        (selectedGroupScales (canonicalBlockEquiv 1)
          CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor) =
      quantizedBlock (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor g
        (selectedGroupScales (canonicalBlockEquiv 1)
          CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor g) := by
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  ext j
  obtain ⟨⟨h, i⟩, rfl⟩ := (canonicalBlockEquiv 1).surjective j
  have hh : h = 0 := Subsingleton.elim _ _
  subst h
  rw [jointParameters_selected_eq_quantizedBlock, canonicalBlockEquiv_one_apply]

/-- A real packed block itself supplies a decoded one-block parameter
vector with the strict CE descent proved above. -/
theorem ceQuantWitness_decoded_packedBlock_strict_descent :
    ∃ decoded_w : EuclideanSpace ℝ (Fin 5),
      CEPackedStep.decodeStep
          (packedBlocks (canonicalBlockEquiv 1)
            CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor 0) =
        some decoded_w ∧
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures decoded_w) <
        Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures 0) := by
  refine ⟨jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
    (selectedGroupScales (canonicalBlockEquiv 1)
      CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor), ?_, ?_⟩
  · rw [decodeStep_packedBlocks,
      ceQuantWitness_joint_selected_eq_quantizedBlock]
  · exact ceQuantWitness_selectedGroupScales_strict_descent

end Hagi.Model.CEGroupedScale
