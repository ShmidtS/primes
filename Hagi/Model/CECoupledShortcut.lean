/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEJointScale

/-!
# Zero-certificate shortcut with exact coupled fallback

A supplied complete scale assignment is used when its coupled penalty is zero;
otherwise Cycle85's complete coupled minimizer is retained.  Thus both branches
minimize the same declared coupled bound over every complete assignment.  Only
the zero branch is a one-candidate logical probe; the fallback still performs
the full exponential finite selection.

The results concern logical scores, exact raw/joint equalities and conditional
actual CE descent.  They do not assert native execution speed, an actual CE
minimum, ordering of different successors, generalization, physical memory
savings, or support for arbitrary-dimensional padding.  The proof and codec
patterns adapt `CEJointScale`; strict raw descent comes from `CEDescent`.
-/

set_option relaxedAutoImplicit false
set_option linter.style.openClassical false

open scoped Matrix

namespace Hagi.Model.CECoupledShortcut

open Hagi.Model
open Hagi.Model.CEGroupedScale
open Hagi.Model.CEJointScale

/-- Use a zero-certificate complete candidate, or the exact full coupled
minimizer when its certificate is nonzero. -/
noncomputable def shortcutScales {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode) :
    Fin G → Hagi.Runtime.DyadicScaleCode := by
  classical
  exact if coupledPenalty e X w fast = 0 then fast else selectedCoupledScales e X w

/-- A zero fast candidate is returned unchanged. -/
theorem shortcutScales_eq_fast_of_coupledPenalty_eq_zero {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode)
    (h : coupledPenalty e X w fast = 0) : shortcutScales e X w fast = fast := by
  unfold shortcutScales
  rw [ite_eq_left h]

/-- A nonzero fast candidate selects the faithful full coupled fallback. -/
theorem shortcutScales_eq_selectedCoupled_of_coupledPenalty_ne_zero {G : ℕ}
    {V : Type} [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode)
    (h : coupledPenalty e X w fast ≠ 0) :
    shortcutScales e X w fast = selectedCoupledScales e X w := by
  unfold shortcutScales
  rw [ite_eq_right h]

/-- Every represented level of the shortcut assignment is positive. -/
theorem shortcutScales_level_pos {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode) (g : Fin G) :
    0 < Hagi.Runtime.dyadicLevel (shortcutScales e X w fast g) :=
  Hagi.Runtime.dyadicLevel_pos _

/-- The shortcut minimizes the exact declared coupled bound over every complete
alternative: zero and nonnegativity suffice in the fast branch; otherwise the
full coupled minimum applies. -/
theorem shortcutScales_score_le {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast alternative : Fin G → Hagi.Runtime.DyadicScaleCode) :
    coupledPenalty e X w (shortcutScales e X w fast) ≤
      coupledPenalty e X w alternative := by
  by_cases h : coupledPenalty e X w fast = 0
  · rw [shortcutScales_eq_fast_of_coupledPenalty_eq_zero e X w fast h, h]
    exact coupledPenalty_nonneg e X w alternative
  · rw [shortcutScales_eq_selectedCoupled_of_coupledPenalty_ne_zero e X w fast h]
    exact selectedCoupledScales_score_le e X w alternative

/-- The shortcut score equals the full coupled minimum, without identifying
the selected assignments or their actual CE values. -/
theorem shortcutScales_score_eq_selectedCoupled {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode) :
    coupledPenalty e X w (shortcutScales e X w fast) =
      coupledPenalty e X w (selectedCoupledScales e X w) := by
  apply le_antisymm
  · exact shortcutScales_score_le e X w fast (selectedCoupledScales e X w)
  · exact selectedCoupledScales_score_le e X w (shortcutScales e X w fast)

/-- The shortcut score retains Cycle85's comparison with the selected separable
score; this is not an ordering of actual cross-entropy values. -/
theorem shortcutScales_le_selectedGroupScales_total {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode) :
    coupledPenalty e X w (shortcutScales e X w fast) ≤
      ∑ g, blockPenalty e X w g (selectedGroupScales e X w g) := by
  rw [shortcutScales_score_eq_selectedCoupled]
  exact selectedCoupledScales_le_selectedGroupScales_total e X w

/-- Actual joint CE after the shortcut is bounded by raw CE plus its exact
coupled certificate. -/
theorem ceOneHot_joint_shortcut_le_coupledPenalty {G : ℕ} {V : Type} [Fintype V]
    [Nonempty V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode) :
    Hagi.ceOneHot t (ceLogits X
      (jointParameters e w (shortcutScales e X w fast))) ≤
      Hagi.ceOneHot t (ceLogits X w) +
        coupledPenalty e X w (shortcutScales e X w fast) :=
  ceOneHot_joint_le_coupledPenalty e X t w (shortcutScales e X w fast)

/-- A zero supplied candidate makes every joint shortcut logit equal to its
raw logit; the separable-to-observed implication stays inside Cycle85's lemma. -/
theorem ceLogits_joint_shortcut_eq_of_coupledPenalty_eq_zero {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode)
    (h : coupledPenalty e X w fast = 0) (v : V) :
    ceLogits X (jointParameters e w (shortcutScales e X w fast)) v =
      ceLogits X w v := by
  rw [shortcutScales_eq_fast_of_coupledPenalty_eq_zero e X w fast h]
  exact ceLogits_joint_eq_of_coupledPenalty_eq_zero e X w fast h v

/-- A zero supplied candidate gives exact equality of actual joint and raw CE. -/
theorem ceOneHot_joint_shortcut_eq_of_coupledPenalty_eq_zero {G : ℕ} {V : Type}
    [Fintype V] [Nonempty V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode)
    (h : coupledPenalty e X w fast = 0) :
    Hagi.ceOneHot t (ceLogits X
      (jointParameters e w (shortcutScales e X w fast))) =
      Hagi.ceOneHot t (ceLogits X w) := by
  rw [shortcutScales_eq_fast_of_coupledPenalty_eq_zero e X w fast h]
  exact ceOneHot_joint_eq_of_coupledPenalty_eq_zero e X t w fast h

/-- A zero candidate at the actual raw safe successor inherits Cycle81's strict
actual CE descent directly, with no separate eligibility premise. -/
theorem shortcutScales_strict_descent_of_coupledPenalty_eq_zero {G : ℕ}
    {V : Type} [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (θ : EuclideanSpace ℝ (Fin (5 * G)))
    (t : V) (fast : Fin G → Hagi.Runtime.DyadicScaleCode)
    (hr : 0 < ceStepRange X θ t)
    (h : coupledPenalty e X (ceNextParameters X θ t (safeStepSize X θ t)) fast = 0) :
    Hagi.ceOneHot t (ceLogits X
      (jointParameters e (ceNextParameters X θ t (safeStepSize X θ t))
        (shortcutScales e X (ceNextParameters X θ t (safeStepSize X θ t)) fast))) <
      Hagi.ceOneHot t (ceLogits X θ) := by
  rw [ceOneHot_joint_shortcut_eq_of_coupledPenalty_eq_zero e X t
    (ceNextParameters X θ t (safeStepSize X θ t)) fast h]
  have hsafe := ceOneHot_safeStep_lt X θ t hr
  change Hagi.ceOneHot t (ceLogits X
    (ceNextParameters X θ t (safeStepSize X θ t))) < _ at hsafe
  exact hsafe

/-- With an explicit coupled-eligible assignment, either the zero fast branch
or the faithful selected fallback gives strict actual CE descent. -/
theorem shortcutScales_strict_descent_of_exists {G : ℕ} {V : Type} [Fintype V]
    [Nonempty V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (θ : EuclideanSpace ℝ (Fin (5 * G)))
    (t : V) (fast : Fin G → Hagi.Runtime.DyadicScaleCode)
    (hr : 0 < ceStepRange X θ t)
    (h : ∃ scales : Fin G → Hagi.Runtime.DyadicScaleCode,
      coupledPenalty e X (ceNextParameters X θ t (safeStepSize X θ t)) scales <
        2 * (ceAlignment X θ t) ^ 2 / (ceStepRange X θ t) ^ 2) :
    Hagi.ceOneHot t (ceLogits X
      (jointParameters e (ceNextParameters X θ t (safeStepSize X θ t))
        (shortcutScales e X (ceNextParameters X θ t (safeStepSize X θ t)) fast))) <
      Hagi.ceOneHot t (ceLogits X θ) := by
  by_cases hfast : coupledPenalty e X
      (ceNextParameters X θ t (safeStepSize X θ t)) fast = 0
  · exact shortcutScales_strict_descent_of_coupledPenalty_eq_zero e X θ t fast hr hfast
  · rw [shortcutScales_eq_selectedCoupled_of_coupledPenalty_ne_zero e X
      (ceNextParameters X θ t (safeStepSize X θ t)) fast hfast]
    exact selectedCoupledScales_strict_descent_of_exists e X θ t hr h

/-- The actual payload carries the shortcut level and the raw five-cell word
encoded at that same level, including in the zero fast branch. -/
noncomputable def packedShortcutScales {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode) : Fin G → BitVec 16 := fun g =>
  Hagi.Runtime.dyadicBlock (shortcutScales e X w fast g) (fun i =>
    Hagi.Runtime.ternaryValueEncode
      (Hagi.Runtime.dyadicLevel (shortcutScales e X w fast g))
      (blockWeights e w g i))

/-- Decoding the actual shortcut payload returns exactly its quantized block;
malformed external inputs remain outside this encoder round-trip theorem. -/
theorem decodeStep_packedShortcutScales {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G)) (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode) (g : Fin G) :
    CEPackedStep.decodeStep (packedShortcutScales e X w fast g) =
      some (quantizedBlock e w g (shortcutScales e X w fast g)) := by
  unfold CEPackedStep.decodeStep packedShortcutScales quantizedBlock
  rw [Hagi.Runtime.dyadicBlockDecode_encode]
  simp only [Option.map_some]
  congr 1
  ext i
  exact Hagi.Runtime.ternaryValueDecode_encode _ _

/-- Each decoded block coordinate agrees with the joint shortcut parameter at
the coordinate supplied by the explicit equivalence. -/
theorem jointParameters_shortcut_eq_quantizedBlock {G : ℕ} {V : Type}
    [Fintype V] (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (w : EuclideanSpace ℝ (Fin (5 * G)))
    (fast : Fin G → Hagi.Runtime.DyadicScaleCode) (g : Fin G) (i : Fin 5) :
    (jointParameters e w (shortcutScales e X w fast)).ofLp (e (g, i)) =
      (quantizedBlock e w g (shortcutScales e X w fast g)).ofLp i := by
  rw [jointParameters_own]
  rfl

/-- On the one-block witness the explicit known-sample candidate takes the zero
branch, so the shortcut is exactly that supplied constant assignment. -/
theorem ceQuantWitness_shortcutScales_eq_knownSample :
    shortcutScales (canonicalBlockEquiv 1) CEQuantized.ceQuantWitnessFeatures
      CEPackedStep.rawSuccessor (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale) =
      (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale) := by
  exact shortcutScales_eq_fast_of_coupledPenalty_eq_zero _ _ _ _
    ceQuantWitness_knownSample_coupledPenalty

/-- The explicit one-block shortcut joint vector is the actual raw successor. -/
theorem ceQuantWitness_jointParameters_shortcut :
    jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
      (shortcutScales (canonicalBlockEquiv 1) CEQuantized.ceQuantWitnessFeatures
        CEPackedStep.rawSuccessor
        (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale)) =
      CEPackedStep.rawSuccessor := by
  rw [ceQuantWitness_shortcutScales_eq_knownSample]
  exact ceQuantWitness_jointParameters_knownSample

/-- The generic zero fast-path theorem gives actual strict CE descent for the
explicit one-block shortcut, below the zero-parameter CE. -/
theorem ceQuantWitness_shortcutScales_strict_descent :
    Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures
      (jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
        (shortcutScales (canonicalBlockEquiv 1) CEQuantized.ceQuantWitnessFeatures
          CEPackedStep.rawSuccessor
          (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale)))) <
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures 0) := by
  apply shortcutScales_strict_descent_of_coupledPenalty_eq_zero (canonicalBlockEquiv 1)
    CEQuantized.ceQuantWitnessFeatures 0 0
    (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale)
  · rw [CEQuantized.ceQuantWitness_range]
    norm_num
  · exact ceQuantWitness_knownSample_coupledPenalty

/-- On one block the complete explicit-shortcut vector equals the block encoded
by its own shortcut payload. -/
theorem ceQuantWitness_joint_shortcut_eq_quantizedBlock (g : Fin 1) :
    jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
      (shortcutScales (canonicalBlockEquiv 1) CEQuantized.ceQuantWitnessFeatures
        CEPackedStep.rawSuccessor
        (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale)) =
      quantizedBlock (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor g
        (shortcutScales (canonicalBlockEquiv 1) CEQuantized.ceQuantWitnessFeatures
          CEPackedStep.rawSuccessor
          (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale) g) := by
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  ext j
  obtain ⟨⟨h, i⟩, rfl⟩ := (canonicalBlockEquiv 1).surjective j
  have hh : h = 0 := Subsingleton.elim _ _
  subst h
  rw [jointParameters_shortcut_eq_quantizedBlock, canonicalBlockEquiv_one_apply]

/-- The actual explicit-shortcut packed payload has a decoded parameter vector
with strict actual CE descent on the one-block witness. -/
theorem ceQuantWitness_decoded_packedShortcutScales_strict_descent :
    ∃ decoded_w : EuclideanSpace ℝ (Fin 5),
      CEPackedStep.decodeStep
        (packedShortcutScales (canonicalBlockEquiv 1)
          CEQuantized.ceQuantWitnessFeatures CEPackedStep.rawSuccessor
          (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale) 0) = some decoded_w ∧
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures decoded_w) <
        Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures 0) := by
  refine ⟨jointParameters (canonicalBlockEquiv 1) CEPackedStep.rawSuccessor
    (shortcutScales (canonicalBlockEquiv 1) CEQuantized.ceQuantWitnessFeatures
      CEPackedStep.rawSuccessor
      (fun _ : Fin 1 => Hagi.Runtime.knownSampleScale)), ?_, ?_⟩
  · rw [decodeStep_packedShortcutScales, ceQuantWitness_joint_shortcut_eq_quantizedBlock]
  · exact ceQuantWitness_shortcutScales_strict_descent

end Hagi.Model.CECoupledShortcut
