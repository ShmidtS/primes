/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEHeldout

set_option linter.style.header false

/-!
# Logical codebook width together with the selected packed CE bound

The cardinality proofs adapt the checked `.tmp/ResearchCEStorage.lean`
probe.  They bound the logical fixed-width payload of the existing joint
codec; they make no physical-storage or optimality assertion.
-/

set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

open scoped Matrix

namespace Hagi.Model.CEStorageBound

open Hagi.Model

/-- The actual packed group codes inject into sixteen-bit words. -/
theorem jointCode_injective {G : ℕ} :
    Function.Injective (fun (c : CEHeldout.JointCode G) => fun g =>
      FinEnum.equiv (Hagi.Runtime.dyadicBlock (c g).1 (c g).2)) := by
  intro a b h
  funext g
  apply Hagi.Runtime.dyadicBlock_injective
  exact FinEnum.equiv.injective (congrFun h g)

/-- The joint codebook fits within the existing logical payload width. -/
theorem card_jointCode_le_payload (G : ℕ) :
    Fintype.card (CEHeldout.JointCode G) ≤
      2 ^ CEGroupedScale.groupPayloadBits G := by
  let f : CEHeldout.JointCode G → Fin G → Fin (2 ^ 16) := fun c g =>
    FinEnum.equiv (Hagi.Runtime.dyadicBlock (c g).1 (c g).2)
  have hf : Function.Injective f := jointCode_injective
  have hcard := Fintype.card_le_of_injective f hf
  calc
    Fintype.card (CEHeldout.JointCode G) = 61965 ^ G :=
      CEHeldout.card_jointCode G
    _ ≤ (2 ^ 16) ^ G := by
      simpa [CEHeldout.JointCode, Fintype.card_fun] using hcard
    _ = 2 ^ CEGroupedScale.groupPayloadBits G := by
      simp [CEGroupedScale.groupPayloadBits, pow_mul]

/-- Base-two logarithmic codebook cardinality respects the same width. -/
theorem log_card_jointCode_le_payload (G : ℕ) :
    Real.log (Fintype.card (CEHeldout.JointCode G) : ℝ) / Real.log 2 ≤
      (CEGroupedScale.groupPayloadBits G : ℝ) := by
  have hcard := card_jointCode_le_payload G
  have hreal : ((Fintype.card (CEHeldout.JointCode G) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ CEGroupedScale.groupPayloadBits G := by
    exact_mod_cast hcard
  have hpos : (0 : ℝ) < Fintype.card (CEHeldout.JointCode G) := by
    exact_mod_cast Fintype.card_pos
  have hlog := Real.log_le_log hpos hreal
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [Real.log_pow] at hlog
  apply (div_le_iff₀ hlog2).2
  simpa [mul_comm] using hlog

/-- One selected scale assignment simultaneously supplies valid packed
blocks, its decoded joint update, the CE increase bound, and the logical
codebook-width bound. -/
theorem selectedPacked_ce_and_codebook_bits {G : ℕ} {V : Type}
    [Fintype V] [Nonempty V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ) (t : V)
    (w : EuclideanSpace ℝ (Fin (5 * G))) :
    (∀ g : Fin G,
      CEPackedStep.decodeStep (CEGroupedScale.packedBlocks e X w g) =
        some (CEGroupedScale.quantizedBlock e w g
          (CEGroupedScale.selectedGroupScales e X w g))) ∧
    CEHeldout.decodeJoint e
        (CEHeldout.encodeJoint e w (CEGroupedScale.selectedGroupScales e X w)) =
      CEGroupedScale.jointParameters e w
        (CEGroupedScale.selectedGroupScales e X w) ∧
    Hagi.ceOneHot t (Hagi.Model.ceLogits X
        (CEHeldout.decodeJoint e
          (CEHeldout.encodeJoint e w (CEGroupedScale.selectedGroupScales e X w)))) ≤
      Hagi.ceOneHot t (Hagi.Model.ceLogits X w) +
        ∑ g, CEGroupedScale.blockPenalty e X w g
          (CEGroupedScale.selectedGroupScales e X w g) ∧
    Real.log (Fintype.card (CEHeldout.JointCode G) : ℝ) / Real.log 2 ≤
      (CEGroupedScale.groupPayloadBits G : ℝ) := by
  let scales := CEGroupedScale.selectedGroupScales e X w
  let code := CEHeldout.encodeJoint e w scales
  change (∀ g : Fin G,
      CEPackedStep.decodeStep (CEGroupedScale.packedBlocks e X w g) =
        some (CEGroupedScale.quantizedBlock e w g (scales g))) ∧
    CEHeldout.decodeJoint e code = CEGroupedScale.jointParameters e w scales ∧
    Hagi.ceOneHot t (Hagi.Model.ceLogits X (CEHeldout.decodeJoint e code)) ≤
      Hagi.ceOneHot t (Hagi.Model.ceLogits X w) +
        ∑ g, CEGroupedScale.blockPenalty e X w g (scales g) ∧
    Real.log (Fintype.card (CEHeldout.JointCode G) : ℝ) / Real.log 2 ≤
      (CEGroupedScale.groupPayloadBits G : ℝ)
  have hdecode : CEHeldout.decodeJoint e code =
      CEGroupedScale.jointParameters e w scales :=
    CEHeldout.decodeJoint_encodeJoint e w scales
  refine ⟨?_, hdecode, ?_, log_card_jointCode_le_payload G⟩
  · intro g
    exact CEGroupedScale.decodeStep_packedBlocks e X w g
  · rw [hdecode]
    exact CEGroupedScale.ceOneHot_joint_le_blockPenalties e X t w scales

end Hagi.Model.CEStorageBound
