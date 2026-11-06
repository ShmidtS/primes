/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CEQuantized
import Hagi.Runtime.DyadicTernary

/-!
# The quantized safe step as an actual packed parameter payload

This module joins the quality-certified successor to the finite common-scale
codec: the 16-bit object encodes the same parameters whose CE strictly
decreases after quantization. Invalid blocks remain `None`. The witness is
one explicit post-training payload, not a whole-training-memory result or
an optimality claim for architecture, hardware, or held-out data.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.CEPackedStep

/-- Actual safe successor used to form the encoded block. -/
noncomputable def rawSuccessor : EuclideanSpace ℝ (Fin 5) :=
  ceNextParameters CEQuantized.ceQuantWitnessFeatures 0 0
    (safeStepSize CEQuantized.ceQuantWitnessFeatures 0 0)

/-- Real-to-trit conversion of the actual successor at the represented
common level. -/
noncomputable def encodedWord : Fin 5 → Fin 3 := fun j =>
  Hagi.Runtime.ternaryValueEncode
    (Hagi.Runtime.dyadicLevel Hagi.Runtime.knownSampleScale) (rawSuccessor.ofLp j)

/-- Actual packed sixteen-bit block of that successor. -/
noncomputable def packedStep : BitVec 16 :=
  Hagi.Runtime.dyadicBlock Hagi.Runtime.knownSampleScale encodedWord

/-- Decode a payload, preserving invalid-input rejection. -/
noncomputable def decodeStep (block : BitVec 16) :
    Option (EuclideanSpace ℝ (Fin 5)) :=
  (Hagi.Runtime.dyadicBlockDecode block).map fun p =>
    WithLp.toLp 2 (fun j =>
      Hagi.Runtime.ternaryValueDecode (Hagi.Runtime.dyadicLevel p.1) (p.2 j))

/-- The actual update encodes the same positive/negative/zero word as the
codec witness, not an unrelated exemplar. -/
theorem encodedWord_eq_known : encodedWord = Hagi.Runtime.knownSampleWord := by
  change (fun j => Hagi.Runtime.ternaryValueEncode
    (Hagi.Runtime.dyadicLevel Hagi.Runtime.knownSampleScale)
      (rawSuccessor.ofLp j)) = Hagi.Runtime.knownSampleWord
  rw [Hagi.Runtime.knownSampleScale_level]
  change (fun j => Hagi.Runtime.ternaryValueEncode (1 / 4)
    ((ceNextParameters CEQuantized.ceQuantWitnessFeatures 0 0
      (safeStepSize CEQuantized.ceQuantWitnessFeatures 0 0)).ofLp j)) =
    Hagi.Runtime.knownSampleWord
  rw [CEQuantized.ceQuantWitness_safeSuccessor]
  funext j
  fin_cases j <;>
    norm_num [Hagi.Runtime.ternaryValueEncode, Hagi.Runtime.knownSampleWord]

/-- The byte-level object itself carries payload `8311`. -/
theorem packedStep_payload : packedStep.toFin.val = 8311 := by
  change Hagi.Runtime.dyadicPayload Hagi.Runtime.knownSampleScale encodedWord = 8311
  rw [encodedWord_eq_known]
  exact Hagi.Runtime.knownSample_payload

/-- The packed bytes decode to the actual ternary successor, not to a
freshly chosen parameter vector. -/
theorem decodeStep_packedStep : decodeStep packedStep =
    some (CEQuantized.ternaryCEParameters (1 / 4) rawSuccessor) := by
  unfold decodeStep packedStep
  rw [Hagi.Runtime.dyadicBlockDecode_encode]
  simp only [Option.map_some]
  congr 1
  ext j
  change Hagi.Runtime.ternaryValueDecode
    (Hagi.Runtime.dyadicLevel Hagi.Runtime.knownSampleScale)
    (Hagi.Runtime.ternaryValueEncode
      (Hagi.Runtime.dyadicLevel Hagi.Runtime.knownSampleScale)
      (rawSuccessor.ofLp j)) =
    Hagi.Runtime.qTern (1 / 4) (rawSuccessor.ofLp j)
  rw [Hagi.Runtime.ternaryValueDecode_encode,
    Hagi.Runtime.knownSampleScale_level]

/-- The valid packed payload has a decoded parameter witness with actual
strict CE descent. This is one explicit post-training result, not a claim
about full training memory or universal model architecture optimality. -/
theorem decoded_packedStep_strict_descent :
    ∃ w : EuclideanSpace ℝ (Fin 5), decodeStep packedStep = some w ∧
      Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures w) <
        Hagi.ceOneHot 0 (ceLogits CEQuantized.ceQuantWitnessFeatures 0) := by
  refine ⟨CEQuantized.ternaryCEParameters (1 / 4) rawSuccessor,
    decodeStep_packedStep, ?_⟩
  exact CEQuantized.ceQuantWitness_strict_descent

end Hagi.Model.CEPackedStep
