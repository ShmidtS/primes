/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.TernaryExact

set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# Exact semantic codec for five ternary samples

A five-place group in this codec has one common real scale `level`.
The group scale is metadata shared by the whole group, not an extra symbol
in the 8-bit alphabet payload. The five symbols themselves are encoded by
the existing injective `Hagi.Energy.tritEncode`; this module does not define
another base-3 packing polynomial.

Douglas Jones' overview of balanced ternary notation is useful background:
<http://homepage.divms.uiowa.edu/~jones/ternary/numbers.shtml>. The proofs
here depend only on the actual local definitions and lemmas.

The results concern this fixed block representation alone. They establish
neither heap/ABI/layout behavior nor storage-latency or global model-size
optimality. Decoding recovers each quantized `qTern level value`, never the
raw real input, and does not attach special validity to the unused payloads
243 through 255.
-/

namespace Hagi.Runtime

open scoped Classical

/-- Encode the exact branch of `Hagi.Energy.roundTern (value / level)` as a
three-valued symbol: negative, middle, and positive map to `0`, `1`, `2`. -/
noncomputable def ternaryValueEncode (level value : ℝ) : Fin 3 :=
  if 1 / 2 < value / level then 2
  else if value / level < -1 / 2 then 0 else 1

/-- Decode a symbol as an offset from the common group level. -/
noncomputable def ternaryValueDecode (level : ℝ) (code : Fin 3) : ℝ :=
  level * ((code.val : ℝ) - 1)

/-- Value decoding exactly reconstructs the saturating quantizer, including
its branches at a zero or negative level; no positivity premise is needed. -/
theorem ternaryValueDecode_encode (level value : ℝ) :
    ternaryValueDecode level (ternaryValueEncode level value) = qTern level value := by
  unfold ternaryValueDecode ternaryValueEncode qTern Hagi.Energy.roundTern
  by_cases hpos : (1 : ℝ) / 2 < value / level
  · rw [ite_eq_left hpos, ite_eq_left hpos]
    norm_num
  · rw [ite_eq_right hpos, ite_eq_right hpos]
    by_cases hneg : value / level < -(1 : ℝ) / 2
    · rw [ite_eq_left hneg, ite_eq_left hneg]
      norm_num
    · rw [ite_eq_right hneg, ite_eq_right hneg]
      norm_num

/-- One bit cannot separately encode all three ternary symbols. This is a
statement about that alphabet, not a general model-compression claim. -/
theorem ternaryOneBit_impossible : ¬ ∃ f : Fin 3 → Fin 2, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hcard := Fintype.card_le_of_injective f hf
  norm_num at hcard

/-- The existing base-3 encoding of a five-symbol word as an eight-bit word. -/
def ternaryByteBlock (t : Fin 5 → Fin 3) : BitVec 8 :=
  BitVec.ofFin ⟨Hagi.Energy.tritEncode t, Hagi.Energy.tritEncode_lt t⟩

/-- The typed byte block inherits injectivity from `tritEncode_injective`. -/
theorem ternaryByteBlock_injective : Function.Injective ternaryByteBlock := by
  intro t s h
  apply Hagi.Energy.tritEncode_injective
  exact congrArg (fun b : BitVec 8 => b.toFin.val) h

/-- Read a little-endian base-3 digit from a numeric payload. The modulus
bound supplies the `Fin 3` witness directly. -/
def ternaryBlockDecode (payload : ℕ) : Fin 5 → Fin 3 :=
  fun i => ⟨payload / 3 ^ (i : ℕ) % 3, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
/-- Little-endian digit lookup inverts the existing five-trit encoder. -/
theorem ternaryBlockDecode_encode (t : Fin 5 → Fin 3) (i : Fin 5) :
    ternaryBlockDecode (Hagi.Energy.tritEncode t) i = t i := by
  decide +revert

/-- Seven-bit uniform block payloads cannot distinguish all 243 five-trit
words. This says nothing about arbitrary entropy or compression schemes. -/
theorem ternaryBlock_seven_bit_impossible :
    ¬ ∃ f : (Fin 5 → Fin 3) → Fin (2 ^ 7), Function.Injective f := by
  rintro ⟨f, hf⟩
  have hcard := Fintype.card_le_of_injective f hf
  norm_num [Fintype.card_fun] at hcard

/-- Encode five real samples with their common level into one byte block.
The level itself is shared metadata and is not part of the byte alphabet. -/
noncomputable def packedTernarySamples (level : ℝ) (values : Fin 5 → ℝ) : BitVec 8 :=
  ternaryByteBlock (fun i => ternaryValueEncode level (values i))

/-- Pointwise block reconstruction gives the quantized sample, not raw input. -/
theorem packedTernarySamples_decode_point (level : ℝ) (values : Fin 5 → ℝ)
    (i : Fin 5) :
    ternaryValueDecode level
      (ternaryBlockDecode ((packedTernarySamples level values).toFin.val) i) =
      qTern level (values i) := by
  change ternaryValueDecode level
    (ternaryBlockDecode (Hagi.Energy.tritEncode
      (fun j => ternaryValueEncode level (values j))) i) = qTern level (values i)
  rw [ternaryBlockDecode_encode, ternaryValueDecode_encode]

end Hagi.Runtime
