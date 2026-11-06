/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.TernaryCodec

/-!
# Byte-aligned packed ternary blocks with a finite dyadic scale

A block carries one of 255 finite scale codes and the existing five-trit
word from `Hagi.Runtime.TernaryCodec`.  The common level of code `k` is
exactly `(k.val + 1) / 128`; in particular, code zero denotes `1 / 128`,
not zero.  Nonpositive levels and arbitrary real-valued scales are outside
this finite family.

The logical payload is byte-aligned: the low byte is the existing
little-endian base-3 ordinal `Hagi.Energy.tritEncode`, and the high byte is
`k.val + 1`.  The `BitVec.ofFin`/`BitVec.toFin` API used here is the pinned
Lean API (`BitVec.toFin_ofFin` is `rfl`); the official API reference is
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/BitVec.html>.
The decoder rejects a missing (zero) high byte and reserved ternary bytes
243 through 255 rather than assigning them an invented meaning.

The injectivity and width results are only about uniform fixed-width codes
for this named finite family.  They are not statements about entropy,
universal compression, ABI/RAM layout, native speed, or latency.  Likewise,
`reference64BitCounter` is a named 64-bit-per-weight reference resource
model, not evidence about physical storage.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false
set_option linter.style.openClassical false

namespace Hagi.Runtime

/-- The finite metadata alphabet for positive common levels. -/
abbrev DyadicScaleCode := Fin 255

/-- The exact real common level represented by a finite scale code. -/
noncomputable def dyadicLevel (k : DyadicScaleCode) : ℝ :=
  ((k.val : ℝ) + 1) / 128

/-- Every level in this finite family is strictly positive. -/
theorem dyadicLevel_pos (k : DyadicScaleCode) : 0 < dyadicLevel k := by
  unfold dyadicLevel
  positivity

/-- Scale code zero denotes `1 / 128`, never zero. -/
theorem dyadicLevel_zero : dyadicLevel (0 : DyadicScaleCode) = 1 / 128 := by
  norm_num [dyadicLevel]

/-- The logical two-byte payload: existing ternary low byte and nonzero
scale high byte. -/
def dyadicPayload (k : DyadicScaleCode) (word : Fin 5 → Fin 3) : ℕ :=
  Hagi.Energy.tritEncode word + 256 * (k.val + 1)

/-- The logical payload fits exactly in sixteen bits. -/
theorem dyadicPayload_lt_two_pow_sixteen
    (k : DyadicScaleCode) (word : Fin 5 → Fin 3) :
    dyadicPayload k word < 2 ^ 16 := by
  have ht := Hagi.Energy.tritEncode_lt word
  have hk := k.isLt
  unfold dyadicPayload
  omega

/-- Pack the scale metadata and exact five-trit payload into sixteen bits. -/
def dyadicBlock (k : DyadicScaleCode) (word : Fin 5 → Fin 3) : BitVec 16 :=
  BitVec.ofFin ⟨dyadicPayload k word, dyadicPayload_lt_two_pow_sixteen k word⟩

set_option maxRecDepth 8192 in
/-- The existing five-trit ordinal in fact occupies the valid base-3 range,
not merely the eight-bit range.  This finite kernel computation supplements
the public `tritEncode_lt` bound without introducing another encoder. -/
theorem tritEncode_lt_243 (word : Fin 5 → Fin 3) :
    Hagi.Energy.tritEncode word < 243 := by
  decide +revert

/-- Decode a byte-aligned block only when both metadata and ternary payload
are valid. -/
def dyadicBlockDecode (block : BitVec 16) :
    Option (DyadicScaleCode × (Fin 5 → Fin 3)) :=
  if hzero : block.toFin.val / 256 = 0 then
    none
  else if _hreserved : 243 ≤ block.toFin.val % 256 then
    none
  else
    some (⟨block.toFin.val / 256 - 1, by
      have hb : block.toFin.val < 65536 := by
        simpa using block.toFin.isLt
      omega⟩, ternaryBlockDecode (block.toFin.val % 256))

/-- An absent high byte is rejected; this includes every payload below 256. -/
theorem dyadicBlockDecode_none_of_high_byte_zero (block : BitVec 16)
    (hzero : block.toFin.val / 256 = 0) : dyadicBlockDecode block = none := by
  rw [dyadicBlockDecode, dite_eq_left hzero]

/-- Reserved low-byte values 243 through 255 are rejected. -/
theorem dyadicBlockDecode_none_of_reserved_ternary (block : BitVec 16)
    (hreserved : 243 ≤ block.toFin.val % 256) : dyadicBlockDecode block = none := by
  by_cases hzero : block.toFin.val / 256 = 0
  · exact dyadicBlockDecode_none_of_high_byte_zero block hzero
  · rw [dyadicBlockDecode, dite_eq_right hzero, dite_eq_left hreserved]

/-- Truncating a block to an eight-bit-only payload removes its scale and is
therefore rejected by this decoder. -/
theorem dyadicBlockDecode_none_of_lt_256 (block : BitVec 16)
    (h : block.toFin.val < 256) : dyadicBlockDecode block = none := by
  apply dyadicBlockDecode_none_of_high_byte_zero
  omega

set_option maxRecDepth 8192 in
/-- Encoding followed by decoding recovers both the finite common scale and
all five ternary symbols. -/
theorem dyadicBlockDecode_encode (k : DyadicScaleCode) (word : Fin 5 → Fin 3) :
    dyadicBlockDecode (dyadicBlock k word) = some (k, word) := by
  have ht256 := Hagi.Energy.tritEncode_lt word
  have ht243 := tritEncode_lt_243 word
  have hdiv : dyadicPayload k word / 256 = k.val + 1 := by
    unfold dyadicPayload
    omega
  have hmod : dyadicPayload k word % 256 = Hagi.Energy.tritEncode word := by
    unfold dyadicPayload
    omega
  have hword : ternaryBlockDecode (Hagi.Energy.tritEncode word) = word := by
    funext i
    exact ternaryBlockDecode_encode word i
  have hval : (dyadicBlock k word).toFin.val = dyadicPayload k word := by
    simp only [dyadicBlock, BitVec.toFin_ofFin]
  rw [dyadicBlockDecode]
  simp only [hval, hdiv, hmod]
  rw [dite_eq_right (Nat.succ_ne_zero k.val),
    dite_eq_right (not_le_of_gt ht243)]
  apply congrArg some
  apply Prod.ext
  · apply Fin.ext
    rfl
  · exact hword

/-- Equality of logical blocks separates their high- and low-byte data. -/
theorem dyadicPayload_injective :
    Function.Injective (fun p : DyadicScaleCode × (Fin 5 → Fin 3) =>
      dyadicPayload p.1 p.2) := by
  rintro ⟨k, word⟩ ⟨l, other⟩ h
  have ht := Hagi.Energy.tritEncode_lt word
  have ho := Hagi.Energy.tritEncode_lt other
  have hk := k.isLt
  have hl := l.isLt
  change dyadicPayload k word = dyadicPayload l other at h
  unfold dyadicPayload at h
  have htrit : Hagi.Energy.tritEncode word = Hagi.Energy.tritEncode other := by
    omega
  have hscale : k.val = l.val := by omega
  apply Prod.ext
  · exact Fin.ext hscale
  · exact Hagi.Energy.tritEncode_injective htrit

/-- The current sixteen-bit embedding is injective on the entire named
finite family. -/
theorem dyadicBlock_injective :
    Function.Injective (fun p : DyadicScaleCode × (Fin 5 → Fin 3) =>
      dyadicBlock p.1 p.2) := by
  intro p q h
  apply dyadicPayload_injective
  exact congrArg (fun b : BitVec 16 => b.toFin.val) h

/-- No uniform fifteen-bit code can distinguish all `255 * 3^5 = 61965`
scale/word pairs.  This is fixed-width optimality for this family only. -/
theorem dyadicBlock_fifteen_bit_impossible :
    ¬ ∃ f : DyadicScaleCode × (Fin 5 → Fin 3) → Fin (2 ^ 15),
      Function.Injective f := by
  rintro ⟨f, hf⟩
  have hcard := Fintype.card_le_of_injective f hf
  norm_num [DyadicScaleCode, Fintype.card_fun] at hcard

/-- In particular, dropping or truncating the metadata to an eight-bit-only
uniform code cannot represent this finite family. -/
theorem dyadicBlock_eight_bit_impossible :
    ¬ ∃ f : DyadicScaleCode × (Fin 5 → Fin 3) → Fin (2 ^ 8),
      Function.Injective f := by
  rintro ⟨f, hf⟩
  have hcard := Fintype.card_le_of_injective f hf
  norm_num [DyadicScaleCode, Fintype.card_fun] at hcard

/-- A nondegenerate sample containing positive, negative, middle, and two
padding-zero branches. -/
def knownSampleWord : Fin 5 → Fin 3 := ![2, 0, 1, 1, 1]

/-- The scale code whose exact common level is one quarter. -/
def knownSampleScale : DyadicScaleCode := ⟨31, by decide⟩

/-- The known scale decodes to exactly `1 / 4`. -/
theorem knownSampleScale_level : dyadicLevel knownSampleScale = 1 / 4 := by
  norm_num [dyadicLevel, knownSampleScale]

/-- The existing five-place little-endian ordinal of the known word. -/
theorem knownSample_trit_payload : Hagi.Energy.tritEncode knownSampleWord = 119 := by
  decide

/-- The combined logical payload is `119 + 32 * 256 = 8311`. -/
theorem knownSample_payload : dyadicPayload knownSampleScale knownSampleWord = 8311 := by
  norm_num [dyadicPayload, knownSampleScale, knownSample_trit_payload]

/-- Pointwise use of the existing value decoder gives the exact real vector,
including the explicit middle and padding-zero branches. -/
theorem knownSample_reconstruction :
    (fun i => ternaryValueDecode (dyadicLevel knownSampleScale) (knownSampleWord i)) =
      ![1 / 4, -1 / 4, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    norm_num [ternaryValueDecode, dyadicLevel, knownSampleScale, knownSampleWord]

/-- Decoding the packed known sample recovers its exact common-level values;
the `Option` result remains visible and no fallback sample is invented. -/
theorem knownSample_decode_reconstruction :
    (dyadicBlockDecode (dyadicBlock knownSampleScale knownSampleWord)).map
      (fun p => fun i => ternaryValueDecode (dyadicLevel p.1) (p.2 i)) =
        some ![1 / 4, -1 / 4, 0, 0, 0] := by
  rw [dyadicBlockDecode_encode]
  exact congrArg some knownSample_reconstruction

/-- A reference counter charging sixty-four bits for each of five weights. -/
def reference64BitCounter : ℕ := 5 * 64

/-- The named reference counter is 320 bits. -/
theorem reference64BitCounter_eq : reference64BitCounter = 320 := by
  norm_num [reference64BitCounter]

/-- The sixteen-bit block is smaller than the named reference counter; this
is only a comparison within the documented reference resource model. -/
theorem sixteen_lt_reference64BitCounter : 16 < reference64BitCounter := by
  norm_num [reference64BitCounter]

end Hagi.Runtime
