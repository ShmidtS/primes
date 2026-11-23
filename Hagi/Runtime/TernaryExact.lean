/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Energy.Ternary
import Hagi.Architecture.LiveDelta
set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# The ternary saturation bridge — the actual quantizer's global error

The actual ternary quantizer `qTern` (nearest-grid rounding on
`{-1, 0, +1}·s`, saturating: `|x| > 3s/2` clips to `±s`) splits
the error budget:

* in-range coordinates (`|x| ≤ 3s/2`): error `≤ s/2`
  (`qTern_error_in`);
* out-of-range coordinates: error exactly `|x| − s`
  (`qTern_error_out`), collected in the saturation tail
  `satTail`.

`ternary_split_bound` decomposes the total squared error
exactly; `quant_energy_bridge_saturation` gives the global
bound `ΔE ≤ κ·(√n·s/2 + √satTail)` with no in-range assumption;
`no_saturation_recover` derives the half-step hypothesis when
nothing saturates.
-/

namespace Hagi.Runtime

open Finset Real
open scoped Classical

/-! ## The actual (saturating) quantizer and the range split -/

/-- The ACTUAL ternary quantizer of the format: nearest-grid
rounding on `{-1, 0, +1}` with per-group scale `s`, saturated —
`qTern s x = s · roundTern (x / s)`, so any `x` with
`|x| > 3s/2` clips to `±s`. -/
noncomputable def qTern (s x : ℝ) : ℝ := s * ((roundTern (x / s) : ℝ))

/-- A coordinate is **in range** for the ternary grid at scale
`s` when nearest-grid rounding covers it: `|x| ≤ 3s/2` (within
half a step of the endpoint level `s`). -/
def ternInRange (s x : ℝ) : Prop := |x| ≤ 3 * s / 2

/-- **The saturation tail** — the measured saturation mass of a
weight vector: the sum of squared overshoots
`Σ_{|w i| > 3s/2} (|w i| − s)²` over the out-of-range
coordinates. Computable from a checkpoint (see the module
docstring: the pre-quantization diagnostic). -/
noncomputable def satTail (s : ℝ) {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => ¬ ternInRange s (w i)), (|w i| - s) ^ 2

/-! ## Pointwise error: in-range vs saturated -/

/-- **In-range coordinates** keep the half-step guarantee: for
`|x| ≤ 3s/2` the saturating quantizer's error is at most `s/2`
(this is `roundTern_error_scaled` restated for `qTern`). -/
theorem qTern_error_in (s x : ℝ) (hs : 0 < s) (hx : ternInRange s x) :
    |x - qTern s x| ≤ s / 2 :=
  roundTern_error_scaled s x hs hx

/-- For `|x| > 3s/2` the quantizer clips to the endpoint `±s`,
so the error is exactly `|x| - s`. -/
theorem qTern_error_out (s x : ℝ) (hs : 0 < s) (hx : ¬ ternInRange s x) :
    |x - qTern s x| = |x| - s := by
  have hout : 3 * s / 2 < |x| := not_le.mp hx
  simp only [qTern, roundTern]
  rcases lt_or_ge x 0 with hx0 | hx0
  · -- x < 0: clips to −s
    have hxlt : x < -3 * s / 2 := by
      rw [abs_of_neg hx0] at hout; linarith
    have hsx : x / s < -1 / 2 := by
      rw [div_lt_iff₀ hs]; linarith
    rw [ite_eq_right (by linarith : ¬ (1 / 2 < x / s)), ite_eq_left hsx]
    push_cast
    rw [show x - s * (-1 : ℝ) = x + s by ring,
      show |x| = -x from abs_of_neg hx0,
      abs_of_neg (by linarith : x + s < 0)]
    ring
  · -- 0 ≤ x, in fact x > 3s/2 > 0: clips to +s
    have hxgt : 3 * s / 2 < x := by
      rw [abs_of_nonneg hx0] at hout; linarith
    have hxpos : 0 < x := by linarith
    have hsx : 1 / 2 < x / s := by
      rw [lt_div_iff₀ hs]; linarith
    rw [ite_eq_left hsx]
    push_cast
    rw [show x - s * (1 : ℝ) = x - s by ring,
      show |x| = x from abs_of_pos hxpos,
      abs_of_nonneg (by linarith : 0 ≤ x - s)]

/-! ## The exact split of the total squared error -/

/-- The exact decomposition of the total squared error into
the in-range part and the saturation tail:
`∑ i, (w i - qTern s (w i)) ^ 2 = Σ_in … + satTail s w`. -/
theorem ternary_split_bound (s : ℝ) {n : ℕ} (hs : 0 < s) (w : Fin n → ℝ) :
    ∑ i, (w i - qTern s (w i)) ^ 2
      = ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (w i - qTern s (w i)) ^ 2
        + satTail s w := by
  have h1 : ∀ i : Fin n, (if ternInRange s (w i) then (w i - qTern s (w i)) ^ 2 else 0)
        + (if ¬ ternInRange s (w i) then (w i - qTern s (w i)) ^ 2 else 0)
      = (w i - qTern s (w i)) ^ 2 := by
    intro i
    by_cases h : ternInRange s (w i)
    · simp [h]
    · simp [h]
  have h2 : ∑ i, (w i - qTern s (w i)) ^ 2
      = ∑ i, (if ternInRange s (w i) then (w i - qTern s (w i)) ^ 2 else 0)
        + ∑ i, (if ¬ ternInRange s (w i) then (w i - qTern s (w i)) ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (h1 i).symm
  rw [h2, ← Finset.sum_filter, ← Finset.sum_filter]
  -- the saturated terms are exactly the overshoots (qTern_error_out)
  have hout : ∀ i ∈ Finset.univ.filter (fun i => ¬ ternInRange s (w i)),
      (w i - qTern s (w i)) ^ 2 = (|w i| - s) ^ 2 := by
    intro i hi
    rw [← sq_abs (w i - qTern s (w i)),
      qTern_error_out s (w i) hs (Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl hout]
  unfold satTail
  rfl

/-- The in-range part is at most `n_in · (s/2)²`: each
in-range coordinate contributes a half-step rounding square. -/
theorem ternary_inrange_bound (s : ℝ) {n : ℕ} (hs : 0 < s) (w : Fin n → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (w i - qTern s (w i)) ^ 2
      ≤ (Finset.univ.filter (fun i => ternInRange s (w i))).card * (s / 2) ^ 2 := by
  have hsq : ∀ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
      (w i - qTern s (w i)) ^ 2 ≤ (s / 2) ^ 2 := by
    intro i hi
    have hin : ternInRange s (w i) := (Finset.mem_filter.mp hi).2
    have hle := qTern_error_in s (w i) hs hin
    rw [abs_le] at hle
    nlinarith [hle.1, hle.2]
  calc ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (w i - qTern s (w i)) ^ 2
      ≤ ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (s / 2) ^ 2 := Finset.sum_le_sum hsq
    _ = (Finset.univ.filter (fun i => ternInRange s (w i))).card * (s / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_filter, nsmul_eq_mul]

/-- The total squared error is at most
`(n : ℝ) * (s / 2) ^ 2 + satTail s w`. -/
theorem ternary_split_le (s : ℝ) {n : ℕ} (hs : 0 < s) (w : Fin n → ℝ) :
    ∑ i, (w i - qTern s (w i)) ^ 2 ≤ (n : ℝ) * (s / 2) ^ 2 + satTail s w := by
  have hsplit := ternary_split_bound s hs w
  have hin := ternary_inrange_bound s hs w
  have hcard : (Finset.univ.filter (fun i => ternInRange s (w i))).card ≤ n := by
    calc (Finset.univ.filter (fun i => ternInRange s (w i))).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = n := by simp
  have hcard' : ((Finset.univ.filter (fun i => ternInRange s (w i))).card : ℝ)
      ≤ (n : ℝ) := by exact_mod_cast hcard
  have hmul : (Finset.univ.filter (fun i => ternInRange s (w i))).card * (s / 2) ^ 2
      ≤ (n : ℝ) * (s / 2) ^ 2 :=
    mul_le_mul_of_nonneg_right hcard' (sq_nonneg (s / 2))
  have hin' : ∑ i ∈ Finset.univ.filter (fun i => ternInRange s (w i)),
          (w i - qTern s (w i)) ^ 2 ≤ (n : ℝ) * (s / 2) ^ 2 :=
    le_trans hin hmul
  linarith

/-- The saturation tail is nonnegative (a sum of squares). -/
theorem satTail_nonneg (s : ℝ) {n : ℕ} (w : Fin n → ℝ) :
    0 ≤ satTail s w := by
  unfold satTail
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Helper: `√` is subadditive on `ℝ≥0` (Mathlib's current
`Real.sqrt_add` family lacks the plain two-term form). -/
private theorem sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have e1 := Real.sq_sqrt ha
    have e2 := Real.sq_sqrt hb
    nlinarith [h1]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = |Real.sqrt a + Real.sqrt b| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt a + Real.sqrt b :=
        abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-! ## The honest global energy bridge -/

/-- If `dE ≤ kappa * √(Σ quantization squares)`, then
`dE ≤ kappa * (√n * s / 2 + √(satTail s w))`: the energy cost
is bounded by the rounding term plus the saturation tail, with
no in-range assumption. -/
theorem quant_energy_bridge_saturation {n : ℕ} (w : Fin n → ℝ) (s kappa dE : ℝ)
    (hs : 0 < s) (hkappa : 0 ≤ kappa)
    (h_emp_lip : dE ≤ kappa * Real.sqrt (∑ i, (w i - qTern s (w i)) ^ 2)) :
    dE ≤ kappa * (Real.sqrt (n : ℝ) * s / 2 + Real.sqrt (satTail s w)) := by
  have hle := ternary_split_le s hs w
  have hnn : 0 ≤ (n : ℝ) * (s / 2) ^ 2 := by positivity
  have htail := satTail_nonneg s w
  have h1 : Real.sqrt (∑ i, (w i - qTern s (w i)) ^ 2)
      ≤ Real.sqrt ((n : ℝ) * (s / 2) ^ 2 + satTail s w) :=
    Real.sqrt_le_sqrt hle
  have h2 := sqrt_add_le ((n : ℝ) * (s / 2) ^ 2) (satTail s w) hnn htail
  have h3 : Real.sqrt ((n : ℝ) * (s / 2) ^ 2)
      = Real.sqrt (n : ℝ) * (s / 2) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)), Real.sqrt_sq_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < s / 2)]
  rw [h3] at h2
  have h4 : dE ≤ kappa * (Real.sqrt (n : ℝ) * (s / 2)
      + Real.sqrt (satTail s w)) :=
    le_trans h_emp_lip (mul_le_mul_of_nonneg_left (le_trans h1 h2) hkappa)
  linarith

/-! ## Recovery of the old bridge when nothing saturates -/

/-- If all coordinates are in range, the saturation tail
vanishes: the half-step bound `|w i - qTern s (w i)| ≤ s / 2`
holds for every `i`, and `dE ≤ kappa * √n * s / 2`. -/
theorem no_saturation_recover {n : ℕ} (w : Fin n → ℝ) (s kappa dE : ℝ)
    (hs : 0 < s) (hkappa : 0 ≤ kappa)
    (hall : ∀ i, ternInRange s (w i))
    (h_emp_lip : dE ≤ kappa * Real.sqrt (∑ i, (w i - qTern s (w i)) ^ 2)) :
    dE ≤ kappa * Real.sqrt (n : ℝ) * s / 2
      ∧ ∀ i, |w i - qTern s (w i)| ≤ s / 2 := by
  refine ⟨?_, fun i => qTern_error_in s (w i) hs (hall i)⟩
  -- the tail is empty: no coordinate is out of range
  have hempty : satTail s w = 0 := by
    unfold satTail
    rw [Finset.sum_eq_zero]
    intro i hi
    exact absurd (hall i) (Finset.mem_filter.mp hi).2
  have h0 : Real.sqrt (satTail s w) = 0 := by rw [hempty]; norm_num
  have hmain := quant_energy_bridge_saturation w s kappa dE hs hkappa h_emp_lip
  rw [h0] at hmain
  have heq : kappa * Real.sqrt (n : ℝ) * s / 2
      = kappa * (Real.sqrt (n : ℝ) * s / 2 + 0) := by ring
  rw [heq]
  exact hmain

/-- instantiation (audit 5.3): coordinatewise ternary rounding
(qTern, in-range) + an L-Lipschitz objective (in the sum of
coordinate deviations) bounds the objective error by
`L·(m·s/2)` — the concrete rounding feed for the State-layer
trajectory theorem's binder (`Hagi.State.coord_err_bound`; the
import Runtime→State is barred by LayerLint cross-folder rule,
so the concrete form lives beside `qTern`). -/
theorem ternary_coord_err {m : ℕ} (w w' : Fin m → ℝ) (s L : ℝ)
    (F : (Fin m → ℝ) → ℝ)
    (hs : 0 < s) (hin : ∀ i, ternInRange s (w i))
    (hw' : ∀ i, w' i = qTern s (w i))
    (hL : 0 ≤ L)
    (hLip : |F w' - F w| ≤ L * ∑ i, |w' i - w i|) :
    |F w' - F w| ≤ L * m * s / 2 := by
  have hcoord : ∀ i, |w' i - w i| ≤ s / 2 := by
    intro i
    rw [hw' i, abs_sub_comm]
    exact qTern_error_in s (w i) hs (hin i)
  calc |F w' - F w| ≤ L * ∑ i, |w' i - w i| := hLip
    _ ≤ L * ∑ i, (s / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => hcoord i)) hL
    _ = L * m * s / 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Hagi.Runtime

namespace Hagi
export Hagi.Runtime (qTern ternInRange qTern_error_in)
end Hagi

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

set_option linter.style.header false

/-!
# Квантизация свёрнутых живых весов

Сертификат для фазы упаковки LiveDelta: когда принятые
низкоранговые блоки сворачиваются в базу и база
перквантизуется на троичной сетке, по-элементная ошибка
ограничена s/2 (для в-диапазоне элементов, qTern_error_in),
а суммарная квадратичная ошибка — n·m·(s/2)².

Вне-диапазонные (сатурированные) элементы исключены
гипотезой; их хвост учитывается отдельным насыщением
(satTail в Runtime.TernaryExact). Ничего о качестве модели
не утверждается — только арифметика квантизации.
-/

open Finset Real Matrix

namespace Hagi.Runtime

variable {m n r : Type} [Fintype m] [Fintype n] [Fintype r]

/-- Поточечная тернарная квантизация матрицы на сетке шага s. -/
noncomputable def quantMat (s : ℝ) (M : Matrix m n ℝ) :
    Matrix m n ℝ :=
  Matrix.of fun i j => qTern s (M i j)

/-- Поточечная гарантия: в-диапазоне элементы матрицы
квантизуются с ошибкой ≤ s/2 (qTern_error_in). -/
theorem quantMat_entry (s : ℝ) (hs : 0 < s) (M : Matrix m n ℝ)
    (i : m) (j : n) (hin : ternInRange s (M i j)) :
    |M i j - quantMat s M i j| ≤ s / 2 :=
  qTern_error_in s (M i j) hs hin

/-- Суммарная квадратичная ошибка квантизации в-диапазонной
матрицы: ∑_{i,j} |M_ij − Q_ij|² ≤ (m·n)·(s/2)². -/
theorem quantMat_sq_bound (s : ℝ) (hs : 0 < s) (M : Matrix m n ℝ)
    (hin : ∀ i j, ternInRange s (M i j)) :
    ∑ i, ∑ j, (M i j - quantMat s M i j) ^ 2
      ≤ (Fintype.card m * Fintype.card n) * (s / 2) ^ 2 := by
  have hle : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      (M i j - quantMat s M i j) ^ 2 ≤ (s / 2) ^ 2 := by
    intro i _ j _
    have h := quantMat_entry s hs M i j (hin i j)
    have e2 : (M i j - quantMat s M i j) ^ 2
        = |M i j - quantMat s M i j| ^ 2 := (sq_abs _).symm
    rw [e2, pow_two, pow_two]
    have hs2 : 0 ≤ s / 2 := by positivity
    exact mul_le_mul h h (abs_nonneg _) hs2
  calc ∑ i, ∑ j, (M i j - quantMat s M i j) ^ 2
      ≤ ∑ i, ∑ j ∈ Finset.univ, (s / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => hle i (Finset.mem_univ i) j (Finset.mem_univ j)
    _ = (Fintype.card m * Fintype.card n) * (s / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ,
          Finset.sum_const, Finset.card_univ]
        ring

end Hagi.Runtime
