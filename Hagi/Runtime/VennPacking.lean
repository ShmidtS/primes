/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.DyadicTernary
import Hagi.Data.BoolVenn

set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# Packing variants table for the Venn lattice matrix

C251 (master plan v3 addendum A8, item F4).  The sixteen Venn masks
of `Hagi.Data.BoolVenn` form a `16 × 4` matrix of `{0,1}` entries —
sixty-four ternary symbols at level one (`vennTritRow`, middle /
positive branches of the existing `ternaryValueEncode`).  This module
counts the byte cost of the existing fixed-width codecs over that
matrix:

* flat — five-symbol `ternaryByteBlock` blocks: `tritsBytes` counts
  `⌈n / 5⌉` blocks, so the whole matrix takes `13` bytes
  (`flatVennBytes`), tight from below: twelve uniform bytes cannot
  carry sixty-four ternary symbols (`flatVenn_twelve_byte_impossible`);
* per-row — each row padded to a five-symbol word and encoded by the
  ACTUAL codec: `rowByte` is injective and its image has exactly `16`
  distinct bytes (`rowByte_injective`, `rowBytes_card`);
* dyadic per-block scale — each five-symbol block plus its own
  `DyadicScaleCode` in the sixteen-bit `dyadicBlock`: `26` bytes
  (`dyadicVennBytes`);
* shared scale — one scale byte for the whole matrix (`scaleCode_byte`)
  plus the flat payload: `14` bytes (`sharedScaleVennBytes`).

Honesty boundary, as in `Hagi.Runtime.TernaryCodec` and
`Hagi.Runtime.DyadicTernary`: these are fixed-width byte counts for
the named codec variants only.  The flat and dyadic counts are the
abstract block-count formula at the concrete matrix size — the full
sixty-four-symbol stream encoder is not instantiated here — while the
per-row variant is instantiated on all sixteen masks.  Nothing here
is a statement about entropy, universal compression, or the layout
behavior of any runtime.
-/

namespace Hagi.Runtime

open Hagi.Data.BoolVenn

/-- Ternary symbol of one mask entry at level one: `{0,1}` maps to
the middle / positive branches of the existing value encoder. -/
noncomputable def vennTritRow (m : Fin 4 → Bool) (j : Fin 4) : Fin 3 :=
  ternaryValueEncode 1 (if m j then 1 else 0)

theorem vennTritRow_eq (m : Fin 4 → Bool) (j : Fin 4) :
    vennTritRow m j = if m j then 2 else 1 := by
  unfold vennTritRow ternaryValueEncode
  by_cases hm : m j <;> simp [hm] <;> norm_num

/-- Byte count of `n` ternary symbols under the five-symbol flat
codec (`ternaryByteBlock`): one byte block per five symbols, the
final partial block included. -/
def tritsBytes (n : ℕ) : ℕ := (n + 4) / 5

theorem tritsBytes_five : tritsBytes 5 = 1 := by decide

theorem vennTrits_count : Fintype.card ((Fin 4 → Bool) × Fin 4) = 64 := by
  decide

/-- The flat variant: the whole lattice matrix (sixteen rows of four
symbols, `vennTrits_count`) takes thirteen flat byte blocks. -/
theorem flatVennBytes : tritsBytes (16 * 4) = 13 := by decide

/-- Twelve uniform bytes cannot carry sixty-four ternary symbols
(`3^64 > 2^96`), so the flat count is tight from below: no
twelve-byte uniform code exists for this payload. -/
theorem flatVenn_twelve_byte_impossible :
    ¬ ∃ f : (Fin 64 → Fin 3) → Fin (2 ^ 96), Function.Injective f := by
  rintro ⟨f, hf⟩
  have hcard := Fintype.card_le_of_injective f hf
  norm_num [Fintype.card_fun] at hcard

/-- Per-row word: the four row symbols padded to five with the middle
symbol. -/
noncomputable def rowWord (m : Fin 4 → Bool) : Fin 5 → Fin 3 :=
  fun i => if h : (i : ℕ) < 4 then vennTritRow m ⟨i, h⟩ else 1

/-- Per-row byte: the ACTUAL codec block of the padded row word. -/
noncomputable def rowByte (m : Fin 4 → Bool) : BitVec 8 :=
  ternaryByteBlock (rowWord m)

theorem vennTritRow_injective {m m' : Fin 4 → Bool}
    (h : ∀ j, vennTritRow m j = vennTritRow m' j) : m = m' := by
  funext j
  have := h j
  rw [vennTritRow_eq, vennTritRow_eq] at this
  by_cases hm : m j <;> by_cases hm' : m' j <;>
    simp [hm, hm'] at this ⊢

theorem rowByte_injective : Function.Injective rowByte := by
  intro m m' h
  have hword := ternaryByteBlock_injective h
  refine vennTritRow_injective fun j => ?_
  have := congrFun hword ⟨j.val, by omega⟩
  simpa [rowWord] using this

/-- The per-row variant occupies exactly sixteen distinct bytes: the
ACTUAL codec instantiated on all sixteen masks of the lattice. -/
theorem rowBytes_card :
    (Finset.univ.image rowByte).card = 16 := by
  rw [Finset.card_image_of_injOn
    (fun a _ b _ hab => rowByte_injective hab)]
  decide

/-- The dyadic per-block-scale variant: thirteen blocks of the
sixteen-bit `dyadicBlock` (five-symbol payload plus per-block scale
code) — twenty-six bytes. -/
theorem dyadicVennBytes : 2 * tritsBytes (16 * 4) = 26 := by decide

/-- A scale code fits a single byte: the finite scale alphabet embeds
injectively into the byte range. -/
theorem scaleCode_byte :
    ∃ f : DyadicScaleCode → Fin (2 ^ 8), Function.Injective f := by
  refine ⟨fun k => ⟨k.val, by omega⟩, fun a b h => Fin.ext ?_⟩
  have h1 := congrArg (fun v : Fin (2 ^ 8) => v.val) h
  simpa using h1

/-- The shared-scale variant: thirteen payload bytes plus one shared
scale byte — fourteen bytes. -/
theorem sharedScaleVennBytes : tritsBytes (16 * 4) + 1 = 14 := by
  decide

end Hagi.Runtime
