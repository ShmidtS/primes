/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic

/-!
# Exact finite BF16 codes and guarded rational delta reads

This is a logical finite-code model, not a physical memory layout, an
executable rounding function, or a hardware-backend claim.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Runtime.BF16Delta

/-- All finite BF16 codes: sign, nonzero-to-254 raw exponent, fraction. -/
structure Code where
  negative : Bool
  exponent : Fin 255
  fraction : Fin 128
  deriving Fintype, DecidableEq

/-- Exact rational decoding, including both zeros and all subnormals. -/
def decode (c : Code) : ℚ :=
  (if c.negative then (-1 : ℚ) else 1) *
    (if c.exponent.val = 0 then (c.fraction.val : ℚ)
      else (128 : ℚ) + c.fraction.val) *
    (2 : ℚ) ^ (if c.exponent.val = 0 then (-133 : ℤ)
      else (c.exponent.val : ℤ) - 134)

/-- The positive raw-zero, fraction-zero code. -/
def zero : Code :=
  ⟨false, ⟨0, by omega⟩, ⟨0, by omega⟩⟩

/-- Pointwise minimum distance against every finite code. -/
def IsNearest (x : ℚ) (candidate : Code) : Prop :=
  ∀ alternative : Code,
    |decode candidate - x| ≤ |decode alternative - x|

set_option maxRecDepth 8000 in
/-- A nearest finite code exists by finite minimum-image selection. -/
theorem exists_IsNearest (x : ℚ) : ∃ result, IsNearest x result := by
  obtain ⟨c, _, hc⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Code)
      (fun d => |decode d - x|) ⟨zero, Finset.mem_univ zero⟩
  exact ⟨c, fun alternative => hc alternative (Finset.mem_univ alternative)⟩

/-- Every representable rational is a fixed point of nearest selection. -/
theorem isNearest_decode_self (c : Code) : IsNearest (decode c) c := by
  intro alternative
  rw [sub_self, abs_zero]
  exact abs_nonneg _

/-- Nearest selection at a representable rational has that exact value. -/
theorem decode_eq_of_isNearest_decode {c d : Code}
    (h : IsNearest (decode c) d) : decode d = decode c := by
  have hle := h c
  rw [sub_self, abs_zero] at hle
  have hzero : |decode d - decode c| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- Positive raw exponent 254 with zero fraction. -/
def anchor : Code :=
  ⟨false, ⟨254, by omega⟩, ⟨0, by omega⟩⟩

/-- The least represented value strictly above one. -/
def nextAboveOne : Code :=
  ⟨false, ⟨127, by omega⟩, ⟨1, by omega⟩⟩

@[simp] theorem decode_zero : decode zero = 0 := by
  norm_num [decode, zero]

@[simp] theorem decode_anchor : decode anchor = (2 : ℚ) ^ (127 : ℤ) := by
  norm_num [decode, anchor]

@[simp] theorem decode_nextAboveOne : decode nextAboveOne = 129 / 128 := by
  norm_num [decode, nextAboveOne]

private def negativeAnchor : Code :=
  ⟨true, ⟨254, by omega⟩, ⟨0, by omega⟩⟩

private theorem decode_negativeAnchor :
    decode negativeAnchor = -(2 : ℚ) ^ (127 : ℤ) := by
  norm_num [decode, negativeAnchor]

private theorem two_pow_127_eq_256_mul :
    (2 : ℚ) ^ (127 : ℤ) = 256 * (2 : ℚ) ^ (119 : ℤ) := by
  rw [show (127 : ℤ) = 119 + 8 by norm_num, zpow_add₀ (by norm_num)]
  norm_num

private theorem two_pow_127_eq_128_mul :
    (2 : ℚ) ^ (127 : ℤ) = 128 * (2 : ℚ) ^ (120 : ℤ) := by
  rw [show (127 : ℤ) = 120 + 7 by norm_num, zpow_add₀ (by norm_num)]
  norm_num

/-- Every finite value other than `-2^127` is strictly farther from
`129/128 - 2^127`; raw exponent 254 is handled separately. -/
private theorem distance_gt_of_ne_negativeAnchor {delta : Code}
    (hne : decode delta ≠ -(2 : ℚ) ^ (127 : ℤ)) :
    129 / 128 < |decode delta - (129 / 128 - (2 : ℚ) ^ (127 : ℤ))| := by
  cases hsign : delta.negative with
  | false =>
      have hd : 0 ≤ decode delta := by
        simp only [decode, hsign, Bool.false_eq_true, ↓reduceIte, one_mul]
        positivity
      have hs : (3 : ℚ) ≤ (2 : ℚ) ^ (127 : ℤ) := by norm_num
      rw [abs_of_nonneg (by linarith)]
      linarith
  | true =>
      by_cases hzero : delta.exponent.val = 0
      · have hd : decode delta =
            -(delta.fraction.val : ℚ) * (2 : ℚ) ^ (-133 : ℤ) := by
          simp [decode, hsign, hzero]
        have hf : (delta.fraction.val : ℚ) ≤ 127 := by
          exact_mod_cast (Nat.le_of_lt_succ delta.fraction.isLt)
        have hp : (0 : ℚ) < (2 : ℚ) ^ (-133 : ℤ) := by positivity
        have hprod := mul_le_mul_of_nonneg_right hf hp.le
        have hsmall : (127 : ℚ) * (2 : ℚ) ^ (-133 : ℤ) ≤ 1 := by norm_num
        have hs : (3 : ℚ) ≤ (2 : ℚ) ^ (127 : ℤ) := by norm_num
        rw [hd, abs_of_nonneg (by nlinarith)]
        nlinarith
      · by_cases htop : delta.exponent.val = 254
        · have hd : decode delta =
              -((128 : ℚ) + delta.fraction.val) * (2 : ℚ) ^ (120 : ℤ) := by
            simp [decode, hsign, htop]
          by_cases hf0 : delta.fraction.val = 0
          · exfalso
            apply hne
            calc
              decode delta = -(128 : ℚ) * (2 : ℚ) ^ (120 : ℤ) := by
                rw [hd, hf0]
                norm_num
              _ = -(2 : ℚ) ^ (127 : ℤ) := by
                rw [two_pow_127_eq_128_mul, neg_mul]
          · have hf : (1 : ℚ) ≤ delta.fraction.val := by
              exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hf0)
            have hp : (0 : ℚ) < (2 : ℚ) ^ (120 : ℤ) := by positivity
            have hdist : decode delta -
                (129 / 128 - (2 : ℚ) ^ (127 : ℤ)) =
                -(delta.fraction.val : ℚ) * (2 : ℚ) ^ (120 : ℤ) - 129 / 128 := by
              rw [hd, two_pow_127_eq_128_mul]
              ring
            rw [hdist, abs_of_nonpos (by nlinarith)]
            nlinarith
        · have hd : decode delta =
              -((128 : ℚ) + delta.fraction.val) *
                (2 : ℚ) ^ ((delta.exponent.val : ℤ) - 134) := by
            simp [decode, hsign, hzero]
          have he : delta.exponent.val ≤ 253 := by
            have := delta.exponent.isLt
            omega
          have hf : ((128 : ℚ) + delta.fraction.val) ≤ 255 := by
            have := delta.fraction.isLt
            exact_mod_cast (show 128 + delta.fraction.val ≤ 255 by omega)
          have hp : (0 : ℚ) <
              (2 : ℚ) ^ ((delta.exponent.val : ℤ) - 134) := by positivity
          have hp_le : (2 : ℚ) ^ ((delta.exponent.val : ℤ) - 134) ≤
              (2 : ℚ) ^ (119 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          have hprod : ((128 : ℚ) + delta.fraction.val) *
              (2 : ℚ) ^ ((delta.exponent.val : ℤ) - 134) ≤
              255 * (2 : ℚ) ^ (119 : ℤ) :=
            calc
              _ ≤ 255 * (2 : ℚ) ^ ((delta.exponent.val : ℤ) - 134) :=
                mul_le_mul_of_nonneg_right hf hp.le
              _ ≤ 255 * (2 : ℚ) ^ (119 : ℤ) :=
                mul_le_mul_of_nonneg_left hp_le (by norm_num)
          have hs : (4 : ℚ) ≤ (2 : ℚ) ^ (119 : ℤ) := by norm_num
          rw [hd, two_pow_127_eq_256_mul, abs_of_nonneg (by nlinarith)]
          nlinarith

/-- The extreme nearest delta is forced to the negative anchor. -/
theorem extreme_nearest_delta_eq {delta : Code}
    (h : IsNearest (decode nextAboveOne - decode anchor) delta) :
    decode delta = -decode anchor := by
  rw [decode_anchor]
  by_contra hne
  have hle := h negativeAnchor
  rw [decode_negativeAnchor, decode_nextAboveOne, decode_anchor] at hle
  have htarget :
      |-(2 : ℚ) ^ (127 : ℤ) - (129 / 128 - (2 : ℚ) ^ (127 : ℤ))| =
        129 / 128 := by
    rw [show -(2 : ℚ) ^ (127 : ℤ) - (129 / 128 - (2 : ℚ) ^ (127 : ℤ)) =
      -(129 / 128) by ring, abs_neg]
    norm_num
  rw [htarget] at hle
  exact (not_lt_of_ge hle) (distance_gt_of_ne_negativeAnchor hne)

/-- Nearest delta followed by nearest reconstruction loses the nonzero
update at the extreme anchor. -/
theorem extreme_nearest_delta_loses_update (delta recovered : Code)
    (hdelta : IsNearest (decode nextAboveOne - decode anchor) delta)
    (hrecovered : IsNearest (decode delta + decode anchor) recovered) :
    decode recovered = 0 := by
  have hzero : decode delta + decode anchor = 0 := by
    rw [extreme_nearest_delta_eq hdelta]
    ring
  rw [hzero, ← decode_zero] at hrecovered
  exact (decode_eq_of_isNearest_decode hrecovered).trans decode_zero

private def negate (c : Code) : Code :=
  ⟨!c.negative, c.exponent, c.fraction⟩

private theorem decode_negate (c : Code) : decode (negate c) = -decode c := by
  by_cases hE : c.exponent.val = 0 <;>
    cases h : c.negative <;>
    simp [negate, decode, h, hE] <;> ring

/-- Construct every nonnegative multiple of a normal binade quantum whose
Nat numerator is below 128, allowing a subnormal result. -/
private theorem exists_nonnegative_scaled (E m : ℕ)
    (hE : E ≠ 0) (hElt : E < 255) (hm : m < 128) :
    ∃ delta : Code, delta.negative = false ∧
      decode delta = (m : ℚ) * (2 : ℚ) ^ ((E : ℤ) - 134) := by
  by_cases hm0 : m = 0
  · exact ⟨zero, rfl, by simp [hm0]⟩
  let ell := Nat.log2 m
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hlower : 2 ^ ell ≤ m := by
    simpa only [ell, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hm0
  have hupper : m < 2 ^ (ell + 1) := by
    simpa only [ell, Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) m
  have hell : ell ≤ 6 := by
    by_contra h
    have hpow : 2 ^ 7 ≤ 2 ^ ell :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hpow
    omega
  by_cases hsub : E + ell ≤ 7
  · have hfrac : m * 2 ^ (E - 1) < 128 := by
      calc
        m * 2 ^ (E - 1) < 2 ^ (ell + 1) * 2 ^ (E - 1) :=
          Nat.mul_lt_mul_of_pos_right hupper (by positivity)
        _ = 2 ^ ((ell + 1) + (E - 1)) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
        _ = 128 := by norm_num
    refine ⟨⟨false, ⟨0, by omega⟩, ⟨m * 2 ^ (E - 1), hfrac⟩⟩,
      rfl, ?_⟩
    simp only [decode, Bool.false_eq_true, ↓reduceIte, one_mul]
    have hexp : ((E - 1 : ℕ) : ℤ) + (-133 : ℤ) = (E : ℤ) - 134 := by
      omega
    have hpow : (2 : ℚ) ^ (((E - 1 : ℕ) : ℤ)) * (2 : ℚ) ^ (-133 : ℤ) =
        (2 : ℚ) ^ ((E : ℤ) - 134) := by
      rw [← zpow_add₀ (a := (2 : ℚ)) (by norm_num), hexp]
    calc
      ((m * 2 ^ (E - 1) : ℕ) : ℚ) * (2 : ℚ) ^ (-133 : ℤ) =
          (m : ℚ) * ((2 : ℚ) ^ (((E - 1 : ℕ) : ℤ)) *
            (2 : ℚ) ^ (-133 : ℤ)) := by
            rw [Nat.cast_mul, Nat.cast_pow, ← zpow_natCast]
            norm_num only [Nat.cast_ofNat]
            ring_nf
      _ = (m : ℚ) * (2 : ℚ) ^ ((E : ℤ) - 134) := by rw [hpow]
  · let R := E + ell - 7
    let M := m * 2 ^ (7 - ell)
    have hR0 : R ≠ 0 := by
      dsimp [R]
      omega
    have hRlt : R < 255 := by
      dsimp [R]
      omega
    have hMlower : 128 ≤ M := by
      calc
        128 = 2 ^ ell * 2 ^ (7 - ell) := by
          rw [← pow_add]
          norm_num [show ell + (7 - ell) = 7 by omega]
        _ ≤ m * 2 ^ (7 - ell) := Nat.mul_le_mul_right _ hlower
        _ = M := rfl
    have hMupper : M < 256 := by
      calc
        M < 2 ^ (ell + 1) * 2 ^ (7 - ell) :=
          Nat.mul_lt_mul_of_pos_right hupper (by positivity)
        _ = 2 ^ ((ell + 1) + (7 - ell)) := (pow_add 2 _ _).symm
        _ = 256 := by norm_num [show ell + 1 + (7 - ell) = 8 by omega]
    have hfrac : M - 128 < 128 := by omega
    refine ⟨⟨false, ⟨R, hRlt⟩, ⟨M - 128, hfrac⟩⟩, rfl, ?_⟩
    simp only [decode, Bool.false_eq_true, ↓reduceIte, one_mul, hR0]
    rw [Nat.cast_sub hMlower]
    change ((128 : ℚ) + ((M : ℚ) - 128)) *
      (2 : ℚ) ^ ((R : ℤ) - 134) =
        (m : ℚ) * (2 : ℚ) ^ ((E : ℤ) - 134)
    have hmantissa : (128 : ℚ) + ((M : ℚ) - 128) = M := by ring
    rw [hmantissa]
    have hexp : ((R : ℤ) - 134) + ((7 - ell : ℕ) : ℤ) =
        (E : ℤ) - 134 := by
      dsimp [R]
      omega
    calc
      (M : ℚ) * (2 : ℚ) ^ ((R : ℤ) - 134) =
          (m : ℚ) * ((2 : ℚ) ^ ((R : ℤ) - 134) *
            (2 : ℚ) ^ (((7 - ell : ℕ) : ℤ))) := by
            dsimp [M]
            rw [Nat.cast_mul, Nat.cast_pow, ← zpow_natCast]
            ring_nf
      _ = (m : ℚ) * (2 : ℚ) ^ ((E : ℤ) - 134) := by
            rw [← zpow_add₀ (a := (2 : ℚ)) (by norm_num), hexp]

/-- Equality of positive, nonzero raw exponents; subnormal results remain
inside the full finite carrier. -/
def SamePositiveNormalBinade (anchor new : Code) : Prop :=
  anchor.negative = false ∧ new.negative = false ∧
    anchor.exponent = new.exponent ∧ anchor.exponent.val ≠ 0

instance decidableSamePositiveNormalBinade (anchor new : Code) :
    Decidable (SamePositiveNormalBinade anchor new) := by
  unfold SamePositiveNormalBinade
  infer_instance

/-- Exact difference membership for every aligned positive normal pair,
including gradual-underflow differences. -/
theorem exists_sameBinade_difference {anchor new : Code}
    (hGuard : SamePositiveNormalBinade anchor new) :
    ∃ delta, decode delta = decode new - decode anchor := by
  rcases hGuard with ⟨haSign, hnSign, hExp, hE⟩
  have hnE : new.exponent.val ≠ 0 := by rwa [← hExp]
  have hp : (0 : ℚ) < (2 : ℚ) ^ ((new.exponent.val : ℤ) - 134) := by
    positivity
  have hdecodeAnchor : decode anchor =
      ((128 : ℚ) + anchor.fraction.val) *
        (2 : ℚ) ^ ((new.exponent.val : ℤ) - 134) := by
    simp [decode, haSign, hE, ← hExp]
  have hdecodeNew : decode new =
      ((128 : ℚ) + new.fraction.val) *
        (2 : ℚ) ^ ((new.exponent.val : ℤ) - 134) := by
    simp [decode, hnSign, hnE]
  rcases le_total (decode anchor) (decode new) with hle | hle
  · have hf : anchor.fraction.val ≤ new.fraction.val := by
      have hmul : ((128 : ℚ) + anchor.fraction.val) *
          (2 : ℚ) ^ ((new.exponent.val : ℤ) - 134) ≤
          ((128 : ℚ) + new.fraction.val) *
            (2 : ℚ) ^ ((new.exponent.val : ℤ) - 134) := by
        rw [← hdecodeAnchor, ← hdecodeNew]
        exact hle
      have hfrac := le_of_mul_le_mul_right hmul hp
      have hnat : 128 + anchor.fraction.val ≤ 128 + new.fraction.val := by
        exact_mod_cast hfrac
      omega
    obtain ⟨delta, _, hdelta⟩ := exists_nonnegative_scaled
      new.exponent.val (new.fraction.val - anchor.fraction.val)
      hnE new.exponent.isLt (by have := new.fraction.isLt; omega)
    refine ⟨delta, ?_⟩
    rw [hdelta, hdecodeAnchor, hdecodeNew, Nat.cast_sub hf]
    ring
  · have hf : new.fraction.val ≤ anchor.fraction.val := by
      have hmul : ((128 : ℚ) + new.fraction.val) *
          (2 : ℚ) ^ ((new.exponent.val : ℤ) - 134) ≤
          ((128 : ℚ) + anchor.fraction.val) *
            (2 : ℚ) ^ ((new.exponent.val : ℤ) - 134) := by
        rw [← hdecodeAnchor, ← hdecodeNew]
        exact hle
      have hfrac := le_of_mul_le_mul_right hmul hp
      have hnat : 128 + new.fraction.val ≤ 128 + anchor.fraction.val := by
        exact_mod_cast hfrac
      omega
    obtain ⟨delta, _, hdelta⟩ := exists_nonnegative_scaled
      new.exponent.val (anchor.fraction.val - new.fraction.val)
      hnE new.exponent.isLt (by have := anchor.fraction.isLt; omega)
    refine ⟨negate delta, ?_⟩
    rw [decode_negate, hdelta, hdecodeAnchor, hdecodeNew, Nat.cast_sub hf]
    ring

/-- Use the supplied readback under the exact-difference guard, otherwise
re-anchor directly to the already finite new code. -/
def guardedRead (anchor new readback : Code) : ℚ :=
  if SamePositiveNormalBinade anchor new then decode readback else decode new

/-- Two pointwise nearest certificates return the new value under the
guard; the fallback is definitionally the direct re-anchor. -/
theorem guardedRead_nearest_returns_new (anchor new delta recovered : Code)
    (hdelta : IsNearest (decode new - decode anchor) delta)
    (hrecovered : IsNearest (decode delta + decode anchor) recovered) :
    guardedRead anchor new recovered = decode new := by
  by_cases hGuard : SamePositiveNormalBinade anchor new
  · rw [guardedRead]
    simp only [hGuard, ↓reduceIte]
    obtain ⟨exactDelta, hexact⟩ := exists_sameBinade_difference hGuard
    have hprem : IsNearest (decode exactDelta) delta := by
      rwa [hexact]
    have hd : decode delta = decode exactDelta :=
      decode_eq_of_isNearest_decode hprem
    have hsum : decode exactDelta + decode anchor = decode new := by
      rw [hexact]
      ring
    rw [hd, hsum] at hrecovered
    exact decode_eq_of_isNearest_decode hrecovered
  · simp [guardedRead, hGuard]

end Hagi.Runtime.BF16Delta
