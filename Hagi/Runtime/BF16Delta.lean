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


/-! ## C249 nearest-normal relative rounding error (A8 F3)

The `Fin 128` fraction carrier plus the implicit leading one give 8
significant bits, so nearest selection inside the normal range
`2 ^ (-126) ≤ |x| ≤ 2 ^ 127` has relative error at most `2 ^ (-8)`
over the exact rational carrier. The constant is derived from the
carrier arithmetic (`ulp = 2 ^ (E - 134)` against the binade floor
`128 * 2 ^ (E - 134)`), never assumed. Below the normal range the
relative bound genuinely fails — the anchor round-trip corollary
documents why the FP32 master accumulation is necessary. -/

private theorem exists_round_le_half (r : ℚ) :
    ∃ n : ℤ, |(n : ℚ) - r| ≤ 1 / 2 := by
  refine ⟨⌊r + 1 / 2⌋, ?_⟩
  have h1 := Int.floor_le (r + 1 / 2)
  have h2 := Int.sub_one_lt_floor (r + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

private theorem exists_binade_bracket {t : ℚ} (ht : 0 < t) :
    ∃ k : ℤ, (2 : ℚ) ^ k ≤ t ∧ t < (2 : ℚ) ^ (k + 1) := by
  obtain ⟨k, hk⟩ := exists_mem_Ico_zpow ht (by norm_num : (1 : ℚ) < 2)
  exact ⟨k, hk.1, hk.2⟩

private theorem abs_sub_le_of_isNearest_pos {t : ℚ} (ht : 0 < t)
    (hmin : (2 : ℚ) ^ (-126 : ℤ) ≤ t) (hmax : t ≤ (2 : ℚ) ^ (127 : ℤ))
    {c : Code} (h : IsNearest t c) :
    |decode c - t| ≤ (2 : ℚ) ^ (-8 : ℤ) * t := by
  obtain ⟨k, hk1, hk2⟩ := exists_binade_bracket ht
  have hq : (1 : ℚ) < 2 := by norm_num
  have hz2 : (2 : ℚ) ≠ 0 := by norm_num
  have hkge : (-126 : ℤ) ≤ k := by
    by_contra hcon
    push_neg at hcon
    have h1 : ((2 : ℚ) ^ (-126 : ℤ)) < (2 : ℚ) ^ ((k : ℤ) + 1) :=
      lt_of_le_of_lt hmin hk2
    have h2 : (2 : ℚ) ^ ((k : ℤ) + 1) ≤ (2 : ℚ) ^ (-126 : ℤ) :=
      zpow_le_zpow_right₀ (le_of_lt hq) (by linarith)
    exact lt_irrefl _ (lt_of_lt_of_le h1 h2)
  have hkle : k ≤ (127 : ℤ) := by
    by_contra hcon
    push_neg at hcon
    have h1 : (2 : ℚ) ^ ((127 : ℤ) + 1) ≤ (2 : ℚ) ^ k :=
      zpow_le_zpow_right₀ (le_of_lt hq) (by linarith)
    have h2 : t < (2 : ℚ) ^ ((127 : ℤ) + 1) :=
      lt_of_le_of_lt hmax (zpow_lt_zpow_right₀ hq (by norm_num))
    exact not_lt_of_ge (h1.trans hk1) h2
  have hqm : (0 : ℚ) < (2 : ℚ) ^ (k - 7) := by positivity
  have him : (0 : ℚ) < (2 : ℚ) ^ (-(k - 7)) := by positivity
  have hmulcancel : (2 : ℚ) ^ (k - 7) * (2 : ℚ) ^ (-(k - 7)) = 1 := by
    rw [← zpow_add₀ hz2]
    norm_num
  have hmant128 : (128 : ℚ) * (2 : ℚ) ^ (k - 7) = (2 : ℚ) ^ k := by
    have h2 := zpow_add₀ (a := (2 : ℚ)) hz2 (7 : ℤ) (k - 7)
    have h128 : (128 : ℚ) = (2 : ℚ) ^ (7 : ℤ) := by norm_num
    rw [h128, ← h2]
    congr 1
    ring
  have hmant256 : (256 : ℚ) * (2 : ℚ) ^ (k - 7) = (2 : ℚ) ^ (k + 1) := by
    have h2 := zpow_add₀ (a := (2 : ℚ)) hz2 (8 : ℤ) (k - 7)
    have h256 : (256 : ℚ) = (2 : ℚ) ^ (8 : ℤ) := by norm_num
    rw [h256, ← h2]
    congr 1
    ring
  have hlow : (128 : ℚ) * (2 : ℚ) ^ (k - 7) ≤ t := by
    rw [hmant128]; exact hk1
  have hhigh : t < (256 : ℚ) * (2 : ℚ) ^ (k - 7) := by
    rw [hmant256]; exact hk2
  have hrlo : (128 : ℚ) ≤ t * (2 : ℚ) ^ (-(k - 7)) := by
    calc (128 : ℚ) = (128 : ℚ) * (2 : ℚ) ^ (k - 7) *
        (2 : ℚ) ^ (-(k - 7)) := by
          rw [mul_assoc, hmulcancel, mul_one]
      _ ≤ t * (2 : ℚ) ^ (-(k - 7)) :=
        mul_le_mul_of_nonneg_right hlow him.le
  have hrhi : t * (2 : ℚ) ^ (-(k - 7)) < (256 : ℚ) := by
    calc t * (2 : ℚ) ^ (-(k - 7)) <
        (256 : ℚ) * (2 : ℚ) ^ (k - 7) * (2 : ℚ) ^ (-(k - 7)) :=
          mul_lt_mul_of_pos_right hhigh him
      _ = (256 : ℚ) := by rw [mul_assoc, hmulcancel, mul_one]
  obtain ⟨n, hn⟩ := exists_round_le_half (t * (2 : ℚ) ^ (-(k - 7)))
  have hnnlo : ((128 : ℤ)) ≤ n := by
    have habs := abs_le.mp hn
    have h1 : (255 : ℚ) ≤ 2 * (n : ℚ) := by linarith
    have h2 : (255 : ℤ) ≤ 2 * n := by exact_mod_cast h1
    linarith
  have hnnhi : n ≤ ((256 : ℤ)) := by
    have habs := abs_le.mp hn
    have h1 : 2 * (n : ℚ) ≤ (513 : ℚ) := by linarith
    have h2 : 2 * n ≤ (513 : ℤ) := by exact_mod_cast h1
    linarith
  have hEpos : (0 : ℤ) ≤ k + 127 := by linarith
  have hElt : k + 127 ≤ 254 := by linarith
  have hhalf : ((1 : ℚ) / 2) * (2 : ℚ) ^ (k - 7) = (2 : ℚ) ^ (k - 8) := by
    rw [show ((1 : ℚ) / 2) = (2 : ℚ) ^ (-1 : ℤ) by norm_num,
      ← zpow_add₀ hz2]
    congr 1
    ring
  have hcand : ∃ d : Code, |decode d - t| ≤ (2 : ℚ) ^ (k - 8) := by
    by_cases hn256 : n = 256
    · have hrge : ((255 : ℚ) + 1 / 2) ≤
          t * (2 : ℚ) ^ (-(k - 7)) := by
        have habs := abs_le.mp hn
        rw [hn256] at habs
        linarith
      have hk126 : k ≤ 126 := by
        by_contra hcon
        push_neg at hcon
        have hprod : (2 : ℚ) ^ (127 : ℤ) * (2 : ℚ) ^ (-(k - 7)) =
            (2 : ℚ) ^ (134 - k) := by
          rw [← zpow_add₀ hz2]
          congr 1
          ring
        have hb1 : t * (2 : ℚ) ^ (-(k - 7)) ≤
            (2 : ℚ) ^ (127 : ℤ) * (2 : ℚ) ^ (-(k - 7)) :=
          mul_le_mul_of_nonneg_right hmax him.le
        have hb2 : (2 : ℚ) ^ (134 - k) ≤ (2 : ℚ) ^ (7 : ℤ) :=
          zpow_le_zpow_right₀ (le_of_lt hq) (by omega)
        have hb3 : (2 : ℚ) ^ (7 : ℤ) = (128 : ℚ) := by norm_num
        have hble : t * (2 : ℚ) ^ (-(k - 7)) ≤ (128 : ℚ) :=
          le_trans (le_trans hb1 hprod.le) (hb2.trans_eq hb3)
        linarith
      have hE1pos : (0 : ℤ) ≤ k + 128 := by linarith
      have hE1lt : k + 128 ≤ 254 := by linarith
      refine ⟨⟨false, ⟨(k + 128).toNat, by
          have := hE1lt
          omega⟩, ⟨0, by omega⟩⟩, ?_⟩
      have hexpne : ((k + 128).toNat) ≠ 0 := by
        have h1 : (((k + 128).toNat : ℤ)) ≠ 0 := by
          rw [Int.toNat_of_nonneg hE1pos]
          omega
        exact fun h => h1 (by exact_mod_cast h)
      have hdec : decode ⟨false, ⟨(k + 128).toNat, by
          have := hE1lt
          omega⟩, ⟨0, by omega⟩⟩ =
          (256 : ℚ) * (2 : ℚ) ^ (k - 7) := by
        simp only [decode, Bool.false_eq_true, ↓reduceIte, one_mul, hexpne]
        rw [Int.toNat_of_nonneg hE1pos]
        have hzpow : (2 : ℚ) ^ ((k : ℤ) + 128 - 134) =
            (2 : ℚ) ^ (k - 6) := by
          congr 1
          ring
        have h2 : (2 : ℚ) ^ (k - 6) = 2 * (2 : ℚ) ^ (k - 7) := by
          conv_lhs => rw [show (k - 6 : ℤ) = 1 + (k - 7) by ring]
          rw [zpow_add₀ hz2]
          norm_num
        rw [hzpow, h2]
        norm_num
        ring
      rw [hdec]
      have hpos : (0 : ℚ) ≤ (256 : ℚ) * (2 : ℚ) ^ (k - 7) - t := by
        have := hrhi
        linarith
      rw [abs_of_nonneg hpos]
      have hsplit : (256 : ℚ) * (2 : ℚ) ^ (k - 7) - t =
          ((256 : ℚ) - (t * (2 : ℚ) ^ (-(k - 7)))) * (2 : ℚ) ^ (k - 7) := by
        have hcancel : t * (2 : ℚ) ^ (-(k - 7)) * (2 : ℚ) ^ (k - 7) = t := by
          rw [mul_assoc, mul_comm ((2 : ℚ) ^ (-(k - 7)))
            ((2 : ℚ) ^ (k - 7)), hmulcancel, mul_one]
        rw [sub_mul, hcancel]
      rw [hsplit]
      have hbound : ((256 : ℚ) - (t * (2 : ℚ) ^ (-(k - 7)))) ≤ 1 / 2 := by
        have habs := abs_le.mp hn
        rw [hn256] at habs
        linarith
      calc ((256 : ℚ) - (t * (2 : ℚ) ^ (-(k - 7)))) * (2 : ℚ) ^ (k - 7) ≤
          ((1 : ℚ) / 2) * (2 : ℚ) ^ (k - 7) :=
            mul_le_mul_of_nonneg_right hbound hqm.le
        _ = (2 : ℚ) ^ (k - 8) := hhalf
    · have hn255 : n ≤ 255 := by omega
      refine ⟨⟨false, ⟨(k + 127).toNat, by
          have := hElt
          omega⟩, ⟨(n - 128).toNat, by
          have := hn255
          have := hnnlo
          omega⟩⟩, ?_⟩
      have hexpne : ((k + 127).toNat) ≠ 0 := by
        have h1 : (((k + 127).toNat : ℤ)) ≠ 0 := by
          rw [Int.toNat_of_nonneg hEpos]
          omega
        exact fun h => h1 (by exact_mod_cast h)
      have hdec : decode ⟨false, ⟨(k + 127).toNat, by
          have := hElt
          omega⟩, ⟨(n - 128).toNat, by
          have := hn255
          have := hnnlo
          omega⟩⟩ =
          ((n : ℚ)) * (2 : ℚ) ^ (k - 7) := by
        simp only [decode, Bool.false_eq_true, ↓reduceIte, one_mul, hexpne]
        have hfraccast : (((n - 128).toNat : ℕ) : ℚ) =
            ((n : ℤ) - 128) := by
          have hnn : (0 : ℤ) ≤ n - 128 := by omega
          exact_mod_cast Int.toNat_of_nonneg hnn
        rw [Int.toNat_of_nonneg hEpos, hfraccast]
        have hzpow : (2 : ℚ) ^ ((k : ℤ) + 127 - 134) =
            (2 : ℚ) ^ (k - 7) := by
          congr 1
          ring
        rw [hzpow]
        ring
      rw [hdec]
      have hsplit : ((n : ℚ)) * (2 : ℚ) ^ (k - 7) - t =
          ((n : ℚ) - (t * (2 : ℚ) ^ (-(k - 7)))) * (2 : ℚ) ^ (k - 7) := by
        have hcancel : t * (2 : ℚ) ^ (-(k - 7)) * (2 : ℚ) ^ (k - 7) = t := by
          rw [mul_assoc, mul_comm ((2 : ℚ) ^ (-(k - 7)))
            ((2 : ℚ) ^ (k - 7)), hmulcancel, mul_one]
        rw [sub_mul, hcancel]
      rw [hsplit, abs_mul, abs_of_pos hqm]
      calc |((n : ℚ) - (t * (2 : ℚ) ^ (-(k - 7))))| * (2 : ℚ) ^ (k - 7) ≤
          ((1 : ℚ) / 2) * (2 : ℚ) ^ (k - 7) :=
            mul_le_mul_of_nonneg_right hn hqm.le
        _ = (2 : ℚ) ^ (k - 8) := hhalf
  obtain ⟨d, hd⟩ := hcand
  have hfin : |decode c - t| ≤ (2 : ℚ) ^ (k - 8) := (h d).trans hd
  have hrel : (2 : ℚ) ^ (k - 8) = (2 : ℚ) ^ (-8 : ℤ) * (2 : ℚ) ^ k := by
    rw [← zpow_add₀ hz2]
    congr 1
    ring
  rw [hrel] at hfin
  exact hfin.trans (mul_le_mul_of_nonneg_left hk1
    (by positivity : (0 : ℚ) ≤ (2 : ℚ) ^ (-8 : ℤ)))


/-- Public sign-symmetric form of the nearest-normal relative bound. -/
theorem abs_sub_le_of_isNearest_normal {x : ℚ} (hx0 : x ≠ 0)
    (hmin : (2 : ℚ) ^ (-126 : ℤ) ≤ |x|)
    (hmax : |x| ≤ (2 : ℚ) ^ (127 : ℤ))
    {c : Code} (h : IsNearest x c) :
    |decode c - x| ≤ (2 : ℚ) ^ (-8 : ℤ) * |x| := by
  rcases lt_or_ge x 0 with hxlt | hxge
  · have hpos : (0 : ℚ) < -x := by linarith
    have hmin' : (2 : ℚ) ^ (-126 : ℤ) ≤ -x := by
      rw [abs_of_neg hxlt] at hmin
      linarith
    have hmax' : -x ≤ (2 : ℚ) ^ (127 : ℤ) := by
      rw [abs_of_neg hxlt] at hmax
      linarith
    have hsymm : IsNearest (-x) (negate c) := by
      intro alternative
      have hle := h (negate alternative)
      rw [decode_negate] at hle
      have h1 : |decode (negate c) - (-x)| = |decode c - x| := by
        rw [decode_negate]
        have hneg : (-(decode c)) - (-x) = -(decode c - x) := by ring
        rw [hneg, abs_neg]
      have h2 : |decode alternative - (-x)| =
          |decode (negate alternative) - x| := by
        rw [decode_negate]
        have hneg : decode alternative - (-x) =
            -((-(decode alternative)) - x) := by ring
        rw [hneg, abs_neg]
      rw [h1]
      calc |decode c - x| ≤ |-decode alternative - x| := hle
        _ = |decode alternative - (-x)| := by
            have h3 : |-decode alternative - x| =
                |-(decode alternative - (-x))| := by
              congr 1
              ring
            rw [h3, abs_neg]
    have hbound := abs_sub_le_of_isNearest_pos hpos hmin' hmax' hsymm
    rw [decode_negate] at hbound
    have hrewb : |(-(decode c)) - (-x)| = |decode c - x| := by
      rw [show ((-(decode c)) - (-x)) = -(decode c - x) from by ring, abs_neg]
    rw [hrewb] at hbound
    rw [abs_of_neg hxlt]
    exact hbound
  · have hpos : (0 : ℚ) < x := by
      rcases eq_or_lt_of_le hxge with rfl | h
      · exact absurd rfl hx0
      · exact h
    rw [abs_of_pos hpos] at hmin hmax ⊢
    exact abs_sub_le_of_isNearest_pos hpos hmin hmax h

/-- FP32-master necessity: the nearest-round-trip update reconstruction at the
extreme anchor loses the whole small update — relative error 1 > 2⁻⁸. -/
theorem bf16_nearestRoundTrip_relativeError_gt
    (delta recovered : Code)
    (hdelta : IsNearest (decode nextAboveOne - decode anchor) delta)
    (hrecovered : IsNearest (decode delta + decode anchor) recovered) :
    (2 : ℚ) ^ (-8 : ℤ) * |decode nextAboveOne| <
      |decode recovered - decode nextAboveOne| := by
  rw [extreme_nearest_delta_loses_update delta recovered hdelta hrecovered,
    decode_nextAboveOne, zero_sub, abs_neg]
  norm_num


end Hagi.Runtime.BF16Delta
