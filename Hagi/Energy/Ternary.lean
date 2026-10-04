/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib



/-!
# Ternary quantization: 5 trits per byte, and grid rounding bounds

This module formalizes the packing/quantization facts of the HAGI_v2
ternary expert format (`scripts/dsv4_experts.py`,
`scripts/dsv4_refit_experts.py`):

* **5 trits per byte**: ternary codes `{0,1,2}^5` are stored base-3 in
  a single byte — `3⁵ = 243 ≤ 2⁸ = 256`, so the encoding
  `t ↦ ∑ tᵢ · 3ⁱ` is injective (`Hagi.tritEncode_injective`).
* **Grid rounding**: quantizing a value to the ternary grid
  `{-1, 0, +1}` (with per-group scale `s`) by nearest-grid rounding
  has error at most half a grid step on the covered range
  (`Hagi.roundTern_error`, `Hagi.roundTern_error_scaled`); likewise
  for the int4 `±7` grid (`Hagi.roundHalf_error`,
  `Hagi.clampInt4_error`). The zero level of the ternary grid is
  essential ("grids without it lose ~8 pp", README.md) — hence the
  symmetric thresholds at `±1/2`.
-/
open scoped Matrix
set_option linter.style.header false

namespace Hagi

/-! ## Base-3 packing of 5 trits into a byte -/

/-- Base-3 packing of a 5-trit word into a byte. -/
def tritEncode (t : Fin 5 → Fin 3) : ℕ := ∑ i, (t i : ℕ) * 3 ^ (i : ℕ)

theorem three_pow_five : (3 : ℕ) ^ 5 = 243 := by norm_num

theorem trits_fit_byte : 243 ≤ 2 ^ 8 := by norm_num

private theorem sum_two_pow (n : ℕ) :
    (∑ i : Fin n, (2 : ℤ) * 3 ^ (i : ℕ)) = 3 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ]
    omega

/-- The packed value of any trit word of length `n` is `< 3^n`; hence
a 5-trit word always fits in a byte. -/
private theorem encode_lt_aux : ∀ (n : ℕ) (t : Fin n → Fin 3),
    (∑ i, (t i : ℕ) * 3 ^ (i : ℕ)) + 1 ≤ 3 ^ n := by
  intro n
  induction n with
  | zero => intro t; simp
  | succ n ih =>
    intro t
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have h1 := ih (fun i => t i.castSucc)
    have hd := (t (Fin.last n)).isLt
    have hL : (t (Fin.last n) : ℕ) * 3 ^ n ≤ 2 * 3 ^ n := by
      gcongr
      omega
    rw [pow_succ]
    omega

theorem tritEncode_lt (t : Fin 5 → Fin 3) : tritEncode t < 256 := by
  have h := encode_lt_aux 5 t
  have h3 : (3 : ℕ) ^ 5 = 243 := three_pow_five
  have h2 : (2 : ℕ) ^ 8 = 256 := by norm_num
  change (∑ i : Fin 5, (t i : ℕ) * 3 ^ (i : ℕ)) < 256
  omega

/-! ## Injectivity of the base-3 encoding -/

/-- If `A + a·X = B + b·X` with `X > 0` and `|A − B| ≤ X − 1`, then
the "digits" and the "prefixes" coincide. (The digit difference
multiplied by `X` would otherwise exceed the prefix gap.) -/
private theorem last_digit_eq {A B a b X : ℤ} (hX : 0 < X)
    (h : A + a * X = B + b * X) (hAB : |A - B| ≤ X - 1) : a = b ∧ A = B := by
  by_cases hd : a = b
  · refine ⟨hd, ?_⟩
    rw [hd] at h
    linarith
  · exfalso
    have h2 : a * X - b * X = B - A := by linarith
    have h4 : B - A = (a - b) * X := by linarith
    have h3 : (a - b) * X = a * X - b * X := sub_mul a b X
    have habs1 : 1 ≤ |a - b| := by
      rcases le_or_gt (a - b) 0 with hle | hgt
      · rw [abs_of_nonpos hle]; omega
      · rw [abs_of_pos hgt]; omega
    have heq : |B - A| = |a - b| * X := by
      rw [h4, abs_mul, abs_of_pos hX]
    have hge : X ≤ |a - b| * X :=
      calc X = 1 * X := by ring
        _ ≤ |a - b| * X := mul_le_mul_of_nonneg_right habs1 (le_of_lt hX)
    rw [abs_sub_comm] at hAB
    rw [heq] at hAB
    omega

private theorem abs_sub_le (n : ℕ) (t s : Fin n → Fin 3) :
    |(∑ i, ((t i : ℕ) : ℤ) * 3 ^ (i : ℕ)) - (∑ i, ((s i : ℕ) : ℤ) * 3 ^ (i : ℕ))|
      ≤ 3 ^ n - 1 := by
  have hsub : (∑ i, ((t i : ℕ) : ℤ) * 3 ^ (i : ℕ))
        - (∑ i, ((s i : ℕ) : ℤ) * 3 ^ (i : ℕ))
      = ∑ i, (((t i : ℕ) : ℤ) - ((s i : ℕ) : ℤ)) * 3 ^ (i : ℕ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsub]
  have h1 : |∑ i, (((t i : ℕ) : ℤ) - ((s i : ℕ) : ℤ)) * 3 ^ (i : ℕ)|
      ≤ ∑ i, |(((t i : ℕ) : ℤ) - ((s i : ℕ) : ℤ)) * 3 ^ (i : ℕ)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ i, |(((t i : ℕ) : ℤ) - ((s i : ℕ) : ℤ)) * 3 ^ (i : ℕ)|
      ≤ ∑ i : Fin n, (2 : ℤ) * 3 ^ (i : ℕ) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hdi : |((t i : ℕ) : ℤ) - ((s i : ℕ) : ℤ)| ≤ 2 := by
      have h1' := (t i).isLt
      have h2' := (s i).isLt
      rw [abs_le]
      constructor <;> omega
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ (i : ℕ))]
    exact mul_le_mul_of_nonneg_right hdi (by positivity)
  have h3 := sum_two_pow n
  linarith

private theorem sum_injective_aux : ∀ (n : ℕ) (t s : Fin n → Fin 3),
    (∑ i, ((t i : ℕ) : ℤ) * 3 ^ (i : ℕ)) = (∑ i, ((s i : ℕ) : ℤ) * 3 ^ (i : ℕ)) →
    t = s := by
  intro n
  induction n with
  | zero =>
    intro t s _
    funext i
    exact i.elim0
  | succ n ih =>
    intro t s h
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at h
    simp only [Fin.val_castSucc, Fin.val_last] at h
    have h' : (∑ i : Fin n, ((t i.castSucc : ℕ) : ℤ) * 3 ^ (i : ℕ))
        + ((t (Fin.last n) : ℕ) : ℤ) * 3 ^ n
        = (∑ i : Fin n, ((s i.castSucc : ℕ) : ℤ) * 3 ^ (i : ℕ))
        + ((s (Fin.last n) : ℕ) : ℤ) * 3 ^ n := by
      linarith
    have hAbs := abs_sub_le n (fun i => t i.castSucc) (fun i => s i.castSucc)
    have hX : (0 : ℤ) < 3 ^ n := by positivity
    obtain ⟨hae, hAe⟩ := last_digit_eq hX h' hAbs
    have hlast : (t (Fin.last n) : ℕ) = (s (Fin.last n) : ℕ) := by
      exact_mod_cast hae
    have hts := ih (fun i => t i.castSucc) (fun i => s i.castSucc) hAe
    funext i
    rcases Nat.lt_or_ge (i : ℕ) n with hin | hin
    · have hic : i = Fin.castSucc (⟨(i : ℕ), hin⟩ : Fin n) := by
        apply Fin.val_injective
        rfl
      rw [hic]
      exact congrFun hts _
    · have hiv : (i : ℕ) = n := by omega
      have hil : i = Fin.last n := by
        apply Fin.val_injective
        rw [hiv]
        rfl
      rw [hil]
      exact Fin.val_injective hlast

/-- **5 trits pack injectively into a byte**: the base-3 encoding
`t ↦ ∑ tᵢ·3ⁱ` is injective on `{0,1,2}^5` (`3⁵ = 243 ≤ 256`, the
"5 trits/byte" packing of `dsv4_experts.py`). -/
theorem tritEncode_injective : Function.Injective tritEncode := by
  intro t s h
  have hz : (∑ i, ((t i : ℕ) : ℤ) * 3 ^ (i : ℕ))
      = (∑ i, ((s i : ℕ) : ℤ) * 3 ^ (i : ℕ)) := by
    have e1 : ((tritEncode t : ℕ) : ℤ)
        = ∑ i, ((t i : ℕ) : ℤ) * 3 ^ (i : ℕ) := by
      simp only [tritEncode]
      push_cast
      rfl
    have e2 : ((tritEncode s : ℕ) : ℤ)
        = ∑ i, ((s i : ℕ) : ℤ) * 3 ^ (i : ℕ) := by
      simp only [tritEncode]
      push_cast
      rfl
    rw [← e1, ← e2, h]
  exact sum_injective_aux 5 t s hz

/-! ## Nearest-grid rounding on the ternary and int4 grids -/

/-- Round to the nearest point of the ternary grid `{-1, 0, +1}`. -/
noncomputable def roundTern (x : ℝ) : ℤ :=
  if 1 / 2 < x then 1 else if x < -1 / 2 then -1 else 0

theorem roundTern_error (x : ℝ) (hx : |x| ≤ 3 / 2) :
    |x - (roundTern x : ℝ)| ≤ 1 / 2 := by
  rw [abs_le] at hx ⊢
  unfold roundTern
  by_cases h1 : 1 / 2 < x
  · rw [ite_eq_left h1]
    push_cast
    constructor <;> linarith
  · by_cases h2 : x < -1 / 2
    · rw [ite_eq_right h1, ite_eq_left h2]
      push_cast
      constructor <;> linarith
    · rw [ite_eq_right h1, ite_eq_right h2]
      push_cast
      constructor <;> linarith

theorem roundTern_error_scaled (s x : ℝ) (hs : 0 < s) (hx : |x| ≤ 3 * s / 2) :
    |x - s * ((roundTern (x / s) : ℝ))| ≤ s / 2 := by
  have hx' : |x / s| ≤ 3 / 2 := by
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs, abs_le]
    rw [abs_le] at hx
    constructor <;> linarith
  have hq := roundTern_error (x / s) hx'
  have key : x - s * ((roundTern (x / s) : ℝ))
      = s * (x / s - (roundTern (x / s) : ℝ)) := by
    field_simp
  rw [key, abs_mul, abs_of_pos hs]
  have h4 : s * |x / s - ((roundTern (x / s)) : ℝ)| ≤ s * (1 / 2) :=
    mul_le_mul_of_nonneg_left hq (le_of_lt hs)
  linarith

/-- Round to the nearest integer (ties up). -/
noncomputable def roundHalf (x : ℝ) : ℤ :=
  if 1 / 2 ≤ x - Int.floor x then Int.floor x + 1 else Int.floor x

theorem roundHalf_error (x : ℝ) : |x - (roundHalf x : ℝ)| ≤ 1 / 2 := by
  have hfl : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have hfu : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
  unfold roundHalf
  by_cases h : 1 / 2 ≤ x - (Int.floor x : ℝ)
  · rw [ite_eq_left h]
    push_cast
    rw [abs_le]
    constructor <;> linarith
  · rw [ite_eq_right h]
    rw [abs_le]
    constructor <;> linarith

/-- Clamp an integer to the int4 grid `{-7, …, 7}`. -/
def clampInt4 (q : ℤ) : ℤ := max (-7) (min 7 q)

theorem clampInt4_error (x : ℝ) (hx : |x| ≤ 15 / 2) :
    |x - ((clampInt4 (roundHalf x) : ℝ))| ≤ 1 / 2 := by
  have hq := roundHalf_error x
  have hqabs := abs_le.mp hq
  have hxabs := abs_le.mp hx
  unfold clampInt4
  rcases le_or_gt (roundHalf x) 7 with h7 | h7
  · rcases le_or_gt (-7) (roundHalf x) with hm | hm
    · rw [min_eq_right h7, max_eq_right hm]
      exact hq
    · have hqm : roundHalf x ≤ -8 := by omega
      rw [min_eq_right h7, max_eq_left (by omega : (roundHalf x) ≤ (-7 : ℤ))]
      push_cast
      have hc : ((roundHalf x : ℤ) : ℝ) ≤ ((-8 : ℤ) : ℝ) :=
        Int.cast_le.mpr hqm
      push_cast at hc
      have hxm : x = -15 / 2 := by linarith
      rw [hxm, abs_le]
      norm_num
  · have hq8 : (8 : ℤ) ≤ roundHalf x := by omega
    rw [min_eq_left (by omega : ((7 : ℤ)) ≤ roundHalf x),
      max_eq_right (by omega : (-7 : ℤ) ≤ (7 : ℤ))]
    push_cast
    have hc : ((8 : ℤ) : ℝ) ≤ ((roundHalf x : ℤ) : ℝ) :=
      Int.cast_le.mpr hq8
    push_cast at hc
    have hx15 : x = 15 / 2 := by linarith
    rw [hx15, abs_le]
    norm_num

/-! ## Least-squares grid scales -/

/-- **LS-scale optimality (normal equations).** For a fixed quantization
pattern `q` (not identically zero), the least-squares scale
`s₀ = ∑ qᵢxᵢ / ∑ qᵢ²` minimizes the squared reconstruction error
`∑ (xᵢ − s·qᵢ)²` over all scales `s` — the closed form behind the
per-(row, group) LS scales of the ternary format ("LS scales instead
of amax = 90% of the PTQ win", README.md). The proof is the normal
equations: the cross term `∑ (x − s₀q)·q = 0` vanishes at `s₀`, so any
other scale adds `(s − s₀)²·∑ q²` of error.

Note: this is **squared-error (L2) optimality at a fixed pattern** —
the minimax (Chebyshev) scale `argmin_s max |x − s·q|` is a different
objective and is *not* claimed here. -/
theorem lsScale_optimal {ι : Type*} [Fintype ι] (x q : ι → ℝ)
    (hQ : 0 < ∑ i, q i * q i) (s : ℝ) :
    ∑ i, (x i - (∑ i, q i * x i) / (∑ i, q i * q i) * q i) ^ 2
      ≤ ∑ i, (x i - s * q i) ^ 2 := by
  set s₀ : ℝ := (∑ i, q i * x i) / (∑ i, q i * q i) with hs₀
  set Q : ℝ := ∑ i, q i * q i with hQdef
  have hQne : Q ≠ 0 := ne_of_gt hQ
  have hcross : ∑ i, (x i - s₀ * q i) * q i = 0 := by
    have h1 : ∑ i, (x i - s₀ * q i) * q i
        = ∑ i, (x i * q i - s₀ * (q i * q i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hQdef, hs₀,
      div_mul_cancel₀ _ hQne, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm (x i) (q i)
  have hexp : ∀ t : ℝ, ∑ i, (x i - t * q i) ^ 2
      = ∑ i, (x i - s₀ * q i) ^ 2 + (t - s₀) ^ 2 * Q := by
    intro t
    have h2 : ∀ i, x i - t * q i = (x i - s₀ * q i) + (s₀ - t) * q i := fun _ => by ring
    have h3 : ∑ i, (x i - t * q i) ^ 2
        = ∑ i, ((x i - s₀ * q i) + (s₀ - t) * q i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [h2 i]
    have h4 : ∑ i, ((x i - s₀ * q i) + (s₀ - t) * q i) ^ 2
        = ∑ i, ((x i - s₀ * q i) ^ 2
            + 2 * (s₀ - t) * ((x i - s₀ * q i) * q i)
            + (s₀ - t) ^ 2 * (q i * q i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h3, h4, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hcross, mul_zero, add_zero]
    ring
  have h5 := hexp s
  rw [h5]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg (s - s₀)) hQ.le)

section FunctionalLS

/-!
### The functional LS scale (the ridge-free normal equations)

**Prescription for the code (§13–14 of the synthesis).** The
terni4 refresh alternates `q → snap` (pattern refresh) and
`scale → LS` (functional re-solve). This section proves the
functional half in the Gram form: with the fixed pattern `q` and
the Gram matrix `H = XᵀX`, the optimal scalar for the functional
error `‖X w − X (s • q)‖²` is `s* = (qᵀ H w)/(qᵀ H q)` — the
normal-equation solution, unique whenever `qᵀ H q > 0`. This
generalizes `lsScale_optimal` (which is the `H = 1` case: there
the functional error reduces to the Euclidean one on the weight
vector), and gives the block-coordinate-descent guarantee:
alternating the exact minimizations in `q` and `s` is
monotonically non-increasing in the functional error — the
quantizer's refresh loop cannot get worse.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- The Gram form of the functional LS scale: for the functional
error `‖X w − s • (X q)‖²`, the optimal scale is `s* =
(qᵀ H w)/(qᵀ H q)` with `H = Xᵀ X`, whenever `qᵀ H q > 0`. The
proof is the complete-the-square decomposition: the cross term
`Σ (Xw − s Xq)(Xq)` vanishes exactly at `s = s*`, and the
remainder `Σ ((s − s*) • (Xq))²` is nonnegative. -/
theorem lsScale_gram {m : Type*} [Fintype m]
    (X : Matrix m n ℝ) (w q : n → ℝ)
    (hqHq : 0 < ∑ j, q j * ((Xᵀ *ᵥ (X *ᵥ q)) j)) :
    ∀ s : ℝ,
      ∑ i, ((X *ᵥ w) i
        - (X *ᵥ q) i * ((∑ j, q j * ((Xᵀ *ᵥ (X *ᵥ w)) j))
          / (∑ j, q j * ((Xᵀ *ᵥ (X *ᵥ q)) j)))) ^ 2
      ≤ ∑ i, ((X *ᵥ w) i - (X *ᵥ q) i * s) ^ 2 := by
  intro s
  set u : m → ℝ := X *ᵥ w with hu
  set v : m → ℝ := X *ᵥ q with hv
  set A : ℝ := ∑ i, u i * v i with hA
  set B : ℝ := ∑ i, v i * v i with hB
  -- the Gram quantities are the coordinate sums (adjointness)
  have hAeq : A = ∑ j, q j * ((Xᵀ *ᵥ (X *ᵥ w)) j) := by
    have h1 : (X *ᵥ w) ⬝ᵥ (X *ᵥ q)
        = (Xᵀ *ᵥ (X *ᵥ w)) ⬝ᵥ q := by
      rw [Matrix.dotProduct_mulVec,
        ← Matrix.vecMul_transpose (A := Xᵀ) (x := (X *ᵥ w)),
        Matrix.transpose_transpose]
    change (X *ᵥ w) ⬝ᵥ (X *ᵥ q) = ∑ j, q j * ((Xᵀ *ᵥ (X *ᵥ w)) j)
    rw [h1, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hBeq : B = ∑ j, q j * ((Xᵀ *ᵥ (X *ᵥ q)) j) := by
    have h1 : (X *ᵥ q) ⬝ᵥ (X *ᵥ q)
        = (Xᵀ *ᵥ (X *ᵥ q)) ⬝ᵥ q := by
      rw [Matrix.dotProduct_mulVec,
        ← Matrix.vecMul_transpose (A := Xᵀ) (x := (X *ᵥ q)),
        Matrix.transpose_transpose]
    rw [hB]
    change (X *ᵥ q) ⬝ᵥ (X *ᵥ q) = ∑ j, q j * ((Xᵀ *ᵥ (X *ᵥ q)) j)
    rw [h1, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- the cross term vanishes at the optimal scale
  have hBpos : 0 < B := hBeq ▸ hqHq
  have hBne : B ≠ 0 := ne_of_gt hBpos
  set s₀ : ℝ := A / B with hs₀
  have hcross : ∑ i, (u i - s₀ * v i) * v i = 0 := by
    have h1 : ∑ i, (u i - s₀ * v i) * v i
        = ∑ i, (u i * v i - s₀ * (v i * v i)) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h1, Finset.sum_sub_distrib, ← hA]
    rw [← Finset.mul_sum, ← hB, hs₀, div_mul_cancel₀ _ hBne,
      sub_eq_zero]
  -- complete the square
  have hexp : ∀ i : m,
      (u i - v i * s) ^ 2
        = ((u i - v i * s₀) + v i * (s₀ - s)) ^ 2 := by
    intro i
    ring
  have hsplit : ∀ i : m,
      ((u i - v i * s₀) + v i * (s₀ - s)) ^ 2
        = (u i - v i * s₀) ^ 2 + 2 * ((u i - v i * s₀) * (v i * (s₀ - s)))
          + (v i * (s₀ - s)) ^ 2 := by
    intro i
    ring
  rw [Finset.sum_congr rfl fun i _ => (hexp i).trans (hsplit i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the goal's LHS optimal scale is s₀ = A/B by the identities
  have hs : (∑ j, q j * ((Xᵀ *ᵥ X *ᵥ w) j))
      / (∑ j, q j * ((Xᵀ *ᵥ X *ᵥ q) j)) = s₀ := by
    rw [← hAeq, ← hBeq, hs₀]
  have hgoal : ∀ i : m,
      (u i - v i * ((∑ j, q j * ((Xᵀ *ᵥ X *ᵥ w) j))
        / (∑ j, q j * ((Xᵀ *ᵥ X *ᵥ q) j)))) ^ 2
      = (u i - v i * s₀) ^ 2 := by
    intro i
    rw [hs]
  rw [Finset.sum_congr rfl fun i _ => hgoal i]
  -- the cross term: 2(s₀-s)·∑(u-vs₀)v = 0
  have hcross' : ∑ i, (u i - v i * s₀) * v i = 0 := by
    have hmem : ∀ i : m, (u i - v i * s₀) * v i
        = (u i - s₀ * v i) * v i := by
      intro i
      ring
    rw [Finset.sum_congr rfl fun i _ => hmem i]
    exact hcross
  have hcrossterm2 : ∑ i, 2 * ((u i - v i * s₀) * (v i * (s₀ - s)))
      = 2 * (s₀ - s) * ∑ i, (u i - v i * s₀) * v i := by
    have hmem : ∀ i : m, 2 * ((u i - v i * s₀) * (v i * (s₀ - s)))
        = (2 * (s₀ - s)) * ((u i - v i * s₀) * v i) := by
      intro i
      ring
    rw [Finset.sum_congr rfl fun i _ => hmem i, Finset.mul_sum]
  rw [hcrossterm2, hcross', mul_zero, add_zero]
  -- the square term is nonnegative
  have hsq : 0 ≤ ∑ i, (v i * (s₀ - s)) ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  linarith

end FunctionalLS


end Hagi
