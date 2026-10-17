/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
/-!
# The ternary DFT-3 (F₃) mixer

Character form of the k-fold DFT-3 mixer on the index type
`Fin k → ZMod 3` (the flattening of the Kronecker recursion
`F₃ ⊗ₖ F₃ᵏ⁻¹`; the binary Kronecker algebra is in
`Hagi.Core.Kronecker`):

* `omega` = e^{2πi/3}: `omega ^ 3 = 1`, `omega ≠ 1`,
  `omega ^ 2 + omega + 1 = 0`, `‖omega‖ = 1`;
* `chi3 : ZMod 3 → ℂ` the multiplicative character:
  `chi3 a * chi3 b = chi3 (a + b)`, `conj (chi3 x) = chi3 (-x)`,
  `‖chi3 x‖ = 1`;
* `sum_chi3_eq_zero` — orthogonality of the nontrivial character on
  `(ZMod 3)^k`;
* `dftPow_mul_conjTranspose` — `dftPow k` is unitary;
  `dftPow_entry_modulus` — every entry has modulus `1 / √(3^k)`.
-/

open scoped Matrix
open scoped ComplexConjugate

namespace Hagi.Core

/-! ## The primitive cube root of unity -/

/-- `ω = e^{2π i/3} = -½ + (√3/2) i`, the generator of the DFT-3 mixer
entries. -/
noncomputable def omega : ℂ := Real.sqrt 3 / 2 * Complex.I - 1 / 2

theorem sq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := by
  rw [← pow_two]
  exact Real.sq_sqrt (by norm_num)

theorem sq3c : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
  rw [← Complex.ofReal_mul]
  exact mod_cast sq3

theorem omega_sq_add_add : omega ^ 2 + omega + 1 = 0 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  unfold omega
  linear_combination (-1 / 4) * sq3c + ((Real.sqrt 3 : ℝ) * (Real.sqrt 3 : ℝ) / 4) * hI

theorem omega_cubed : omega ^ 3 = 1 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  unfold omega
  linear_combination (3 - (Real.sqrt 3 : ℝ) * Complex.I) / 8 * sq3c
    + ((Real.sqrt 3 : ℝ) * (Real.sqrt 3 : ℝ)
      * ((Real.sqrt 3 : ℝ) * Complex.I - 3) / 8) * hI

theorem conj_omega : conj omega = omega ^ 2 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  unfold omega
  simp only [map_div₀, map_mul, map_sub, map_one, Complex.conj_I,
    Complex.conj_ofReal, Complex.conj_ofNat, pow_two]
  linear_combination (1 / 4) * sq3c - ((Real.sqrt 3 : ℝ) * (Real.sqrt 3 : ℝ) / 4) * hI

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  have h2 := omega_sq_add_add
  rw [h] at h2
  norm_num at h2

/-- `ω` lies on the unit circle: `‖ω‖ = 1`. -/
theorem norm_omega : ‖omega‖ = 1 := by
  have h0 : omega * omega ^ 2 = 1 := by
    rw [show omega * omega ^ 2 = omega ^ 3 from by ring, omega_cubed]
  have h1 : omega * conj omega = 1 := by
    rw [conj_omega]
    exact h0
  have h2 : ((Complex.normSq omega : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj]
    exact h1
  have h3 : Complex.normSq omega = 1 := mod_cast h2
  have h4 : ‖omega‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact h3
  have hnn : 0 ≤ ‖omega‖ := norm_nonneg omega
  nlinarith

theorem omega_pow_mod (n : ℕ) : omega ^ n = omega ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3]
  rw [pow_add, pow_mul, omega_cubed, one_pow, one_mul]

/-! ## The multiplicative character `χ₃` -/

/-- The multiplicative character `χ₃ : ZMod 3 → ℂ`, `a ↦ ω ^ a.val`.
Multiplicative: `χ₃ a * χ₃ b = χ₃ (a + b)`; unimodular: `‖χ₃ a‖ = 1`. -/
noncomputable def chi3 (a : ZMod 3) : ℂ := omega ^ (a.val : ℕ)

theorem chi3_zero : chi3 0 = 1 := by
  simp [chi3]

theorem chi3_one : chi3 1 = omega := by
  simp [chi3, ZMod.val_one]

theorem chi3_mul (a b : ZMod 3) : chi3 a * chi3 b = chi3 (a + b) := by
  simp only [chi3]
  rw [← pow_add, ZMod.val_add, omega_pow_mod]

theorem zmod3_two_add_eq_neg (x : ZMod 3) : x + x = -x := by
  have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  linear_combination x * h3

theorem chi3_sq_neg (x : ZMod 3) : chi3 x * chi3 x = chi3 (-x) := by
  rw [chi3_mul, zmod3_two_add_eq_neg]

theorem conj_chi3 (x : ZMod 3) : conj (chi3 x) = chi3 (-x) := by
  have h1 : conj (chi3 x) = chi3 x * chi3 x := by
    simp only [chi3]
    rw [map_pow (starRingEnd ℂ), conj_omega, ← pow_mul, two_mul, ← pow_add]
  rw [h1, chi3_sq_neg]

/-- The character is unimodular. -/
theorem chi3_norm (x : ZMod 3) : ‖chi3 x‖ = 1 := by
  rw [chi3, norm_pow, norm_omega, one_pow]

theorem chi3_ne_one {a : ZMod 3} (ha : a ≠ 0) : chi3 a ≠ 1 := by
  intro h
  apply ha
  have hv : a.val < 3 := ZMod.val_lt a
  rcases (show a.val = 0 ∨ a.val = 1 ∨ a.val = 2 by omega) with hv2 | hv2 | hv2
  · rw [(ZMod.natCast_zmod_val a).symm, hv2, Nat.cast_zero]
  · rw [chi3, hv2, pow_one] at h
    exact absurd h omega_ne_one
  · rw [chi3, hv2] at h
    have h2 : omega * omega ^ 2 = 1 := by
      rw [show omega * omega ^ 2 = omega ^ 3 from by ring, omega_cubed]
    rw [h, mul_one] at h2
    exact absurd h2 omega_ne_one

/-! ## Orthogonality of nontrivial characters on `(ZMod 3)^k` -/

variable {k : ℕ}

/-- **Orthogonality of the nontrivial character.** For `w ≠ 0` on
`(ZMod 3)^k`, the character sum `∑ c, χ₃ ⟨w, c⟩` vanishes: translating
`c` by `e_{l₀} · (w l₀)⁻¹` at a coordinate where `w` is nonzero
multiplies every term by `ω ≠ 1`. -/
theorem sum_chi3_eq_zero {w : Fin k → ZMod 3} (hw : w ≠ 0) :
    ∑ c : Fin k → ZMod 3, chi3 (∑ l, w l * c l) = 0 := by
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, w l₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (funext fun l => by simpa using hcon l)
  classical
  set t : Fin k → ZMod 3 := Pi.single l₀ ((w l₀)⁻¹) with ht
  set e : (Fin k → ZMod 3) → (Fin k → ZMod 3) := fun c => c + t with he
  have hbij : Function.Bijective e := by
    constructor
    · intro x y h
      exact add_right_cancel h
    · intro y
      exact ⟨y - t, by simp [he, sub_add_cancel]⟩
  have hshift : ∀ c : Fin k → ZMod 3,
      (∑ l, w l * (e c) l) = (∑ l, w l * c l) + 1 := by
    intro c
    have h1 : (∑ l, w l * (e c) l)
        = (∑ l, w l * c l) + (∑ l, w l * t l) := by
      simp only [he, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have h2 : (∑ l, w l * t l) = 1 := by
      rw [Finset.sum_eq_single l₀]
      · simp [ht, mul_inv_cancel₀ hl₀]
      · intro l _ hl
        rw [ht, Pi.single_apply, ite_eq_right hl, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ l₀) h
    rw [h1, h2]
  have hflip : ∀ c : Fin k → ZMod 3,
      chi3 (∑ l, w l * (e c) l) = omega * chi3 (∑ l, w l * c l) := by
    intro c
    rw [hshift c, ← chi3_mul, chi3_one]
    ring
  have hpair : ∑ c : Fin k → ZMod 3, chi3 (∑ l, w l * (e c) l)
      = ∑ c : Fin k → ZMod 3, chi3 (∑ l, w l * c l) :=
    Finset.sum_bijective e hbij
      (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      (fun _ _ => rfl)
  rw [Finset.sum_congr rfl (fun c _ => hflip c), ← Finset.mul_sum] at hpair
  have hzero : (1 - omega) * (∑ c : Fin k → ZMod 3, chi3 (∑ l, w l * c l))
      = 0 := by
    rw [sub_mul, one_mul]
    linear_combination (-1) * hpair
  rcases mul_eq_zero.mp hzero with h1 | h2
  · exfalso
    apply omega_ne_one
    exact (sub_eq_zero.mp h1).symm
  · exact h2

/-! ## The k-fold DFT-3 mixer `F₃ᵏ` -/

variable (k)

/-- The unscaled character matrix `M i j = χ₃ ⟨i, j⟩` on `(ZMod 3)^k`. -/
noncomputable def charMat : Matrix (Fin k → ZMod 3) (Fin k → ZMod 3) ℂ :=
  fun i j => chi3 (∑ l, i l * j l)

/-- The k-fold ternary DFT-3 mixer `F₃ᵏ` (character form on
`Fin k → ZMod 3`, the canonical flattening of `F₃ ⊗ₖ F₃ᵏ⁻¹`):
entries `χ₃ ⟨i, j⟩ / √(3^k)`. -/
noncomputable def dftPow : Matrix (Fin k → ZMod 3) (Fin k → ZMod 3) ℂ :=
  ((Real.sqrt (3 ^ k : ℝ)) : ℂ)⁻¹ • charMat k

variable {k}

theorem dftPow_apply (i j : Fin k → ZMod 3) :
    dftPow k i j
      = ((Real.sqrt (3 ^ k : ℝ)) : ℂ)⁻¹ * chi3 (∑ l, i l * j l) := by
  simp [dftPow, Matrix.smul_apply, smul_eq_mul, charMat]

/-- The unscaled character matrix satisfies `M * Mᴴ = 3^k • 1`
(the orthogonality of the characters `χ₃ ⟨i, ·⟩`). -/
theorem charMat_mul_conjTranspose :
    charMat k * (charMat k)ᴴ = ((3 ^ k : ℕ) : ℂ) • 1 := by
  ext i j
  have h1 : ∀ c : Fin k → ZMod 3,
      chi3 (∑ l, i l * c l) * chi3 (-(∑ l, j l * c l))
        = chi3 (∑ l, (i - j) l * c l) := by
    intro c
    rw [chi3_mul, ← sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => (sub_mul (i l) (j l) (c l)).symm
  have h2 : (charMat k * (charMat k)ᴴ) i j
      = ∑ c : Fin k → ZMod 3, chi3 (∑ l, (i - j) l * c l) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, charMat,
      Complex.star_def]
    simp only [conj_chi3]
    exact Finset.sum_congr rfl fun c _ => h1 c
  rw [h2]
  by_cases h : i = j
  · subst h
    have h3 : ∀ c : Fin k → ZMod 3,
        chi3 (∑ l, (i - i) l * c l) = 1 := by
      intro c
      have h4 : ∀ l : Fin k, (i - i) l * c l = 0 := by
        intro l
        rw [Pi.sub_apply, sub_self, zero_mul]
      rw [Finset.sum_congr rfl (fun l _ => h4 l), Finset.sum_const_zero,
        chi3_zero]
    rw [Finset.sum_congr rfl (fun c _ => h3 c), Finset.sum_const,
      Finset.card_univ, Fintype.card_fun]
    push_cast
    simp [Matrix.smul_apply]
  · rw [sum_chi3_eq_zero (fun hcon => h (sub_eq_zero.mp hcon))]
    simp [Matrix.smul_apply, h]

/-- The k-fold mixer is unitary: `dftPow k * (dftPow k)ᴴ = 1`. -/
theorem dftPow_mul_conjTranspose : dftPow k * (dftPow k)ᴴ = 1 := by
  set c : ℂ := ((Real.sqrt (3 ^ k : ℝ)) : ℂ)⁻¹ with hc
  have hconj : conj c = c := by
    rw [hc, ← Complex.ofReal_inv, Complex.conj_ofReal]
  have hconjT : (c • charMat k)ᴴ = c • (charMat k)ᴴ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
      map_mul, Complex.star_def]
    rw [hconj]
  have hcc : c * c = ((3 ^ k : ℝ) : ℂ)⁻¹ := by
    rw [hc, ← mul_inv, ← Complex.ofReal_mul, ← pow_two,
      Real.sq_sqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) k)]
  have hd : c * c * ((3 ^ k : ℕ) : ℂ) = 1 := by
    rw [hcc]
    push_cast
    rw [inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]
  have hdft : dftPow k = c • charMat k := rfl
  rw [hdft, hconjT, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    charMat_mul_conjTranspose, smul_smul, hd, one_smul]

/-- Every entry of `dftPow k` has modulus `(Real.sqrt (3 ^ k : ℝ))⁻¹`. -/
theorem dftPow_entry_modulus (i j : Fin k → ZMod 3) :
    ‖dftPow k i j‖ = (Real.sqrt (3 ^ k : ℝ))⁻¹ := by
  rw [dftPow_apply, norm_mul, chi3_norm, mul_one, norm_inv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

end Hagi.Core

namespace Hagi
export Hagi.Core (omega sq3 sq3c omega_sq_add_add omega_cubed conj_omega omega_ne_one norm_omega omega_pow_mod chi3 chi3_zero chi3_one chi3_mul zmod3_two_add_eq_neg chi3_sq_neg conj_chi3 chi3_norm chi3_ne_one sum_chi3_eq_zero charMat dftPow dftPow_apply charMat_mul_conjTranspose dftPow_mul_conjTranspose dftPow_entry_modulus)
end Hagi
/-!
# The real 6x6 lift of the F3 transform: the interleaving isometry

The complex F₃ transform of `Hagi.Core.DFT3` transported to real
(re, im)-interleaved coordinates: `interleave z = ![z.re, z.im]`,
lifted branch-major to `interleave3 : (Fin 3 → ℂ) → (Fin 3 × Fin 2 → ℝ)`.

* `interleave_norm` — the lift is an isometry: the real inner
  product of the interleaved images equals `∑ a, ‖z a‖ ^ 2`.
* `reCharMat` — the canonical 6×6 real character matrix built
  from `chi3`, with the conjugation identity `interleave_char_mul`:
  the interleaved image of the character multiplication equals
  `reCharMat *ᵥ interleave3 z`; `reUnitMat` is its scaling by
  `1 / Real.sqrt 3`.
* `reBlock_mul_transpose` — block algebra
  `reBlock c * (reBlock d)ᵀ = reBlock (c * star d)`.

The orthogonality of `reUnitMat` is not yet proven here.
-/

open scoped Matrix

namespace Hagi.RealF3

open Hagi

/-- The interleaving of a complex number as a real pair. -/
def interleave (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

/-- The branch-major, pair-interleaved lift of a complex 3-vector
to ℝ⁶: coordinate `(a, p)` is `p = 0 → re`, `p = 1 → im` of branch
`a`. -/
def interleave3 (z : Fin 3 → ℂ) : Fin 3 × Fin 2 → ℝ :=
  fun ab => interleave (z ab.1) ab.2

/-- The isometry: the real inner product of the interleaved
vectors is the real part of the complex inner product. -/
theorem interleave_norm (z : Fin 3 → ℂ) :
    (∑ ab : Fin 3 × Fin 2, interleave3 z ab * interleave3 z ab)
      = ∑ a, ‖z a‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hpair : ∑ p : Fin 2, interleave3 z (a, p) * interleave3 z (a, p)
      = (z a).re * (z a).re + (z a).im * (z a).im := by
    simp only [interleave3, interleave]
    rw [Fin.sum_univ_two]
    rfl
  rw [hpair]
  have hmod : ‖z a‖ ^ 2 = (z a).re * (z a).re + (z a).im * (z a).im := by
    have hnnsq : (0:ℝ) ≤ (z a).re * (z a).re + (z a).im * (z a).im :=
      add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    rw [Complex.norm_def, Complex.normSq_apply, pow_two,
      Real.mul_self_sqrt hnnsq]
  rw [hmod]

/-- The canonical real 6×6 block for one character value: the
2×2 block `c.re • (1 0; 0 1) + c.im • (0 -1; 1 0)` — the real
representation of multiplication by the complex number `c`. -/
noncomputable def reBlock (c : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c.re, -c.im; c.im, c.re]

/-- The coercion of a branch index into the character domain. -/
def branchZ (a : Fin 3) : ZMod 3 := (a.val : ZMod 3)

/-- The real 6×6 *character* matrix (no F₃ normalization): the
transported basis-change action, branch-major blocks
`reBlock (chi3 (a - b))`. -/
noncomputable def reCharMat : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ :=
  fun ab cd =>
    reBlock (chi3 (-(branchZ ab.1 * branchZ cd.1))) ab.2 cd.2

/-- The real 6×6 transport scaled by the F₃ normalization
`1 / Real.sqrt 3`. -/
noncomputable def reUnitMat : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ :=
  (1 / Real.sqrt 3) • reCharMat

/-- **The conjugation identity (the transported basis change).**
The interleaved image of the full character multiplication
`w a = ∑_c chi3 (a - c) * z c` equals the real character matrix
applied to the interleaved input — the real matrix realizes the
complex character action. -/
theorem interleave_char_mul (z : Fin 3 → ℂ) :
    interleave3 (fun a => ∑ c, chi3 (-(branchZ a * branchZ c)) * z c)
      = reCharMat *ᵥ interleave3 z := by
  ext ⟨a, p⟩
  fin_cases p
  · -- p = 0 (the re-coordinate)
    change (∑ c, chi3 (-(branchZ a * branchZ c)) * z c).re
      = ∑ cd : Fin 3 × Fin 2,
          reBlock (chi3 (-(branchZ a * branchZ (cd : Fin 3 × Fin 2).1))) 0 cd.2
            * interleave3 z cd
    rw [Fintype.sum_prod_type]
    have hsumre : (∑ c, chi3 (-(branchZ a * branchZ c)) * z c).re
        = ∑ c, (chi3 (-(branchZ a * branchZ c)) * z c).re := by
      rw [Fin.sum_univ_three, Fin.sum_univ_three, Complex.add_re,
        Complex.add_re]
    rw [hsumre]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fin.sum_univ_two]
    simp only [interleave3, interleave,
      Matrix.cons_val_one]
    simp [reBlock]
    ring
  · -- p = 1 (the im-coordinate)
    change (∑ c, chi3 (-(branchZ a * branchZ c)) * z c).im
      = ∑ cd : Fin 3 × Fin 2,
          reBlock (chi3 (-(branchZ a * branchZ (cd : Fin 3 × Fin 2).1))) 1 cd.2
            * interleave3 z cd
    rw [Fintype.sum_prod_type]
    have hsumim : (∑ c, chi3 (-(branchZ a * branchZ c)) * z c).im
        = ∑ c, (chi3 (-(branchZ a * branchZ c)) * z c).im := by
      rw [Fin.sum_univ_three, Fin.sum_univ_three, Complex.add_im,
        Complex.add_im]
    rw [hsumim]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fin.sum_univ_two]
    simp only [interleave3, interleave,
      Matrix.cons_val_one]
    simp [reBlock]
    ring

/-!
The orthogonality of `reUnitMat` is documented here but not yet
proven: the block algebra reduces `R Rᵀ` to
`(1/3) ∑_c reBlock (chi3 (c * (a - b)))`, and the character
orthogonality (`sum_chi3_eq_zero`) collapses the sum to `3` at
`a = b` and `0` otherwise, giving `R Rᵀ = 1`.
-/

/-- Block algebra: `reBlock c * (reBlock d)ᵀ = reBlock (c * star d)`
— the 2×2 real blocks compose under complex multiplication. -/
theorem reBlock_mul_transpose (c d : ℂ) :
    (reBlock c : Matrix (Fin 2) (Fin 2) ℝ) * (reBlock d)ᵀ = reBlock (c * star d) := by
  ext i j
  simp only [reBlock, Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    ring

end Hagi.RealF3

set_option linter.style.header false

/-!
# Entry-level orthogonality of the real 6×6 F₃ lift

`reUnitMat_mul_transpose`: the block algebra `reBlock_mul_transpose`
plus the character orthogonality collapse to
`reUnitMat * reUnitMatᵀ = 1`.
-/

open scoped Matrix
open scoped ComplexConjugate

namespace Hagi.RealF3

open Hagi

theorem chi3_two : chi3 (2 : ZMod 3) = omega ^ 2 := by
  rw [chi3, show ((2 : ZMod 3).val = 2) from rfl]

theorem chi3_four : chi3 (4 : ZMod 3) = omega := by
  rw [chi3, show ((4 : ZMod 3).val = 1) from rfl, pow_one]

/-- The character sum over the three branches vanishes for a
nonzero frequency `w`. -/
theorem sum_chi3_branch_eq_zero {w : ZMod 3} (hw : w ≠ 0) :
    ∑ e : Fin 3, chi3 (w * branchZ e) = 0 := by
  have hv : w.val < 3 := ZMod.val_lt w
  have hv0 : w.val ≠ 0 := fun h =>
    hw ((ZMod.natCast_zmod_val w).symm.trans (by rw [h]; exact Nat.cast_zero))
  rcases (show w = 1 ∨ w = 2 by
    rcases (show w.val = 1 ∨ w.val = 2 by omega) with h1 | h1
    · exact Or.inl ((ZMod.natCast_zmod_val w).symm.trans (by
        rw [h1]; exact Nat.cast_one))
    · exact Or.inr ((ZMod.natCast_zmod_val w).symm.trans (by
        rw [h1]; exact Nat.cast_two))) with h | h
  · subst h
    rw [Fin.sum_univ_three]
    norm_num [branchZ, chi3_zero, chi3_one, chi3_two, chi3_four]
    linear_combination omega_sq_add_add
  · subst h
    rw [Fin.sum_univ_three]
    norm_num [branchZ, chi3_zero, chi3_one, chi3_two, chi3_four]
    linear_combination omega_sq_add_add

theorem branchZ_inj (a b : Fin 3) (h : branchZ a = branchZ b) : a = b := by
  have ha : a.val < 3 := Fin.isLt a
  have hb : b.val < 3 := Fin.isLt b
  have h1 : ((a.val : ℕ) : ZMod 3) = ((b.val : ℕ) : ZMod 3) := h
  have h2 : ((a.val : ℕ) : ZMod 3).val = ((b.val : ℕ) : ZMod 3).val := by
    rw [h1]
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] at h2
  exact Fin.ext h2

/-- `reBlock` is additive under finite sums of scalars. -/
theorem reBlock_sum {α : Type*} [Fintype α] (f : α → ℂ) :
    ∑ e, reBlock (f e) = reBlock (∑ e, f e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reBlock, Matrix.sum_apply]

/-- The real 6×6 F₃ lift is orthogonal:
`reUnitMat * reUnitMatᵀ = 1`. -/
theorem reUnitMat_mul_transpose :
    reUnitMat * reUnitMatᵀ
      = (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ) := by
  ext ⟨a, p⟩ ⟨c, r⟩
  simp only [reUnitMat, reCharMat, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, Matrix.one_apply]
  have hblock : ∀ e : Fin 3, ∑ q : Fin 2,
      reBlock (chi3 (-(branchZ a * branchZ e))) p q
        * reBlock (chi3 (-(branchZ c * branchZ e))) r q
      = reBlock (chi3 (-(branchZ a * branchZ e))
          * star (chi3 (-(branchZ c * branchZ e)))) p r := by
    intro e
    rw [← reBlock_mul_transpose]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hchi : ∀ e : Fin 3,
      chi3 (-(branchZ a * branchZ e))
        * star (chi3 (-(branchZ c * branchZ e)))
      = chi3 ((branchZ c - branchZ a) * branchZ e) := by
    intro e
    rw [show star (chi3 (-(branchZ c * branchZ e)))
          = conj (chi3 (-(branchZ c * branchZ e))) from rfl,
      conj_chi3, chi3_mul]
    congr 1
    linear_combination branchZ e
      * sub_mul (branchZ c) (branchZ a) (branchZ e)
  have hconst : ∀ e : Fin 3, ∑ q : Fin 2,
      ((1 / Real.sqrt 3) * reBlock (chi3 (-(branchZ a * branchZ e))) p q)
        * ((1 / Real.sqrt 3) * reBlock (chi3 (-(branchZ c * branchZ e))) r q)
      = (1 / Real.sqrt 3) * (1 / Real.sqrt 3)
          * reBlock (chi3 ((branchZ c - branchZ a) * branchZ e)) p r := by
    intro e
    rw [Finset.sum_congr rfl (fun q (_ : q ∈ Finset.univ) =>
        show ((1 / Real.sqrt 3)
            * reBlock (chi3 (-(branchZ a * branchZ e))) p q)
            * ((1 / Real.sqrt 3)
              * reBlock (chi3 (-(branchZ c * branchZ e))) r q)
          = (1 / Real.sqrt 3) * (1 / Real.sqrt 3)
            * (reBlock (chi3 (-(branchZ a * branchZ e))) p q
              * reBlock (chi3 (-(branchZ c * branchZ e))) r q) from by ring),
      ← Finset.mul_sum, hblock e, hchi e]
  rw [Finset.sum_congr rfl fun e _ => hconst e, ← Finset.mul_sum,
    show (∑ i, reBlock (chi3 ((branchZ c - branchZ a) * branchZ i)) p r)
      = ((∑ i, reBlock (chi3 ((branchZ c - branchZ a) * branchZ i))) p r)
      from rfl,
    reBlock_sum]
  by_cases hac : a = c
  · subst hac
    have hzero : ∀ e : Fin 3,
        chi3 ((branchZ a - branchZ a) * branchZ e) = 1 := by
      intro e
      rw [sub_self, zero_mul, chi3_zero]
    have hsum : ∑ e, chi3 ((branchZ a - branchZ a) * branchZ e) = 3 := by
      rw [Finset.sum_congr rfl fun e (_ : e ∈ Finset.univ) => hzero e,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num
    rw [hsum]
    have hs : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ * 3 = 1 := by
      rw [← mul_inv_rev, sq3, inv_mul_cancel₀ (by norm_num : (3:ℝ) ≠ 0)]
    fin_cases p <;> fin_cases r <;>
      simp [reBlock, hs]
  · have hinj : branchZ c - branchZ a ≠ 0 := fun h =>
      hac (branchZ_inj a c ((sub_eq_zero.mp h).symm))
    rw [sum_chi3_branch_eq_zero hinj]
    have hne : (⟨a, p⟩ : Fin 3 × Fin 2) ≠ (⟨c, r⟩ : Fin 3 × Fin 2) :=
      fun h => hac (congrArg Prod.fst h)
    simp only [reBlock, hne]
    fin_cases p <;> fin_cases r <;> simp

end Hagi.RealF3
