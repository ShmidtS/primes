/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false


/-!
# The ternary DFT-3 (F₃) mixer of the recursive growth cycle

HAGI_v2 grows models by merging experts in **groups of three** via the
complex DFT-3 mixer (README.md "Growth cycle algorithm"):

> Merge three experts via the ternary DFT-3 mixer … recombines them
> with a unitary F₃ ⊗ I mixer. F₃ is unitary, every entry has modulus
> 1/√3 — uniform mixing with no blind channels. Groups of size 3ᵏ
> (3, 9, 27, …) are supported via Kronecker recursion F₃ᵏ.

This module formalizes, in the character form on the index type
`Fin k → ZMod 3` (the canonical flattening of the Kronecker recursion
`F₃ ⊗ₖ F₃ᵏ⁻¹`; the binary Kronecker algebra is proved in
`Hagi.Core/Kronecker`):

* `omega` = e^{2πi/3}: `ω³ = 1`, `ω ≠ 1`, `ω² + ω + 1 = 0`, `‖ω‖ = 1`;
* `chi3 : ZMod 3 → ℂ` the multiplicative character: `χ₃ a * χ₃ b =
  χ₃ (a + b)`, `conj (χ₃ x) = χ₃ (-x)`, `‖χ₃ x‖ = 1`;
* **orthogonality of nontrivial characters** on `(ZMod 3)^k`;
* `dftPow k`, the k-fold mixer: unitary (`F₃ᵏ * (F₃ᵏ)ᴴ = 1`) with
  every entry of modulus `1 / √(3^k)` — uniform mixing, no blind
  channels.
-/

open scoped Matrix
open scoped ComplexConjugate

namespace Hagi

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
        rw [ht, Pi.single_apply, if_neg hl, mul_zero]
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

/-- **The DFT-3 mixer is unitary**: `F₃ᵏ * (F₃ᵏ)ᴴ = 1` — "F₃ is
unitary … uniform mixing with no blind channels" (README.md). -/
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

/-- **Every entry has modulus `1/√(3^k)`** — uniform mixing with no
blind channels (README.md). -/
theorem dftPow_entry_modulus (i j : Fin k → ZMod 3) :
    ‖dftPow k i j‖ = (Real.sqrt (3 ^ k : ℝ))⁻¹ := by
  rw [dftPow_apply, norm_mul, chi3_norm, mul_one, norm_inv,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

end Hagi
