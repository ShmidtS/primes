/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false


/-!
# Sylvester (Walsh) Hadamard matrices of the HAGI cross-expert mixer

This module formalizes the Hadamard part of the HAGI_v2 merge mechanism
(`src/hagi/model/merge.py`, GROWING_HYPOTHESIS.md Part V "Hadamard
Cross-Expert Mixer"):

* the Sylvester Hadamard matrix `H` of order `2^k` (Walsh character form,
  indexed by bit vectors `Fin k → ZMod 2`, the canonical reindexing of
  `Fin (2^k)`) satisfies `H * Hᵀ = 2^k • 1`, hence `H / √(2^k)` is an
  orthonormal matrix — "a pure permutation of the expert axis … it adds
  no information, only re-mixes it";
* every entry has modulus `1 / √(2^k)` — uniform mixing, no blind
  channels.

The Python definition is the recursion
`H_1 = [1]`, `H_{2n} = [[H_n, H_n], [H_n, -H_n]]`; here we use the
equivalent closed (character) form `H i j = (-1)^{⟨i, j⟩}` with the
`ZMod 2` dot product `⟨i, j⟩ = ∑ l, i l * j l`.
-/

open scoped Matrix

namespace Hagi

/-! ## Small `ZMod 2` facts -/

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by exact mod_cast rfl
  calc a + a = 2 * a := by ring
    _ = 0 := by rw [h2, zero_mul]

theorem zmod2_neg_eq_self (a : ZMod 2) : -a = a :=
  neg_eq_of_add_eq_zero_left (zmod2_add_self a)

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := zmod2_add_self 1

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv : a.val < 2 := ZMod.val_lt a
  rw [← ZMod.natCast_zmod_val a]
  interval_cases a.val <;> simp

/-! ## The sign character of `ZMod 2` -/

/-- The sign character `χ : ZMod 2 → ℤ`, `0 ↦ 1`, `1 ↦ -1`.
It is multiplicative: `χ a * χ b = χ (a + b)`. -/
def chi2 (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

theorem chi2_zero : chi2 0 = 1 := rfl

theorem chi2_one : chi2 1 = -1 := ite_eq_right (by decide)

theorem chi2_sq (a : ZMod 2) : chi2 a * chi2 a = 1 := by
  rcases zmod2_cases a with h | h <;> simp [chi2, h]

theorem chi2_mul (a b : ZMod 2) : chi2 a * chi2 b = chi2 (a + b) := by
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;>
    simp [chi2, ha, hb, zmod2_one_add_one]

/-! ## The Sylvester Hadamard matrix -/

variable (k : ℕ)

/-- The Sylvester Hadamard matrix of order `2^k` in Walsh (character)
form: `H i j = χ (⟨i, j⟩)` where `⟨i, j⟩ = ∑ l, i l * j l` in `ZMod 2`.
Equivalent to the recursive `H_{2n} = [[H_n, H_n], [H_n, -H_n]]`
definition used in `src/hagi/model/merge.py` (up to the canonical
reindexing `Fin (2^k) ≃ (Fin k → ZMod 2)`). -/
def sylvester : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℤ :=
  fun i j => chi2 (∑ l, i l * j l)

variable {k}

theorem sylvester_apply (i j : Fin k → ZMod 2) :
    sylvester k i j = chi2 (∑ l, i l * j l) := rfl

@[simp]
theorem sylvester_transpose : (sylvester k)ᵀ = sylvester k := by
  ext i j
  rw [Matrix.transpose_apply, sylvester_apply, sylvester_apply]
  exact congrArg chi2
    (Finset.sum_congr rfl fun l _ => mul_comm (j l) (i l))

theorem sylvester_mem : ∀ i j, sylvester k i j = 1 ∨ sylvester k i j = -1 := by
  intro i j
  rw [sylvester_apply]
  rcases zmod2_cases (∑ l, i l * j l) with h | h <;> simp [chi2, h]

/-- Dot-product right-distributivity in the first argument. -/
theorem inner2_add_left (i j c : Fin k → ZMod 2) :
    (∑ l : Fin k, (i + j) l * c l) = (∑ l : Fin k, i l * c l) + (∑ l : Fin k, j l * c l) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by
    simp only [Pi.add_apply, add_mul]

/-- **Orthogonality of the nontrivial character.** For `w ≠ 0` the
character sum `∑ c, χ ⟨w, c⟩` vanishes (pairing `c ↔ c + e_{l₀}` at a
coordinate `l₀` where `w` is `1` flips every sign). -/
theorem sum_chi2_eq_zero {w : Fin k → ZMod 2} (hw : w ≠ 0) :
    ∑ c : Fin k → ZMod 2, chi2 (∑ l, w l * c l) = 0 := by
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, w l₀ = 1 := by
    by_contra hcon
    push Not at hcon
    refine hw (funext fun l => ?_)
    rcases zmod2_cases (w l) with h | h
    · exact h
    · exact absurd h (hcon l)
  classical
  set s : Fin k → ZMod 2 := Pi.single l₀ (1 : ZMod 2) with hs
  set e : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun c => c + s with he
  have hss : s + s = 0 := by
    funext l
    by_cases hl : l = l₀
    · simp [hs, hl, zmod2_one_add_one]
    · simp [hs, hl]
  have hbij : Function.Bijective e := by
    constructor
    · intro x y h
      exact add_right_cancel h
    · intro y
      refine ⟨y + s, ?_⟩
      simp only [he, add_assoc, hss, add_zero]
  have hflip : ∀ c : Fin k → ZMod 2,
      chi2 (∑ l, w l * (e c) l) = -chi2 (∑ l, w l * c l) := by
    intro c
    have h1 : (∑ l, w l * (e c) l)
        = (∑ l, w l * c l) + (∑ l, w l * s l) := by
      simp only [he, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have h2 : (∑ l, w l * s l) = w l₀ := by
      rw [Finset.sum_eq_single l₀]
      · simp [hs, hl₀]
      · intro l _ hl
        rw [hs, Pi.single_apply, ite_eq_right hl, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ l₀) h
    rw [h1, h2, hl₀, ← chi2_mul, chi2_one]
    ring
  have hpair : ∑ c : Fin k → ZMod 2, chi2 (∑ l, w l * (e c) l)
      = ∑ c : Fin k → ZMod 2, chi2 (∑ l, w l * c l) :=
    Finset.sum_bijective e hbij (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      (fun _ _ => rfl)
  rw [Finset.sum_congr rfl (fun c _ => hflip c)] at hpair
  rw [Finset.sum_neg_distrib] at hpair
  have hzero : (2 : ℤ) * (∑ c : Fin k → ZMod 2, chi2 (∑ l, w l * c l)) = 0 := by
    linarith
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- **Sylvester orthogonality**: `H * Hᵀ = 2^k • 1`, so `H / √(2^k)` is
an orthonormal matrix. This is the mathematical core of the Hadamard
cross-expert mixer (`Q = H_n / √n` in GROWING_HYPOTHESIS.md Part V). -/
theorem sylvester_mul_transpose :
    sylvester k * (sylvester k)ᵀ = (2 ^ k : ℤ) • 1 := by
  ext i j
  have h1 : ((sylvester k) * (sylvester k)ᵀ) i j
      = ∑ c : Fin k → ZMod 2, chi2 (∑ l, i l * c l) * chi2 (∑ l, j l * c l) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, sylvester_apply]
  rw [h1]
  by_cases h : i = j
  · subst h
    have hsum : ∑ c : Fin k → ZMod 2,
        chi2 (∑ l, i l * c l) * chi2 (∑ l, i l * c l) = (2 ^ k : ℤ) := by
      rw [Finset.sum_congr rfl (fun c _ => chi2_sq _), Finset.sum_const,
        Finset.card_univ, Fintype.card_fun]
      simp
    rw [hsum]
    simp [Matrix.smul_apply]
  · have h2 : ∀ c : Fin k → ZMod 2,
        chi2 (∑ l, i l * c l) * chi2 (∑ l, j l * c l)
          = chi2 (∑ l, (i + j) l * c l) := by
      intro c
      rw [chi2_mul, ← inner2_add_left]
    rw [Finset.sum_congr rfl (fun c _ => h2 c)]
    rw [sum_chi2_eq_zero (by
      intro hcon
      apply h
      funext l
      have hl := congrFun hcon l
      simp only [Pi.add_apply, Pi.zero_apply] at hl
      rw [eq_neg_of_add_eq_zero_left hl, zmod2_neg_eq_self])]
    simp [Matrix.smul_apply, h]

/-! ## The orthonormal transform `H / √(2^k)` -/

variable (k)

/-- The real Sylvester matrix, cast from `ℤ`. -/
def hadamardReal : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ :=
  (sylvester k).map (algebraMap ℤ ℝ)

/-- The orthonormal Hadamard transform `Q = H / √(2^k)` used as the
fixed part of the Hadamard cross-expert mixer. -/
noncomputable def hadamardOrthonormal : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ :=
  (Real.sqrt (2 ^ k : ℝ))⁻¹ • hadamardReal k

variable {k}

theorem hadamardReal_mul_transpose :
    hadamardReal k * (hadamardReal k)ᵀ = (2 ^ k : ℝ) • 1 := by
  have h1 : hadamardReal k * (hadamardReal k)ᵀ
      = ((sylvester k) * (sylvester k)ᵀ).map (algebraMap ℤ ℝ) := by
    rw [hadamardReal, ← Matrix.transpose_map, ← Matrix.map_mul]
  rw [h1, sylvester_mul_transpose]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  split <;> simp

/-- Generic scaling lemma: if `A * Aᵀ = d • 1` then `(c • A)` is
orthonormal whenever `c² * d = 1`. -/
theorem smul_orthonormal {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℝ} {d : ℝ} (hd : A * Aᵀ = d • 1) {c : ℝ}
    (hc : c * c * d = 1) : (c • A) * (c • A)ᵀ = 1 := by
  rw [Matrix.smul_mul, Matrix.transpose_smul, Matrix.mul_smul, smul_smul,
    hd, smul_smul, hc, one_smul]

/-- **The mixer matrix is orthonormal**: `Q * Qᵀ = 1` for
`Q = H / √(2^k)`. Uniform mixing with no blind channels. -/
theorem hadamardOrthonormal_mul_transpose :
    hadamardOrthonormal k * (hadamardOrthonormal k)ᵀ = 1 := by
  have hpos : 0 < (2 ^ k : ℝ) := pow_pos (by norm_num) _
  have hc2 : ((Real.sqrt (2 ^ k : ℝ))⁻¹) * ((Real.sqrt (2 ^ k : ℝ))⁻¹)
      * (2 ^ k : ℝ) = 1 := by
    rw [← pow_two, inv_pow, Real.sq_sqrt (le_of_lt hpos),
      inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]
  exact smul_orthonormal hadamardReal_mul_transpose hc2

end Hagi
