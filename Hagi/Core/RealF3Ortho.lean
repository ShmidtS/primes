/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.RealF3

set_option linter.style.header false

/-!
# Entry-level orthogonality of the real 6×6 F₃ lift

Step 2 of the documented orthogonality route (STATUS.md R89):
the block algebra `reBlock_mul_transpose` plus the character
orthogonality collapse `reUnitMat * reUnitMatᵀ = 1`.
-/

open scoped Matrix
open scoped ComplexConjugate

namespace Hagi.RealF3

open Hagi

/-- The character sum over the three branches vanishes for a
nonzero frequency `w` (the `k = 1` instance of the character
orthogonality `Hagi.sum_chi3_eq_zero`). -/
theorem chi3_two : chi3 (2 : ZMod 3) = omega ^ 2 := by
  rw [chi3, show ((2 : ZMod 3).val = 2) from rfl]

theorem chi3_four : chi3 (4 : ZMod 3) = omega := by
  rw [chi3, show ((4 : ZMod 3).val = 1) from rfl, pow_one]

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

/-- **The entry-level orthogonality of the real F₃ lift** (R89
step 2): the production 6×6 matrix `_f3_real_column_matrix` is
orthogonal — `reUnitMat * reUnitMatᵀ = 1`. -/
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
