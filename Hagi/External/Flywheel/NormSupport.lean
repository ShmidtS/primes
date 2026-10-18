/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski

# Shared norm-support lemmas for the Flywheel linear-algebra modules

Single canonical copy of the helper lemmas previously duplicated
`private` in `MatrixNormRelations`, `SpectralNormGap`,
`CourantFischer` and `WeylInequality` (DupLint groups).
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! ### Shared helper lemmas -/

namespace Hagi.External.Flywheel

open scoped Complex BigOperators
open Matrix

/-- v4.34 port: Matrix.toEuclideanLin_apply removed; definitional. -/
lemma toEuclideanLin_apply {m : Type*} [Fintype m] [DecidableEq m]
    {𝕜 : Type*} [RCLike 𝕜] (A : Matrix m m 𝕜) (x : EuclideanSpace 𝕜 m) :
    Matrix.toEuclideanLin A x = A.mulVec x := rfl

/-- Cauchy-Schwarz for complex sums: |∑ⱼ aⱼ bⱼ| ≤ √(∑ⱼ |aⱼ|²) · √(∑ⱼ |bⱼ|²) -/
lemma complex_sum_cauchy_schwarz {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ j, a j * b j‖ ≤ Real.sqrt (∑ j, ‖a j‖^2) * Real.sqrt (∑ j, ‖b j‖^2) := by
  let a' : EuclideanSpace ℂ ι := WithLp.toLp 2 (star a)
  let b' : EuclideanSpace ℂ ι := WithLp.toLp 2 b
  have h1 : inner ℂ a' b' = ∑ j, a j * b j := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, a', b', dotProduct]
    simp only [Pi.star_apply, star_star]
    apply Finset.sum_congr rfl; intro j _; ring
  have h2 : ‖inner ℂ a' b'‖ ≤ ‖a'‖ * ‖b'‖ := norm_inner_le_norm a' b'
  rw [h1] at h2
  calc ‖∑ j, a j * b j‖ ≤ ‖a'‖ * ‖b'‖ := h2
    _ = Real.sqrt (∑ j, ‖a j‖^2) * Real.sqrt (∑ j, ‖b j‖^2) := by
        simp only [EuclideanSpace.norm_eq, a', b']
        congr 1
        · congr 1; apply Finset.sum_congr rfl; intro j _
          simp only [Pi.star_apply, Complex.star_def, Complex.norm_conj]

/-- Matrix-vector multiplication bound: ‖A *ᵥ x‖² ≤ ‖A‖_F² · ‖x‖² -/
lemma mulVec_eucl_norm_sq_le {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) (x : EuclideanSpace ℂ n') :
    ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖^2 ≤
      (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have cs := fun i => complex_sum_cauchy_schwarz (A i) x.ofLp
  have h_nonneg : ∀ i, 0 ≤ Real.sqrt (∑ j, ‖A i j‖^2) * Real.sqrt (∑ j, ‖x.ofLp j‖^2) := by
    intro i; apply mul_nonneg <;> apply Real.sqrt_nonneg
  calc ∑ i, ‖∑ j, A i j * x.ofLp j‖ ^ 2
      ≤ ∑ i, (Real.sqrt (∑ j, ‖A i j‖^2) * Real.sqrt (∑ j, ‖x.ofLp j‖^2))^2 := by
        apply Finset.sum_le_sum; intro i _
        apply sq_le_sq'
        · linarith [h_nonneg i, norm_nonneg (∑ j, A i j * x.ofLp j)]
        · calc ‖∑ j, A i j * x.ofLp j‖ ≤ _ := cs i
            _ ≤ _ := abs_of_nonneg (h_nonneg i) ▸ le_refl _
    _ = ∑ i, (∑ j, ‖A i j‖^2) * (∑ j, ‖x.ofLp j‖^2) := by
        apply Finset.sum_congr rfl; intro i _
        rw [mul_pow, Real.sq_sqrt, Real.sq_sqrt] <;>
        · apply Finset.sum_nonneg; intro j _; exact sq_nonneg _
    _ = (∑ i, ∑ j, ‖A i j‖^2) * (∑ j, ‖x.ofLp j‖^2) := by rw [Finset.sum_mul]
    _ = (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := by rw [EuclideanSpace.norm_sq_eq]

/-- Matrix-vector multiplication bound: ‖A *ᵥ x‖ ≤ √(∑ᵢⱼ |Aᵢⱼ|²) · ‖x‖ -/
lemma mulVec_eucl_norm_le {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) (x : EuclideanSpace ℂ n') :
    ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖ ≤
      Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖ := by
  have h_sq := mulVec_eucl_norm_sq_le A x
  have h_frob_nonneg : 0 ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := Real.sqrt_nonneg _
  have h_norm_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
  apply le_of_sq_le_sq _ (mul_nonneg h_frob_nonneg h_norm_nonneg)
  calc ‖(EuclideanSpace.equiv m' ℂ).symm (A *ᵥ x.ofLp)‖ ^ 2
      ≤ (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖^2 := h_sq
    _ = Real.sqrt (∑ i, ∑ j, ‖A i j‖^2)^2 * ‖x‖^2 := by
        rw [Real.sq_sqrt]
        apply Finset.sum_nonneg; intro i _
        apply Finset.sum_nonneg; intro j _
        exact sq_nonneg _
    _ = (Real.sqrt (∑ i, ∑ j, ‖A i j‖^2) * ‖x‖)^2 := by ring

/-- Frobenius norm expressed as square root of sum of squared entries. -/
lemma frobenius_norm_eq_sqrt {m' n' : Type*} [Fintype m'] [Fintype n']
    (A : Matrix m' n' ℂ) :
    @Norm.norm _ Matrix.frobeniusSeminormedAddCommGroup.toNorm A =
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  norm_cast

end Hagi.External.Flywheel
