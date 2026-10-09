/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false


/-!
# Kronecker products preserve orthonormality

The Kronecker product of two matrices satisfying `A * Aᴴ = 1` and
`B * Bᴴ = 1` again satisfies `(A ⊗ₖ B) * (A ⊗ₖ B)ᴴ = 1`
(`kronecker_mul_conjTranspose`), with the analogous statements for
columns (`conjTranspose_kronecker_mul`) and over `ℝ` with the
transpose in place of the conjugate transpose
(`kronecker_mul_transpose`, `transpose_kronecker_mul`). The k-fold
products follow by induction.
-/

open scoped Matrix
open scoped Kronecker

namespace Hagi

section Complex

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Kronecker of unitary is unitary** (complex version):
if `A * Aᴴ = 1` and `B * Bᴴ = 1` then `(A ⊗ₖ B) * (A ⊗ₖ B)ᴴ = 1`. -/
theorem kronecker_mul_conjTranspose {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A * Aᴴ = 1) (hB : B * Bᴴ = 1) :
    (A ⊗ₖ B) * (A ⊗ₖ B)ᴴ = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA, hB,
    Matrix.one_kronecker_one]

/-- **Kronecker of orthonormal rows is orthonormal** (complex columns
version): if `Aᴴ * A = 1` and `Bᴴ * B = 1` then
`(A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1`. -/
theorem conjTranspose_kronecker_mul {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA, hB,
    Matrix.one_kronecker_one]

end Complex

section Real

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- If `A * Aᵀ = 1` and `B * Bᵀ = 1` then
`(A ⊗ₖ B) * (A ⊗ₖ B)ᵀ = 1`. -/
theorem kronecker_mul_transpose {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (hA : A * Aᵀ = 1) (hB : B * Bᵀ = 1) :
    (A ⊗ₖ B) * (A ⊗ₖ B)ᵀ = 1 := by
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, hA, hB,
    Matrix.one_kronecker_one]

/-- **Kronecker of orthonormal columns is orthonormal** (real version):
if `Aᵀ * A = 1` and `Bᵀ * B = 1` then `(A ⊗ₖ B)ᵀ * (A ⊗ₖ B) = 1`. -/
theorem transpose_kronecker_mul {A : Matrix m m ℝ} {B : Matrix n n ℝ}
    (hA : Aᵀ * A = 1) (hB : Bᵀ * B = 1) :
    (A ⊗ₖ B)ᵀ * (A ⊗ₖ B) = 1 := by
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, hA, hB,
    Matrix.one_kronecker_one]

end Real

end Hagi
