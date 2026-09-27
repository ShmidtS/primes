/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false


/-!
# Kronecker products preserve orthonormality

HAGI_v2 builds recursive/local mixers as Kronecker products of
orthonormal factors (GROWING_HYPOTHESIS.md Part VI):

* the recursive Hadamard mixer `Q = H_{g_k} ⊗ ⋯ ⊗ H_{g_1}` with
  `prod g_i = n`, each factor orthonormal;
* the ternary growth cycle's `F₃ᵏ` via Kronecker recursion
  (README.md: "Groups of size 3ᵏ (3, 9, 27, …) are supported via
  Kronecker recursion F₃ᵏ").

This module proves the underlying algebraic fact in its binary form
(the k-fold products follow by induction): the Kronecker product of
matrices with orthonormal rows (resp. columns, resp. unitary matrices)
again has orthonormal rows (resp. is unitary). Over a nontrivially
starred ring the conjugate-transpose version holds; over `ℝ` it
specializes to the transpose version.

This is the mathematical content of "Каждый фактор ортонормирован,
поэтому произведение ортонормировано" (GROWING_HYPOTHESIS.md Part VI)
and of `IsHadamard.kronecker` in Mathlib (cited there for the
unscaled ±1 / unit-modulus version).
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

/-- **Kronecker of orthonormal rows is orthonormal** (real version):
if `A * Aᵀ = 1` and `B * Bᵀ = 1` then `(A ⊗ₖ B) * (A ⊗ₖ B)ᵀ = 1`.
This is the algebraic core of the recursive/local Hadamard mixer
`Q = H_{g_k} ⊗ ⋯ ⊗ H_{g_1}` (GROWING_HYPOTHESIS.md Part VI). -/
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
