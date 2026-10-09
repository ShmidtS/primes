/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false


/-!
# Step-0 equivalence of the mixer merge and the concat head

* `head_prerotation` — if `Q * Qᵀ = 1`, the pre-rotated head
  `W * Qᵀ` reproduces the original head's logits on the mixed
  stream: `(W * Qᵀ) *ᵥ (Q *ᵥ x) = W *ᵥ x`.
* `blockCols_mulVec_sum` — the column-concatenated head applied to
  stacked expert states yields the sum of the experts' individual
  contributions.
* `mulVec_dotProduct_mulVec` — an orthonormal mixer preserves the
  dot product: `(Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y`.
-/

open scoped Matrix

namespace Hagi

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Head pre-rotation.** For an orthonormal mixer `Q` (rows
orthonormal: `Q * Qᵀ = 1`, which for square `Q` also gives
`Qᵀ * Q = 1`), the pre-rotated head `W' = W * Qᵀ` reproduces the
original head's logits on the mixed stream exactly:
`(W * Qᵀ) *ᵥ (Q *ᵥ x) = W *ᵥ x`. -/
theorem head_prerotation (Q : Matrix n n ℝ) (hQ : Q * Qᵀ = 1)
    {o : Type*} (W : Matrix o n ℝ) (x : n → ℝ) :
    (W * Qᵀ) *ᵥ (Q *ᵥ x) = W *ᵥ x := by
  have hQ' : Qᵀ * Q = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq n n ℝ rfl).mp hQ
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ', Matrix.mul_one]

/-- The column-concatenation of two head projections: reads the `inl`
block with `W₁` and the `inr` block with `W₂`. -/
def blockCols {o : Type*} [Fintype o] {m₁ m₂ : Type*} [Fintype m₁]
    [Fintype m₂] (W₁ : Matrix o m₁ ℝ) (W₂ : Matrix o m₂ ℝ) :
    Matrix o (m₁ ⊕ m₂) ℝ :=
  fun j p => p.elim (W₁ j) (W₂ j)

/-- The column-concatenated head applied to a stacked vector yields
the sum of the two blocks' individual contributions. -/
theorem blockCols_mulVec_sum {o : Type*} [Fintype o] {m₁ m₂ : Type*}
    [Fintype m₁] [Fintype m₂] (W₁ : Matrix o m₁ ℝ) (W₂ : Matrix o m₂ ℝ)
    (v : m₁ ⊕ m₂ → ℝ) :
    blockCols W₁ W₂ *ᵥ v
      = W₁ *ᵥ (fun a => v (Sum.inl a)) + W₂ *ᵥ (fun b => v (Sum.inr b)) := by
  ext j
  simp [Matrix.mulVec, dotProduct, blockCols, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]

/-- An orthonormal mixer preserves the dot product:
`(Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y`. -/
theorem mulVec_dotProduct_mulVec (Q : Matrix n n ℝ) (hQ : Q * Qᵀ = 1)
    (x y : n → ℝ) :
    (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y := by
  have hQ' : Qᵀ * Q = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq n n ℝ rfl).mp hQ
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hQ',
    Matrix.one_mulVec, dotProduct_comm]

end Hagi
