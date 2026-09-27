/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false


/-!
# Step-0 equivalence of the mixer merge and the concat head

**Two different scales live in this story — do not mix them up**
(their confusion already cost HAGI a bug, commit `74e7d30`):

* `√n` (i.e. `H_n / √n`) is the *mixer* scale: it makes the Hadamard
  transform orthonormal (`Hagi.Hadamard`). It belongs to the hidden
  stream, never to the logits.
* `1/n` (i.e. `child / n`) is the *logit_scale* of the concat head:
  the head SUMS the per-block contributions, so dividing by `n`
  restores the child's temperature exactly
  (`Hagi.Concat.concat_unique_identity_scale`). The old `√n` here was
  a temperature artifact.


This module formalizes the step-0 claims of the HAGI_v2 merge
mechanism (GROWING_HYPOTHESIS.md Part V "Hadamard Cross-Expert
Mixer", `src/hagi/model/merge.py`):

1. **Head pre-rotation.** The Hadamard mixer at gain 0 computes
   `y = Q x` with an orthonormal `Q`. To make the step-0 logits
   coincide with the block-diagonal merge, the head projection is
   pre-rotated: `W' = W * Qᵀ`. Then `W' *ᵥ (Q *ᵥ x) = W *ᵥ x` exactly
   ("Проверено на реальных экспертах: max logit diff ~ bf16 noise").
2. **Concat head.** A head whose input projection is the column
   concatenation of the experts' heads sums the experts' logits — the
   `logit_scale / √N` observation of GROWING_HYPOTHESIS.md.
3. **Information neutrality.** An orthonormal mixer preserves the dot
   product: `(Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y`. The transform is a pure
   permutation of the expert axis — "it adds no information, only
   re-mixes it" (the user's core observation).
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

/-- **The concat head sums the experts' logits.** Applying the
column-concatenated head to the stacked expert states yields the sum
of the experts' individual logit contributions — the mechanism behind
the `logit_scale / √N` normalization of GROWING_HYPOTHESIS.md
("merged head-проекция (concat по input) суммирует N вкладов"). -/
theorem blockCols_mulVec_sum {o : Type*} [Fintype o] {m₁ m₂ : Type*}
    [Fintype m₁] [Fintype m₂] (W₁ : Matrix o m₁ ℝ) (W₂ : Matrix o m₂ ℝ)
    (v : m₁ ⊕ m₂ → ℝ) :
    blockCols W₁ W₂ *ᵥ v
      = W₁ *ᵥ (fun a => v (Sum.inl a)) + W₂ *ᵥ (fun b => v (Sum.inr b)) := by
  ext j
  simp [Matrix.mulVec, dotProduct, blockCols, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]

/-- **Information neutrality of the mixer.** An orthonormal mixer `Q`
preserves the dot product: `(Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y`. The
orthogonal transform adds no information — it only re-mixes the expert
axis. -/
theorem mulVec_dotProduct_mulVec (Q : Matrix n n ℝ) (hQ : Q * Qᵀ = 1)
    (x y : n → ℝ) :
    (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y := by
  have hQ' : Qᵀ * Q = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq n n ℝ rfl).mp hQ
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hQ',
    Matrix.one_mulVec, dotProduct_comm]

end Hagi
