/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false


/-!
# HAGI_v2: block-diagonal expert merge (step-0 equivalence)

This file formalizes the block-diagonal merge mechanism of HAGI_v2
(see `GROWING_HYPOTHESIS.md`, section "Механизм", and
`src/hagi/model/merge.py`).

HAGI_v2 merges N independently trained experts into one wide model by
block-diagonal initialization: `W_merged = diag(W₁, …, W_N)` (and likewise
for the other linear layers, e.g. `W_Q = diag(W_Q^1, …, W_Q^N)`).

The key property is that at optimization step 0 the merged model computes
*exactly* the N independent experts' outputs:

* off-diagonal blocks of `W_merged` are zero, so expert `k`'s output block
  receives no contribution from any other expert's weights or states;
* each diagonal block `W_k` reproduces expert `k`'s forward pass verbatim.

This is stated as `Hagi.step0_equivalence`: applying the merged linear layer
`Matrix.blockDiagonal' W` to the stacked expert states
(`Hagi.stackStates`) returns, in block `k`, exactly expert `k`'s output
`(W k *ᵥ x k)`.

Note on Mathlib: for matrix *multiplication* the Sigma-indexed analogue
already exists as `Matrix.blockDiagonal'_mul`
(`blockDiagonal' (fun k => M k * N k) = blockDiagonal' M * blockDiagonal' N`,
Mathlib/Data/Matrix/Block.lean); the `mulVec` version below is its
vector-action companion, which is what a linear layer's forward pass needs.
-/

namespace Hagi

open Matrix

variable {o : Type*} [Fintype o] [DecidableEq o]

/-- **Block-diagonal matrix–vector product, block-wise.**

For a family of expert matrices `M : ∀ i, Matrix (m' i) (n' i) α`, the
block-diagonal merge `blockDiagonal' M` acts on a stacked vector `v`
block-wise: in block `k`, the merged layer's output equals expert `k`'s
matrix `M k` applied to the `k`-th slice of `v`. Off-diagonal blocks
contribute nothing. -/
theorem blockDiagonal'_mulVec_apply {m' n' : o → Type*} [∀ i, Fintype (n' i)]
    {α : Type*} [CommSemiring α]
    (M : ∀ i, Matrix (m' i) (n' i) α) (v : (Σ i, n' i) → α) (k : o) (i : m' k) :
    (blockDiagonal' M *ᵥ v) ⟨k, i⟩ = (M k *ᵥ (fun j => v ⟨k, j⟩)) i := by
  simp only [Matrix.mulVec_apply_eq_sum, ← Finset.univ_sigma_univ, Finset.sum_sigma,
    Matrix.blockDiagonal'_apply]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro j' hj'
    exact Finset.sum_eq_zero fun _ _ => by rw [dif_neg hj'.symm, zero_mul]

/-- Stack the per-expert states `x : ∀ i, m' i → ℝ` into a single vector on
the disjoint union `Σ i, m' i` (the merged model's wide state layout). -/
def stackStates {m' : o → Type*} (x : ∀ i, m' i → ℝ) : (Σ i, m' i) → ℝ :=
  fun p => x p.1 p.2

/-- **Step-0 equivalence of the HAGI_v2 block-diagonal merge.**

At merge time (step 0), the merged linear layer `blockDiagonal' W`
(the block-diagonal `diag(W₁, …, W_N)`) applied to the stacked expert
states reproduces, in block `k`, exactly expert `k`'s forward pass:
`(W k *ᵥ x k) i`. Off-diagonal blocks are zero and contribute nothing,
so the merged model is *exactly* the N independent experts. -/
theorem step0_equivalence {m' n' : o → Type*} [∀ i, Fintype (n' i)]
    (W : ∀ i, Matrix (m' i) (n' i) ℝ)
    (x : ∀ i, n' i → ℝ) (k : o) (i : m' k) :
    (blockDiagonal' W *ᵥ stackStates x) ⟨k, i⟩ = (W k *ᵥ x k) i :=
  blockDiagonal'_mulVec_apply W (stackStates x) k i

end Hagi
