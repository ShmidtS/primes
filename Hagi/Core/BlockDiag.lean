/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false


/-!
# Block-diagonal expert merge (step-0 equivalence)

The merged linear layer of `N` experts is `Matrix.blockDiagonal' W`
acting on the stacked states `stackStates x`.

* `blockDiagonal'_mulVec_apply` — block-wise action of
  `blockDiagonal' M` on a stacked vector (the mulVec companion of
  Mathlib's `Matrix.blockDiagonal'_mul`).
* `step0_equivalence` — in block `k`, the merged layer returns
  exactly expert `k`'s output `(W k *ᵥ x k)`: at step 0 the merged
  model computes exactly the `N` independent experts.
-/

namespace Hagi

open Matrix

variable {o : Type*} [Fintype o] [DecidableEq o]

/-- In block `k`, `blockDiagonal' M *ᵥ v` equals `M k` applied to
the k-th slice of `v`; off-diagonal blocks contribute nothing. -/
theorem blockDiagonal'_mulVec_apply {m' n' : o → Type*} [∀ i, Fintype (n' i)]
    {α : Type*} [CommSemiring α]
    (M : ∀ i, Matrix (m' i) (n' i) α) (v : (Σ i, n' i) → α) (k : o) (i : m' k) :
    (blockDiagonal' M *ᵥ v) ⟨k, i⟩ = (M k *ᵥ (fun j => v ⟨k, j⟩)) i := by
  simp only [Matrix.mulVec_apply_eq_sum, ← Finset.univ_sigma_univ, Finset.sum_sigma,
    Matrix.blockDiagonal'_apply]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro j' hj'
    exact Finset.sum_eq_zero fun _ _ => by rw [dite_eq_right hj'.symm, zero_mul]

/-- Stack the per-expert states `x : ∀ i, m' i → ℝ` into a single vector on
the disjoint union `Σ i, m' i` (the merged model's wide state layout). -/
def stackStates {m' : o → Type*} (x : ∀ i, m' i → ℝ) : (Σ i, m' i) → ℝ :=
  fun p => x p.1 p.2

/-- In block `k`, the merged linear layer `blockDiagonal' W` applied
to the stacked expert states returns exactly expert `k`'s output
`(W k *ᵥ x k) i`. -/
theorem step0_equivalence {m' n' : o → Type*} [∀ i, Fintype (n' i)]
    (W : ∀ i, Matrix (m' i) (n' i) ℝ)
    (x : ∀ i, n' i → ℝ) (k : o) (i : m' k) :
    (blockDiagonal' W *ᵥ stackStates x) ⟨k, i⟩ = (W k *ᵥ x k) i :=
  blockDiagonal'_mulVec_apply W (stackStates x) k i

end Hagi
