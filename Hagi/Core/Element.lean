/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Element theory: shared base + low-rank expert deltas

The redesigned leaf is the synthesis form `E₀ + A * B` (shared
base + low-rank residual; `residualLeaf`).

* `residualLeaf_zero`, `residualLeaf_zero_apply` — with zero
  residual factors the redesigned leaf is exactly the base.
* `delta_rank_le` — an exact residual `A * B` has rank at most
  `Fintype.card r`; `delta_exact_rank_bound` — if `A * B = ΔE`
  then `ΔE.rank ≤ Fintype.card r`.
* `params_count` — arithmetic identity behind the parameter
  budget of `N + 1` leaves sharing a base.

The L2-approximation theory (Eckart-Young) is not formalized
here; only exact representability is certified.
-/

open scoped Matrix

namespace Hagi

section Element

variable {V d r : Type*} [Fintype V] [Fintype d] [Fintype r]
  [DecidableEq V] [DecidableEq d] [DecidableEq r]

/-- The redesigned leaf: shared base + low-rank residual deltas. -/
def residualLeaf (E₀ : Matrix V d ℝ) (A : Matrix V r ℝ)
    (B : Matrix r d ℝ) : Matrix V d ℝ := E₀ + A * B

omit [Fintype V] [Fintype d] [DecidableEq V] [DecidableEq d] [DecidableEq r] in
/-- With zero residual factors the redesigned leaf is exactly the
base: `residualLeaf E₀ 0 0 = E₀`. -/
theorem residualLeaf_zero (E₀ : Matrix V d ℝ) :
    residualLeaf E₀ (0 : Matrix V r ℝ) (0 : Matrix r d ℝ) = E₀ := by
  rw [residualLeaf, Matrix.zero_mul, add_zero]

omit [Fintype V] [DecidableEq V] [DecidableEq d] [DecidableEq r] in
/-- Action-level form of `residualLeaf_zero`: with zero residual
factors, `residualLeaf E₀ 0 0 *ᵥ x = E₀ *ᵥ x`. -/
theorem residualLeaf_zero_apply (E₀ : Matrix V d ℝ) (x : d → ℝ) :
    residualLeaf E₀ (0 : Matrix V r ℝ) (0 : Matrix r d ℝ) *ᵥ x
      = E₀ *ᵥ x := by
  rw [residualLeaf_zero]

omit [Fintype V] [DecidableEq V] [DecidableEq d] [DecidableEq r] in
/-- An exact residual `A * B` with inner dimension `r` has rank at
most `Fintype.card r` (via `Matrix.rank_mul_le`). -/
theorem delta_rank_le (A : Matrix V r ℝ) (B : Matrix r d ℝ) :
    (A * B).rank ≤ Fintype.card r :=
  le_trans (Matrix.rank_mul_le A B)
    (le_trans (min_le_right A.rank B.rank)
      (Matrix.rank_le_card_height B))

omit [Fintype V] [DecidableEq V] [DecidableEq d] [DecidableEq r] in
/-- If `A * B = ΔE`, then `ΔE.rank ≤ Fintype.card r` (contrapositive:
a delta of rank `> card r` has no exact rank-r factorization). -/
theorem delta_exact_rank_bound (ΔE : Matrix V d ℝ)
    (A : Matrix V r ℝ) (B : Matrix r d ℝ)
    (hrep : A * B = ΔE) :
    ΔE.rank ≤ Fintype.card r := by
  rw [← hrep]
  exact delta_rank_le A B

/-- Parameter-budget identity: the total cost of `N + 1` leaves
each carrying a shared `V • d` base and a rank-`r` residual
`r • (V + d)` decomposes as one leaf's cost plus `N` copies. -/
theorem params_count (N V d r : ℕ) :
    (N + 1) * (V * d) + (N + 1) * (r * (V + d))
      = (V * d + r * (V + d)) + N * ((V * d) + (r * (V + d))) := by
  induction N with
  | zero => ring
  | succ n ih => nlinarith [ih]

end Element

end Hagi
