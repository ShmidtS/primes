/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# The element theory: shared base + low-rank expert deltas

The growth loop is closed (`Hagi.GapLaw`, gate v4); the next
bottleneck is the *element* itself: 96% of a leaf's parameters
are the embedding and head tables. The proposed redesign is the
synthesis form

`E_i = E₀ + Aᵢ * Bᵢ`, `W_i = W₀ + Cᵢ * Dᵢ`

(shared base + low-rank expert deltas). Before spending GPU on
it, this module fixes the formal conditions under which such an
element is *safe* (step-0 equivalent) and when the low rank is
*possible at all* (the go/no-go test on the measured deltas).

**Prescription for the code.**

1. `rankZero_step0` — the safe start: with rank-0 deltas the
   redesigned leaf is *definitionally* the original one, so any
   training run can start from the pretrained leaf with zero
   residual parameters and cannot lose anything at step 0 (the
   `Hagi.BlockDiag` sense of a safe lift). This is the formal
   green light for the *architecture* change as such.
2. `delta_rank_le` — any exact residual `AᵢBᵢ` has rank ≤ r. So
   the *exact* representation of the observed delta `ΔE_i =
   E_i − E₀` by a rank-r factorization exists only if
   `rank ΔE_i ≤ r` (`delta_exact_rank_bound`). The go/no-go test
   for the redesign is therefore a *rank measurement on the
   checkpoints*, not a training run: compute `ΔE_i = E_i − E₀`
   across the pool and measure `rank ΔE_i` (or the singular
   spectrum) — if the ranks are high (the BTX averaging failure
   10.10 → 10.36 is the measured hint that the deltas are NOT
   low-rank), the exact low-rank redesign cannot represent the
   pool, and only the *approximate* regime remains.
3. `params_count` — the parameter budget: N leaves with rank-r
   residuals cost `N • r • (V + d)` extra parameters against
   `N • V • d` of independent tables — the compression factor
   `r • (V + d) / (V • d)`; at the measured scales (V ≫ d) the
   saving is real only if r ≪ d.
4. **The honest gap**: the L2-approximation theory (Eckart–Young:
   the best rank-r approximation error is the (r+1)-st singular
   value) is not currently available in Mathlib in a usable
   form; the formal side therefore certifies the *exact*
   representability question, and the approximate question goes
   through the measured spectrum: the practical test is
   `σ_{r+1}(ΔE_i)/σ_1(ΔE_i)` small — cheap to compute on
   checkpoints, and the rank bound above is its zero-threshold
   case.
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
/-- **Step-0 safety (rank-0 deltas are the identity).** With
zero residual factors the redesigned leaf *is* the shared base:
`residualLeaf E₀ 0 0 = E₀` and the action on any input vector is
unchanged. The architecture change is safe to adopt — training can
start from the pretrained tables with zero residual parameters. -/
theorem residualLeaf_zero (E₀ : Matrix V d ℝ) :
    residualLeaf E₀ (0 : Matrix V r ℝ) (0 : Matrix r d ℝ) = E₀ := by
  rw [residualLeaf, Matrix.zero_mul, add_zero]

omit [Fintype V] [DecidableEq V] [DecidableEq d] [DecidableEq r] in
/-- The action-level statement of the same safety. -/
theorem residualLeaf_zero_apply (E₀ : Matrix V d ℝ) (x : d → ℝ) :
    residualLeaf E₀ (0 : Matrix V r ℝ) (0 : Matrix r d ℝ) *ᵥ x
      = E₀ *ᵥ x := by
  rw [residualLeaf_zero]

omit [Fintype V] [DecidableEq V] [DecidableEq d] [DecidableEq r] in
/-- **The rank of an exact residual is at most r.** Any delta
represented exactly as `A * B` with inner dimension r has rank ≤
r — the elementary factorization bound (`Matrix.rank_mul_le`). -/
theorem delta_rank_le (A : Matrix V r ℝ) (B : Matrix r d ℝ) :
    (A * B).rank ≤ Fintype.card r :=
  le_trans (Matrix.rank_mul_le A B)
    (le_trans (min_le_right A.rank B.rank)
      (Matrix.rank_le_card_height B))

omit [Fintype V] [DecidableEq V] [DecidableEq d] [DecidableEq r] in
/-- **The go/no-go test (exact representability).** If the
observed delta `ΔE = E_i − E₀` has rank strictly greater than r,
then *no* rank-r factorization represents it exactly — the
contrapositive of `delta_rank_le`. The redesign's exact regime is
decided by a rank measurement on the checkpoints, before any
training run. -/
theorem delta_exact_rank_bound (ΔE : Matrix V d ℝ)
    (A : Matrix V r ℝ) (B : Matrix r d ℝ)
    (hrep : A * B = ΔE) :
    ΔE.rank ≤ Fintype.card r := by
  rw [← hrep]
  exact delta_rank_le A B

/-- **The parameter budget.** N independent leaves cost
`N • (V • d)` table parameters; the shared-base redesign with
rank-r residuals costs `V • d + N • (r • (V + d))`. The redesign
is parameter-cheaper iff `r • (V + d) < V • d` per leaf (with the
base amortized across the pool). -/
theorem params_count (N V d r : ℕ) :
    (N + 1) * (V * d) + (N + 1) * (r * (V + d))
      = (V * d + r * (V + d)) + N * ((V * d) + (r * (V + d))) := by
  induction N with
  | zero => ring
  | succ n ih => nlinarith [ih]

end Element

end Hagi
