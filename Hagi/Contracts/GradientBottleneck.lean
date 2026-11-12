/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.LogitGrad
import Hagi.External.Flywheel.EckartYoungLower

set_option relaxedAutoImplicit false

/-!
# Gradient bottleneck bound via Eckart–Young

`gradient_bottleneck_bound`: any achievable logit update `Δ` whose
matrix has rank at most `k` leaves Frobenius residual at least the
squared tail of the singular values of the logit-gradient matrix
beyond `k`. In the paper's usage `k = 2D` for a rank-`D` head, so the
residual retains the tail beyond `2D`.

Honesty notes (premise-form statement):

* The achievable-update set is formalized as the premise `hΔ : Δ.rank
  ≤ k`. The head-derivation — a rank-`D` head forces achievable logit
  updates to have rank at most `2D` — is DEFERRED, as is the
  rectangular contexts-×-vocabulary carrier: `logitGradM` is the
  square `n × n` complex matrix view (real entries coerced) required
  by the Flywheel SVD API.
* The bound can be vacuous when `k ≥ n` (empty tail); the statement
  remains true.

The entire content is the definitions plus the rank premise: the
theorem is a direct corollary of `eckart_young_lower_bound` (C226)
applied to `logitGradM`. The row facts live in
`Hagi.Contracts.LogitGrad`.
-/

open scoped BigOperators

namespace Hagi.Contracts.GradientBottleneck

open Hagi.External.Flywheel.Matrix.FrobeniusNorm in
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Matrix view of the logit gradient over contexts and vocabulary
both indexed by `n` (square complex carrier required by the Flywheel
SVD API; real entries coerced). -/
noncomputable def logitGradM (z N : n → n → ℝ) : Matrix n n ℂ :=
  Matrix.of fun c v => (Hagi.Contracts.LogitGrad.logitGrad z N c v : ℂ)

/-- Gradient bottleneck bound: any achievable logit update `Δ` with
`Δ.rank ≤ k` leaves residual at least the squared singular-value tail
of `logitGradM z N` beyond `k`. Direct corollary of
`eckart_young_lower_bound`; see the module docstring for the
premise-form honesty notes. -/
theorem gradient_bottleneck_bound (z N : n → n → ℝ) (k : ℕ)
    (Δ : Matrix n n ℂ) (hΔ : Δ.rank ≤ k) :
    ∑ i, (Hagi.External.Flywheel.Matrix.SVD.truncatedSingularValues_tail
            (logitGradM z N) k i)^2
      ≤ ‖logitGradM z N - Δ‖^2 :=
  Hagi.External.Flywheel.Matrix.FrobeniusNorm.eckart_young_lower_bound
    (logitGradM z N) k Δ hΔ

end Hagi.Contracts.GradientBottleneck
