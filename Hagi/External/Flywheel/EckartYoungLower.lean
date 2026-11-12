/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import Hagi.External.Flywheel.FrobeniusNorm

/-!
# General Eckart-Young Frobenius lower bound

For any target `B` of rank at most `k`, the Frobenius error to `A` is at
least the squared tail of the singular values of `A`:

`∑ i, (truncatedSingularValues_tail A k i)^2 ≤ ‖A - B‖^2`.

This is the matching LOWER bound for the optimality statement
`eckart_young_frobenius`: since the error of the truncated SVD itself is
exactly the tail sum (`frobenius_error_truncatedSVD`), optimality of
`truncatedSVD` is equivalent to this tail-sum lower bound holding for
every rank-`k` approximant.

## References

[1] Eckart, C. & Young, G. (1936). The approximation of one matrix by
    another of lower rank. Psychometrika 1(3), 211–218.

Created: 2026-11-12
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

set_option relaxedAutoImplicit false

namespace Hagi.External.Flywheel.Matrix.FrobeniusNorm

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- General Eckart-Young lower bound (tail-sum form): any matrix `B`
with `B.rank ≤ k` leaves Frobenius error at least the squared tail of
the singular values of `A`. Closes the rank-one gap of
`truncatedSVD_rank1_identity` in full generality. -/
theorem eckart_young_lower_bound (A : Matrix n n ℂ) (k : ℕ)
    (B : Matrix n n ℂ) (hB : B.rank ≤ k) :
    ∑ i, (Matrix.SVD.truncatedSingularValues_tail A k i)^2 ≤ ‖A - B‖^2 := by
  have h_opt := eckart_young_frobenius A k B hB
  have h_err := frobenius_error_truncatedSVD A k
  calc ∑ i, (Matrix.SVD.truncatedSingularValues_tail A k i)^2
      = ‖A - Matrix.SVD.truncatedSVD A k‖^2 := h_err.symm
    _ ≤ ‖A - B‖^2 := by
      nlinarith [h_opt, norm_nonneg (A - B),
        norm_nonneg (A - Matrix.SVD.truncatedSVD A k)]

end Hagi.External.Flywheel.Matrix.FrobeniusNorm
