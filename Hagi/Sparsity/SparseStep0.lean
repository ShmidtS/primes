/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.RecursiveGrowth
set_option linter.style.header false

/-!
# R60: sparse step-0 preservation

Block II.1 of the grand-unified roadmap: at inference scale
(thousands of specialists), HAGI must route each token to a
few branches. The certificate: with the orthonormal (Hadamard)
branch basis, dropping branches changes the output by EXACTLY
the tail energy (`gating_tail_bound`, R53). This module adds
the decision form: routing to the top-k coefficients with
tail energy below tol² keeps the merged output within tol of
the dense merge — the sparse step-0 preservation certificate,
independent of the number of dropped branches.
-/

open Finset Real

namespace Hagi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Sparse step-0 preservation**: if the tail energy of the
routed-out coefficients is below tol², the sparse merge
approximates the dense merge within tol — for ANY number of
dropped branches (the certificate scales with the tail, not
with N). -/
theorem sparse_step0 {v : ι → E} (hv : Orthonormal ℝ v)
    (c : ι → ℝ) (s : Finset ι) (tol : ℝ) (htol : 0 ≤ tol)
    (htail : ∑ i ∈ sᶜ, c i ^ 2 < tol ^ 2) :
    ‖(∑ i, c i • v i) - ∑ i ∈ s, c i • v i‖ < tol := by
  have hgt := gating_tail_bound hv c s
  have hsq : ‖(∑ i, c i • v i) - ∑ i ∈ s, c i • v i‖ < tol := by
    by_contra hcon
    push Not at hcon
    have hnn : 0 ≤ ‖(∑ i, c i • v i) - ∑ i ∈ s, c i • v i‖ := norm_nonneg _
    have hms : tol * tol ≤ ‖(∑ i, c i • v i) - ∑ i ∈ s, c i • v i‖ * ‖(∑ i, c i • v i) - ∑ i ∈ s, c i • v i‖ :=
      mul_self_le_mul_self htol hcon
    have hn2 : tol ^ 2 ≤ ‖(∑ i, c i • v i) - ∑ i ∈ s, c i • v i‖ ^ 2 := by
      rw [sq, sq]
      exact hms
    rw [hgt] at hn2
    exact absurd hn2 (not_le.mpr htail)
  exact hsq

end Hagi
