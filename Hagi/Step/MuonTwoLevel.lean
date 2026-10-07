/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# MuonTwoLevel — exact orthogonalization vs NS approximation
(plan §2 R225; sources 2502.16982, 2609.36600 Thm 4.1)

The two-level structure of the Muon preconditioner. What is
PROVED here is the level-2 gap ACCOUNTING:

LEVEL 1 (contract, not proved here): the ideal update
O = U·Vᵀ (SVD of the gradient) is orthogonal — spectral
norm 1, i.e. the R224 premise C = 1 at the exact level
(taken as hypothesis there).

LEVEL 2 (proved): `ns_gap_scaled` — the squared NS
deviation Σᵢ (p(σᵢ) − 1)² ≤ r · maxᵢ (p(σᵢ) − 1)²: the
gap budget factorizes into rank times the worst POINTWISE
polynomial error on the singular spectrum. NOT proved
here: the Frobenius identity ‖U·p(Σ)·Vᵀ − U·Vᵀ‖_F =
‖p(Σ) − I‖_F (requires the U/V-orthogonality machinery),
the polynomial coefficients, and any NS iteration
convergence — the accounting bound above is the module's
full content.
-/

namespace Hagi

open Finset

/-- **The per-singular-value accounting**: the squared NS
gap Σᵢ (p(σᵢ) − 1)² ≤ r · maxᵢ (p(σᵢ) − 1)²: the gap budget
factorizes into rank × worst pointwise polynomial error —
the NS step-count/spectrum tradeoff in one line (the
2609.36600 SNR regime split is the split of the max term). -/
theorem ns_gap_scaled (r : ℕ) (dev : Fin r → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hdev : ∀ i, (dev i)^2 ≤ M) :
    ∑ i, (dev i)^2 ≤ r * M := by
  have h1 : ∑ i, (dev i)^2 ≤ ∑ _i, M :=
    Finset.sum_le_sum fun i _ => hdev i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1
  exact h1


end Hagi
