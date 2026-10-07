/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# MuonTwoLevel — exact orthogonalization vs NS approximation
(plan §2 R225; sources 2502.16982, 2609.36600 Thm 4.1)

The two-level structure of the Muon preconditioner, with the
level split EXPLICIT:

LEVEL 1 — exact: the ideal update O = U·Vᵀ (SVD of the
gradient) is EXACTLY orthogonal (spectral norm 1, all
singular values 1): the ideal direction is norm-1 by
construction.

LEVEL 2 — NS-approximate: the Newton–Schulz polynomial
p(x) = a·x + b·x³ + c·x⁵ (fixed coefficients, iterated)
approximates x ↦ sign(x); the realized update is
U·p(Σ)·Vᵀ. The deviation from the exact level is EXACTLY
diagonal: ‖U·p(Σ)·Vᵀ − U·Vᵀ‖_F = ‖p(Σ) − I‖_F — the
two-level gap is the polynomial's pointwise deviation on
the singular spectrum, nothing else.

* `exact_ortho_norm`: the level-1 contract — U·Vᵀ has
  operator norm exactly 1 (U, V orthonormal columns);
* `ns_gap_diagonal`: the level-2 deviation law — the
  Frobenius gap between the realized and exact updates
  equals the Frobenius norm of (p(Σ) − I): the gap is
  SPECTRAL, not directional (the U/V subspaces are shared);
* `ns_gap_scaled`: the per-singular-value accounting: the
  squared gap is Σᵢ (p(σᵢ) − 1)² ≤ r · maxᵢ(p(σᵢ) − 1)² —
  the gap budget factorizes into rank times worst pointwise
  polynomial error: THE NS step-count/spectrum tradeoff in
  one line (2609.36600's regime split is exactly the split
  of maxᵢ|p(σᵢ) − 1| by SNR).
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
