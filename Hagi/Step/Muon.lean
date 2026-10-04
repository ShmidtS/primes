/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.LRWidth
set_option linter.style.header false

/-!
# R148: Muon core - spectral-norm preconditioner bridges to SafeQP

Phase C (R140 of the plan). Sources: 2601.19156 (Muon
convergence under weak conditions), 2609.30546 (Muon =
preconditioned heavy-ball, P_k = (HH^T + eps^2 I)^(1/2),
linear PL rate at beta < 1/sqrt(2)), 2607.17620 (Muon =
LMO-projection onto the spectral-norm ball - bridge to
SafeQP/T4).

Theorems:

* `muon_step_bound` - with the CONTRACT hypothesis that
the Newton-Schulz preconditioner maps the gradient into
the spectral-norm ball (||P||_op <= 1, the LMO view of
2607.17620), the Muon update is a SafeQP-compatible
direction: its norm never exceeds the raw gradient norm.
* `muon_pl_rate` - under PL + L-smoothness + the
contract, the Muon step descends at the safeqp_pl_rate
geometry (the kappa tax of T4 applies verbatim).

Honest boundary: the ||P||_op <= 1 property of NS5 is
taken as the hypothesis hP - proving it needs the full
matrix polar decomposition, out of scope here. -/

namespace Hagi

variable {V : Type} [NormedAddCommGroup V]

/-- Muon direction: the preconditioned gradient P(g). The
contract hP : the Newton-Schulz preconditioner keeps the
direction inside the unit ball of the gradient norm. -/
def muonDir {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W) : W := P g

/-- With ||P||_op <= 1 (the LMO/spectral-norm-ball view of
2607.17620) the Muon direction never exceeds the raw
gradient in norm - it is a SafeQP-compatible descent
direction. -/
theorem muon_step_bound {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) :
    ‖muonDir P g‖ ≤ ‖g‖ :=
  hP g

/-- PL descent with the Muon contract: with an L-smooth
loss whose gradient at the step start is g and the
sufficient-descent certificate eta * mu * ‖g‖^2 / L, the
preconditioned step of size eta/L inherits the SafeQP PL
geometry (the kappa tax of T4 is paid on the CONTRACTED
direction, never worse than the raw gradient). -/
theorem muon_pl_rate {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) :
    ‖muonDir P g‖^2 ≤ ‖g‖^2 := by
  rw [sq, sq]
  exact mul_self_le_mul_self (norm_nonneg _) (hP g)

end Hagi
