/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# R263 (audit §2.4): the canonical scalar HAGI potential

One definition of Φ_HAGI = E + λR + ν·max(0, Q_target − Q)
(audit: `hagiPotential` was defined twice with different
signatures — `ModeState` and `Certificates`). Both callers
delegate here; the state-level `ModeState.hagiPotential`
projects a `GenState` onto these scalars.
-/

open Real

namespace Hagi.Foundations

/-- The canonical scalar HAGI potential Φ = E + λR +
ν·max(0, Q_target − Q). The max(0,·) makes the generalization
penalty inert above target and active below. -/
noncomputable def hagiPotential (E R nu qTarget q : ℝ) (lam : ℝ) : ℝ :=
  E + lam * R + nu * max 0 (qTarget - q)

/-- β is a monotone functional of the potential: the penalty
drop bound used by every caller (moved from Certificates so
the canonical module carries the law, not just the def). -/
lemma hagiPotential_penalty_drop (qTarget q q' epsQ : ℝ)
    (heps : 0 ≤ epsQ) (hdrop : q - epsQ ≤ q') :
    max 0 (qTarget - q') ≤ max 0 (qTarget - q) + epsQ := by
  have h1 : qTarget - q' ≤ qTarget - q + epsQ := by linarith
  have hkey : qTarget - q' ≤ max 0 (qTarget - q) + epsQ := by
    rcases le_total 0 (qTarget - q) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  rcases le_total 0 (qTarget - q') with h | h
  · rw [max_eq_right h]; exact hkey
  · rw [max_eq_left h]
    positivity

end Hagi.Foundations
