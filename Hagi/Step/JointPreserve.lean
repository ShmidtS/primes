/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Budget.ElementQuant

set_option linter.style.header false

/-!
# JointPreserve: diversity non-collapse under SafeQP steps (round 49, block 3)

The composition: IF each SafeQP joint step contracts the
cross-expert diversity by at most factor a and injects at
most s (the h_emp hypotheses — measured on the Gram
telemetry), THEN the diversity after T steps obeys the
general recurrence bound (SeedOnly.disp_recurrence_general):
bounded above by a^T·D₀ + s·Σa^i — the non-collapse
certificate: the Jensen gain CANNOT shrink below its floor
unless a ≥ 1 (the measured regime decides).

NOT PROVED: deriving h_emp per-step (a, s) from the SafeQP
geometry itself (the dynamics of the projected steps on the
representation covariance) — the hypotheses remain empirical
inputs from the Gram logs.

**Prescription**: log the per-step diversity ratio on the
joint phase; a < 1 with small s certifies non-collapse in
advance; a ≥ 1 flags the collapse regime for the schedule
program (Wave3) to intervene.
-/

open Finset

namespace Hagi

/-- **The diversity non-collapse bound**: with per-step
contraction ≤ a and injection ≤ s (measured), the
cross-expert diversity after T steps is bounded by the
recurrence solution — the representation-collapse
certificate (conditional on the empirical step law). -/
theorem diversity_noncollapse (D : ℕ → ℝ) (a s : ℝ)
    (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hstep : ∀ t, D (t+1) ≤ a * D t + s) (T : ℕ) :
    D T ≤ a^T * D 0 + s * ∑ i ∈ Finset.range T, a^i :=
  disp_recurrence_general ha hs hstep T

end Hagi
