/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.CertChecker
import Hagi.Theory.HoldoutRisk

/-!
# Certified CE training: the holdout-risk interpretation bridge (C442)

The certified CE training loop (scripts/bench_bridge.py `--mode
cert-ce`) feeds `Hagi.Runtime.CertChecker` with trajectories of a
rational-softmax cross-entropy surrogate: exact `Fraction` gradient
descent with `η = 1/L` (`L` the Frobenius smoothness estimate of the
linear block, the BlockSmooth pattern), per-step executable
admission, and holdout risk telemetry.  This module is the
meaning-level bridge:

* `RiskChannel` — the accuracy contract for the risk fields: the
  `risk`/`risk'` readouts of a step equal the `holdoutMean` of the
  model's loss table on the holdout sample, before/after the update
  (the C435 tie: holdout telemetry on a finite dataset, honest in
  the sense that it is NOT required to decrease);
* `cert_ce_interpretation` — a passing executable trajectory check
  whose data describes the real transitions and whose risk fields
  ride the risk channel yields BOTH (a) the certified train-objective
  telescope (via `Hagi.Runtime.checkTrajectory_sound` — the train CE
  decreases by the declared drops) AND (b) the terminal risk readout
  equals the holdout mean of the final model — the end-to-end reading
  of a certified training run.

## Honest boundaries (pins)

1. The Python trainer's `L` is a Frobenius ESTIMATE (as the
   `BlockSmooth` empirical smoothness premise), not a certified
   Hessian bound for the surrogate; what is certified is each step's
   exact admission (`checkStep`), not the a priori smoothness claim.
2. The holdout sample here is a fixed `k`-point draw; the risk
   channel is exact equality of readouts, and — per the C435
   selection-bias results — nothing here claims the holdout estimate
   decreases or is unbiased under data-dependent model selection.
-/

set_option linter.style.header false

namespace Hagi.Theory.CertCEHoldout

open Hagi.Runtime Hagi.Theory.HoldoutRisk
open Hagi.Cert (SystemMetrics StepObligations FloorsKept)

variable {Ω Θ : Type}

/-! ## The risk telemetry channel -/

/-- Accuracy contract for the risk fields: the `risk`/`risk'`
readouts of one certificate step equal the holdout mean of the
model's loss table on the holdout sample `ωs`, at the pre-state
model `θ` and the post-state model `θ'` respectively. -/
def RiskChannel (ℓ : Θ → Ω → ℝ) (θ θ' : Θ) {k : ℕ} (ωs : Fin k → Ω)
    (d : CertStepData) : Prop :=
  (d.risk : ℝ) = holdoutMean (ℓ θ) ωs
    ∧ (d.risk' : ℝ) = holdoutMean (ℓ θ') ωs

/-! ## The interpretation theorem -/

/-- **Certified CE interpretation**: if the executable trajectory
check passes, every step describes the real system transitions, and
the risk fields ride the holdout risk channel, then (a) the
certified telescope applies — the train objective at the terminal
state is bounded by the initial objective minus the sum of declared
drops (the train CE decreases), and (b) the terminal risk readout is
exactly the holdout mean of the final model on the holdout sample. -/
theorem cert_ce_interpretation {S TaskId : Type}
    {M : SystemMetrics S TaskId} {obl : StepObligations TaskId}
    (t : ℕ → S) (θ : ℕ → Θ) (ℓ : Θ → Ω → ℝ) {k : ℕ} (ωs : Fin k → Ω)
    (start : ℚ) (ds : List CertStepData)
    (hacc : ∀ j, Describes M (t j) (t (j + 1)) (ds.getD j default))
    (hfl : ∀ j : ℕ, FloorsKept M obl (t (j + 1)))
    (hrisk : ∀ j, j < ds.length → RiskChannel ℓ (θ j) (θ (j + 1)) ωs
      (ds.getD j default))
    (hne : ds ≠ [])
    (h : checkTrajectory start ds = true) :
    M.objective (t ds.length) ≤ M.objective (t 0)
        - ∑ j : Fin ds.length, ((ds.getD ↑j default).drop : ℝ)
      ∧ ((ds.getD (ds.length - 1) default).risk' : ℝ)
          = holdoutMean (ℓ (θ ds.length)) ωs := by
  refine ⟨checkTrajectory_sound t start ds hacc hfl h, ?_⟩
  have hlen : 0 < ds.length := List.length_pos_iff.mpr hne
  have h1 := hrisk (ds.length - 1) (by omega)
  rw [Nat.sub_add_cancel hlen] at h1
  exact h1.2

end Hagi.Theory.CertCEHoldout
