/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.GuardedRobustSelection
import Hagi.Unified.ParetoLogit
set_option linter.style.header false

/-!
# Guarded robust selection for the scalar logistic controller

This is a one-step specialization of `guardedRobustNext` to the actual
`logitProblem`, with `logitEstimate` and guard radius `1 / 2`.  The selected
successor is always an actual feasible logit successor.  Without an estimated
upgrade it is exactly the stay state; in all cases its logistic cross-entropy
is no greater than the stay value.

An exact update requires both feasibility of action `1` and an estimated
upgrade.  The upgrade can alternatively be obtained from an explicit true-CE
drop of at least `1`; smaller drops need not pass the `2 * (1 / 2)` guard.
These are deterministic one-step statements, not probability, generalization,
or parameter-convergence claims.
-/

namespace Hagi.Unified.GuardedRobustLogit

open Hagi.Model
open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection
open Hagi.Unified.ParetoLogit
open Hagi.Unified.LogitCert

/-- The guarded robust successor specialized to the scalar logistic problem. -/
noncomputable def guardedLogitNext (eta : ℝ) (M C : ℕ) (w : ℝ) : ℝ :=
  guardedRobustNext (logitProblem eta) logitEstimate (1 / 2) w M C
    (0 : Fin 2) (logit_feasible_zero eta M C)

/-- The guarded successor is the actual step of some original feasible action. -/
theorem guardedLogitNext_exists (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∃ a ∈ feasible (logitProblem eta) M C,
      guardedLogitNext eta M C w = logitStepFun eta a w := by
  simpa only [guardedLogitNext, logitProblem_step] using
    (guardedRobustNext_exists (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2) (logit_feasible_zero eta M C))

/-- If no feasible action passes the estimate-margin guard, the actual
successor is exactly the stay state. -/
theorem guardedLogitNext_of_no_upgrade (eta : ℝ) (M C : ℕ) (w : ℝ)
    (h : ¬ estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    guardedLogitNext eta M C w = w := by
  unfold guardedLogitNext
  rw [guardedRobustNext_of_no_upgrade (logitProblem eta) logitEstimate (1 / 2)
    w M C (0 : Fin 2) (logit_feasible_zero eta M C) h]
  exact logitStepFun_zero eta w

/-- Unconditional one-step logistic-CE non-regression.  No positivity or
resource assumptions are needed: the error bound holds on every feasible
successor, including the always-feasible stay action. -/
theorem logitCE_guardedLogitNext_le (eta : ℝ) (M C : ℕ) (w : ℝ) :
    logitCE (guardedLogitNext eta M C w) ≤ logitCE w := by
  have h := guardedRobustNext_quality_ge_stay (logitProblem eta) logitEstimate
    (1 / 2) w M C (0 : Fin 2) (logit_feasible_zero eta M C)
    (fun a _ => le_of_eq (logitEstimate_error_action eta a w))
  change -logitCE w ≤ -logitCE (guardedLogitNext eta M C w) at h
  linarith only [h]

/-- A true-CE drop of at least `1` by action `1` supplies the exact
`2 * (1 / 2)` estimated-upgrade margin. -/
theorem estimatedUpgrade_of_logitCE_drop (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hdrop : 1 ≤ logitCE w - logitCE (w + eta / (1 + Real.exp w))) :
    estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2) := by
  refine ⟨1, logit_feasible_one eta heta M C hM hC, ?_⟩
  simp only [logitProblem_step, logitStepFun_zero, logitStepFun_one]
  unfold logitEstimate
  norm_num
  linarith only [hdrop]

/-- With action `1` feasible and the estimated-upgrade guard active, the
wrapper executes the existing robust logistic update exactly. -/
theorem guardedLogitNext_eq_update_of_upgrade (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    guardedLogitNext eta M C w = w + eta / (1 + Real.exp w) := by
  unfold guardedLogitNext guardedRobustNext
  rw [ite_eq_left hup]
  exact logit_robustNext eta heta w M C (logit_feasible_zero eta M C)
    (logit_feasible_one eta heta M C hM hC)

/-- The same exact update follows from an explicit true-CE drop of at least
`1`, rather than from a pre-established estimated-upgrade witness. -/
theorem guardedLogitNext_eq_update_of_logitCE_drop (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hdrop : 1 ≤ logitCE w - logitCE (w + eta / (1 + Real.exp w))) :
    guardedLogitNext eta M C w = w + eta / (1 + Real.exp w) := by
  exact guardedLogitNext_eq_update_of_upgrade eta heta M C hM hC w
    (estimatedUpgrade_of_logitCE_drop eta heta M C hM hC w hdrop)

/-- Under the exact-update resources and an active guard, logistic CE strictly
decreases by the existing scalar descent theorem. -/
theorem logitCE_guardedLogitNext_lt_of_upgrade (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    logitCE (guardedLogitNext eta M C w) < logitCE w := by
  rw [guardedLogitNext_eq_update_of_upgrade eta heta M C hM hC w hup]
  exact descent_step_strict w eta heta

end Hagi.Unified.GuardedRobustLogit
