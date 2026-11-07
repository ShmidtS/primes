/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.GuardedRobustTrajectory
import Hagi.Unified.GuardedRobustLogit
import Hagi.Contracts.ObjectiveTrajectory
set_option linter.style.header false

/-!
# Guarded scalar logistic-CE trajectories

The concrete guarded logistic successor determines a recursive scalar path.
Its actual value `-logitCE` is monotone, so logistic cross-entropy is antitone
and converges to its infimum. The actual one-step CE drops telescope exactly,
are summable, tend to zero, and have total sum at most the initial CE.

These are unconditional statements for the fixed scalar guarded controller.
They do not identify the limiting CE with a global optimum or `0`, and do not
assert convergence of the raw states, estimator calibration, generalization,
or cumulative physical resource bounds.
-/

namespace Hagi.Contracts.GuardedLogitTrajectory

open Hagi.Model
open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustTrajectory
open Hagi.Unified.GuardedRobustLogit
open Hagi.Unified.ParetoLogit
open Hagi.Unified.LogitCert
open Filter Topology

/-- The recursive path of the concrete guarded logistic controller, using the
same fixed estimate and exact error radius `1 / 2` at every step. -/
noncomputable def guardedLogitPath (eta : ℝ) (M C : ℕ) (w : ℝ) : ℕ → ℝ :=
  guardedRobustPath (logitProblem eta) (fun _ => logitEstimate) (fun _ => 1 / 2)
    M C (0 : Fin 2) (logit_feasible_zero eta M C) w

@[simp] theorem guardedLogitPath_zero (eta : ℝ) (M C : ℕ) (w : ℝ) :
    guardedLogitPath eta M C w 0 = w := by
  simp only [guardedLogitPath, guardedRobustPath_zero]

/-- Every successor is definitionally the reviewed concrete guarded logistic
successor applied to the actual current path state. -/
@[simp] theorem guardedLogitPath_succ (eta : ℝ) (M C : ℕ) (w : ℝ) (t : ℕ) :
    guardedLogitPath eta M C w (t + 1) =
      guardedLogitNext eta M C (guardedLogitPath eta M C w t) := by
  simp only [guardedLogitPath, guardedRobustPath_succ, guardedLogitNext]

private theorem logitProblem_stay_step (eta : ℝ) (w : ℝ) :
    (logitProblem eta).step (0 : Fin 2) w = w :=
  logitStepFun_zero eta w

/-- The exact estimator error is available on every feasible successor at the
actual current recursive state, without positivity or resource assumptions. -/
private theorem guardedLogitPath_error_bound (eta : ℝ) (M C : ℕ) (w : ℝ)
    (t : ℕ) (a : Fin 2) (_ha : a ∈ feasible (logitProblem eta) M C) :
    |(logitProblem eta).value
          ((logitProblem eta).step a (guardedLogitPath eta M C w t)) -
        logitEstimate ((logitProblem eta).step a
          (guardedLogitPath eta M C w t))| ≤ 1 / 2 := by
  exact le_of_eq (logitEstimate_error_action eta a (guardedLogitPath eta M C w t))

private theorem guardedLogitPath_quality_monotone (eta : ℝ) (M C : ℕ) (w : ℝ) :
    Monotone (fun t =>
      (logitProblem eta).value (guardedLogitPath eta M C w t)) := by
  exact guardedRobustPath_quality_monotone (logitProblem eta)
    (fun _ => logitEstimate) (fun _ => 1 / 2) M C (0 : Fin 2)
    (logit_feasible_zero eta M C) w (logitProblem_stay_step eta)
    (guardedLogitPath_error_bound eta M C w)

/-- Actual logistic CE never increases along the guarded path, for every step
size and all logical per-action resource limits. -/
theorem guardedLogitPath_logitCE_antitone (eta : ℝ) (M C : ℕ) (w : ℝ) :
    Antitone (fun t => logitCE (guardedLogitPath eta M C w t)) := by
  intro s t hst
  have h := guardedLogitPath_quality_monotone eta M C w hst
  change -logitCE (guardedLogitPath eta M C w s) ≤
    -logitCE (guardedLogitPath eta M C w t) at h
  exact neg_le_neg_iff.mp h

/-- Nonnegative antitone logistic CE converges to its real infimum; no value
for that infimum beyond the convergence statement is asserted. -/
theorem guardedLogitPath_logitCE_tendsto_ciInf (eta : ℝ) (M C : ℕ) (w : ℝ) :
    Tendsto (fun t => logitCE (guardedLogitPath eta M C w t)) atTop
      (𝓝 (⨅ t, logitCE (guardedLogitPath eta M C w t))) := by
  exact Hagi.Contracts.ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (guardedLogitPath_logitCE_antitone eta M C w)
    (fun t => logitCE_nonneg _)

private theorem guardedLogitPath_value_le_zero
    (eta : ℝ) (M C : ℕ) (w : ℝ) (t : ℕ) :
    (logitProblem eta).value (guardedLogitPath eta M C w t) ≤ 0 := by
  simp only [logitProblem_value, neg_nonpos]
  exact logitCE_nonneg _

/-- The actual logistic-CE decrease at one guarded step. -/
noncomputable def guardedLogitDrop (eta : ℝ) (M C : ℕ) (w : ℝ) (t : ℕ) : ℝ :=
  logitCE (guardedLogitPath eta M C w t) -
    logitCE (guardedLogitPath eta M C w (t + 1))

/-- Every actual one-step logistic-CE drop is nonnegative. -/
theorem guardedLogitDrop_nonneg (eta : ℝ) (M C : ℕ) (w : ℝ) (t : ℕ) :
    0 ≤ guardedLogitDrop eta M C w t := by
  exact sub_nonneg.mpr
    (guardedLogitPath_logitCE_antitone eta M C w (Nat.le_succ t))

/-- Negating the model value reverses subtraction, so an actual CE drop is
exactly the corresponding generic actual quality gain. -/
private theorem guardedLogitDrop_eq_gain (eta : ℝ) (M C : ℕ) (w : ℝ) (t : ℕ) :
    guardedLogitDrop eta M C w t =
      guardedRobustGain (logitProblem eta) (fun _ => logitEstimate)
        (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w t := by
  simp only [guardedLogitDrop, guardedRobustGain, guardedLogitPath,
    logitProblem_value]
  ring

/-- Finite actual CE drops telescope exactly, including at horizon zero. -/
theorem guardedLogitDrop_sum_range (eta : ℝ) (M C : ℕ) (w : ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, guardedLogitDrop eta M C w t =
      logitCE (guardedLogitPath eta M C w 0) -
        logitCE (guardedLogitPath eta M C w T) := by
  calc
    ∑ t ∈ Finset.range T, guardedLogitDrop eta M C w t =
        ∑ t ∈ Finset.range T,
          guardedRobustGain (logitProblem eta) (fun _ => logitEstimate)
            (fun _ => 1 / 2) M C (0 : Fin 2)
            (logit_feasible_zero eta M C) w t := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact guardedLogitDrop_eq_gain eta M C w t
    _ = (logitProblem eta).value
          (guardedRobustPath (logitProblem eta) (fun _ => logitEstimate)
            (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w T) -
        (logitProblem eta).value
          (guardedRobustPath (logitProblem eta) (fun _ => logitEstimate)
            (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w 0) :=
      guardedRobustGain_sum_range (logitProblem eta) (fun _ => logitEstimate)
        (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w T
    _ = logitCE (guardedLogitPath eta M C w 0) -
        logitCE (guardedLogitPath eta M C w T) := by
      simp only [logitProblem_value, guardedLogitPath]
      ring

/-- Actual logistic-CE drops are summable by the generic gain theorem with
upper quality bound `B = 0`. -/
theorem guardedLogitDrop_summable (eta : ℝ) (M C : ℕ) (w : ℝ) :
    Summable (guardedLogitDrop eta M C w) := by
  have hfun : guardedLogitDrop eta M C w =
      guardedRobustGain (logitProblem eta) (fun _ => logitEstimate)
        (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w := by
    funext t
    exact guardedLogitDrop_eq_gain eta M C w t
  rw [hfun]
  exact guardedRobustGain_summable (logitProblem eta) (fun _ => logitEstimate)
    (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w
    (logitProblem_stay_step eta) (guardedLogitPath_error_bound eta M C w)
    0 (guardedLogitPath_value_le_zero eta M C w)

/-- Actual one-step logistic-CE drops tend to zero; this does not imply that
raw scalar states converge or that the controller stops changing state. -/
theorem guardedLogitDrop_tendsto_zero (eta : ℝ) (M C : ℕ) (w : ℝ) :
    Tendsto (guardedLogitDrop eta M C w) atTop (𝓝 0) := by
  have hfun : guardedLogitDrop eta M C w =
      guardedRobustGain (logitProblem eta) (fun _ => logitEstimate)
        (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w := by
    funext t
    exact guardedLogitDrop_eq_gain eta M C w t
  rw [hfun]
  exact guardedRobustGain_tendsto_zero (logitProblem eta)
    (fun _ => logitEstimate) (fun _ => 1 / 2) M C (0 : Fin 2)
    (logit_feasible_zero eta M C) w (logitProblem_stay_step eta)
    (guardedLogitPath_error_bound eta M C w) 0
    (guardedLogitPath_value_le_zero eta M C w)

/-- Total actual logistic-CE decrease is at most the initial CE. -/
theorem guardedLogitDrop_tsum_le (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∑' t, guardedLogitDrop eta M C w t ≤
      logitCE (guardedLogitPath eta M C w 0) := by
  calc
    ∑' t, guardedLogitDrop eta M C w t =
        ∑' t, guardedRobustGain (logitProblem eta) (fun _ => logitEstimate)
          (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w t := by
      apply tsum_congr
      intro t
      exact guardedLogitDrop_eq_gain eta M C w t
    _ ≤ 0 - (logitProblem eta).value
        (guardedRobustPath (logitProblem eta) (fun _ => logitEstimate)
          (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w 0) :=
      guardedRobustGain_tsum_le (logitProblem eta) (fun _ => logitEstimate)
        (fun _ => 1 / 2) M C (0 : Fin 2) (logit_feasible_zero eta M C) w
        (logitProblem_stay_step eta) (guardedLogitPath_error_bound eta M C w)
        0 (guardedLogitPath_value_le_zero eta M C w)
    _ = logitCE (guardedLogitPath eta M C w 0) := by
      simp only [logitProblem_value, guardedLogitPath, zero_sub, neg_neg]

end Hagi.Contracts.GuardedLogitTrajectory
