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

set_option relaxedAutoImplicit false

/-!
# Discrete progress and finite stabilization of guarded logistic paths

For the concrete two-action logistic controller, an active estimate-margin
upgrade has an action-`1` witness whose true logistic-CE decrease is at least
`1`. Consequently, every actual one-step CE drop is either zero or at least
one, without assuming positivity of the step size or resource limits in
advance: those facts are derived from the active witness.

The number of strictly positive outer CE-improvement steps is bounded by the
initial CE. If that initial CE is below one, every guarded successor stays at
its initial scalar state. In all cases, convergence of drops to zero and the
discrete floor imply that the raw path is eventually constant and converges
to its finite eventual value. These statements do not assert a global optimum,
zero limiting CE, physical compute bounds, or convergence of arbitrary model
parameters.
-/

namespace Hagi.Contracts.GuardedLogitProgress

open Hagi.Model
open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection
open Hagi.Unified.GuardedRobustLogit
open Hagi.Unified.ParetoLogit
open Hagi.Unified.LogitCert
open Hagi.Contracts.GuardedLogitTrajectory
open Hagi.Unified.FixedBiasBinaryProgress
open Filter Topology

private theorem fixedBiasLogit_stay_step (eta : ℝ) :
    ∀ w, (logitProblem eta).step (0 : Fin 2) w = w := by
  intro w
  exact logitStepFun_zero eta w

private theorem logitUpgrade_one_spec (eta : ℝ) (M C : ℕ) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    (1 : Fin 2) ∈ feasible (logitProblem eta) M C ∧
      1 ≤ logitCE w - logitCE (w + eta / (1 + Real.exp w)) := by
  obtain ⟨a, ha, hmargin⟩ := hup
  have ha_one : a = 1 := by
    fin_cases a
    · exfalso
      have hself : logitEstimate w + 2 * (1 / 2) ≤ logitEstimate w := by
        simpa [logitProblem_step, logitStepFun] using hmargin
      unfold logitEstimate at hself
      linarith
    · rfl
  subst a
  refine ⟨ha, ?_⟩
  simp only [logitProblem_step, logitStepFun_zero, logitStepFun_one] at hmargin
  unfold logitEstimate at hmargin
  linarith

private theorem logitUpgrade_resources (eta : ℝ) (M C : ℕ) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    1 ≤ M ∧ 2 ≤ C := by
  have hfeasible := (logitUpgrade_one_spec eta M C w hup).1
  have hresources := (mem_feasible.mp hfeasible).2
  constructor
  · simpa [logitProblem] using hresources.1
  · simpa [logitProblem] using hresources.2

private theorem logitUpgrade_pos_eta (eta : ℝ) (M C : ℕ) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    0 < eta := by
  have hdrop := (logitUpgrade_one_spec eta M C w hup).2
  have hce : logitCE (w + eta / (1 + Real.exp w)) < logitCE w := by
    linarith only [hdrop]
  have hw : w < w + eta / (1 + Real.exp w) := by
    rcases lt_trichotomy (w + eta / (1 + Real.exp w)) w with hlt | heq | hgt
    · have hcontra := logitCE_strictAnti hlt
      linarith only [hce, hcontra]
    · exfalso
      rw [heq] at hce
      exact lt_irrefl _ hce
    · exact hgt
  have hstep : 0 < eta / (1 + Real.exp w) := by
    linarith only [hw]
  have hdenominator : 0 < 1 + Real.exp w := by positivity
  exact (div_pos_iff_of_pos_right hdenominator).mp hstep

/-- An active estimate-margin guard executes the actual scalar update for
arbitrary parameters. Positivity and resource bounds are derived from the
active action-`1` witness rather than added as hypotheses. -/
theorem guardedLogitNext_eq_update_of_any_upgrade (eta : ℝ) (M C : ℕ) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    guardedLogitNext eta M C w = w + eta / (1 + Real.exp w) := by
  have hresources := logitUpgrade_resources eta M C w hup
  have heta := logitUpgrade_pos_eta eta M C w hup
  exact guardedLogitNext_eq_update_of_upgrade eta heta M C hresources.1
    hresources.2 w hup

/-- The original logit path is definitionally the shared fixed-bias path;
the only estimate change is the exact `value = -logitCE` simplification. -/
private theorem guardedLogitPath_eq_fixedBiasBinaryPath
    (eta : ℝ) (M C : ℕ) (w : ℝ) :
    guardedLogitPath eta M C w =
      fixedBiasBinaryPath (logitProblem eta) M C (logit_feasible_zero eta M C) w := by
  unfold guardedLogitPath fixedBiasBinaryPath
  have hestimate : (fun _ : ℕ => logitEstimate) =
      (fun _ : ℕ => fixedBiasBinaryValueEstimate (logitProblem eta)) := by
    funext t s
    simp only [logitEstimate, fixedBiasBinaryValueEstimate, logitProblem_value]
  rw [hestimate]

/-- The actual CE drop equals the common actual value gain, including both
negative signs. -/
private theorem guardedLogitDrop_eq_fixedBiasBinaryGain
    (eta : ℝ) (M C : ℕ) (w : ℝ) (t : ℕ) :
    guardedLogitDrop eta M C w t =
      fixedBiasBinaryGain (logitProblem eta) M C (logit_feasible_zero eta M C) w t := by
  rw [fixedBiasBinaryGain_eq_sub]
  unfold guardedLogitDrop
  rw [guardedLogitPath_eq_fixedBiasBinaryPath]
  simp only [logitProblem_value]
  ring

private theorem fixedBiasLogitPath_value_le_zero
    (eta : ℝ) (M C : ℕ) (w : ℝ) (t : ℕ) :
    (logitProblem eta).value
      (fixedBiasBinaryPath (logitProblem eta) M C (logit_feasible_zero eta M C) w t) ≤ 0 := by
  simp only [logitProblem_value, neg_nonpos]
  exact logitCE_nonneg _

/-- Every actual recursive logistic-CE drop is either zero or at least one. -/
theorem guardedLogitDrop_eq_zero_or_one_le (eta : ℝ) (M C : ℕ) (w : ℝ)
    (t : ℕ) :
    guardedLogitDrop eta M C w t = 0 ∨
      1 ≤ guardedLogitDrop eta M C w t := by
  rw [guardedLogitDrop_eq_fixedBiasBinaryGain]
  exact fixedBiasBinaryGain_eq_zero_or_one_le (logitProblem eta) M C
    (logit_feasible_zero eta M C) w (fixedBiasLogit_stay_step eta) t

/-- Number of outer steps with strictly positive actual logistic-CE decrease.
This counts no estimator evaluations, primitive operations, or wall-clock
work. -/
noncomputable def guardedLogitProgressCount (eta : ℝ) (M C : ℕ) (w : ℝ)
    (T : ℕ) : ℕ := by
  classical
  exact {t ∈ Finset.range T | 0 < guardedLogitDrop eta M C w t}.card

/-- The filters are equal by a pointwise proof at every member of the range,
not by a merely asymptotic equivalence of positive drops and gains. -/
private theorem guardedLogitProgressCount_eq_fixedBiasBinaryProgressCount
    (eta : ℝ) (M C : ℕ) (w : ℝ) (T : ℕ) :
    guardedLogitProgressCount eta M C w T =
      fixedBiasBinaryProgressCount (logitProblem eta) M C
        (logit_feasible_zero eta M C) w T := by
  classical
  unfold guardedLogitProgressCount fixedBiasBinaryProgressCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro t _ht
  rw [guardedLogitDrop_eq_fixedBiasBinaryGain]

/-- The real-valued number of strictly positive CE-improvement steps is at
most the initial logistic CE, by the discrete drop floor and exact telescope. -/
theorem guardedLogitProgressCount_le_logitCE (eta : ℝ) (M C : ℕ) (w : ℝ)
    (T : ℕ) :
    (guardedLogitProgressCount eta M C w T : ℝ) ≤
      logitCE (guardedLogitPath eta M C w 0) := by
  rw [guardedLogitProgressCount_eq_fixedBiasBinaryProgressCount]
  have hbound := fixedBiasBinaryProgressCount_le (logitProblem eta) M C
    (logit_feasible_zero eta M C) w (fixedBiasLogit_stay_step eta) 0
    (fixedBiasLogitPath_value_le_zero eta M C w) T
  rw [← guardedLogitPath_eq_fixedBiasBinaryPath] at hbound
  simpa only [logitProblem_value, zero_sub, neg_neg] using hbound

/-- If the initial logistic CE is below one, the guarded raw path never moves.
This is a conservative no-small-update guarantee, not an optimality claim. -/
theorem guardedLogitPath_forall_eq_of_CE_lt_one (eta : ℝ) (M C : ℕ) (w : ℝ)
    (hsmall : logitCE (guardedLogitPath eta M C w 0) < 1) :
    ∀ t, guardedLogitPath eta M C w t = w := by
  have hgap : 0 - (logitProblem eta).value
      (fixedBiasBinaryPath (logitProblem eta) M C (logit_feasible_zero eta M C) w 0) < 1 := by
    rw [← guardedLogitPath_eq_fixedBiasBinaryPath]
    simpa only [logitProblem_value, zero_sub, neg_neg] using hsmall
  have hconst := fixedBiasBinaryPath_forall_eq_of_gap_lt_one (logitProblem eta)
    M C (logit_feasible_zero eta M C) w (fixedBiasLogit_stay_step eta) 0
    (fixedBiasLogitPath_value_le_zero eta M C w) hgap
  intro t
  rw [guardedLogitPath_eq_fixedBiasBinaryPath]
  exact hconst t

/-- Eventually every actual raw guarded-logit successor equals its current
state; the proof uses convergence of nonnegative drops to zero at radius one. -/
theorem guardedLogitPath_eventually_succ_eq (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∃ N, ∀ t ≥ N,
      guardedLogitPath eta M C w (t + 1) = guardedLogitPath eta M C w t := by
  have h := fixedBiasBinaryPath_eventually_succ_eq (logitProblem eta) M C
    (logit_feasible_zero eta M C) w (fixedBiasLogit_stay_step eta) 0
    (fixedBiasLogitPath_value_le_zero eta M C w)
  rw [← guardedLogitPath_eq_fixedBiasBinaryPath] at h
  exact h

/-- The actual raw path is eventually equal to one finite path state. -/
theorem guardedLogitPath_eventually_eq (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∃ N, ∀ t ≥ N, guardedLogitPath eta M C w t =
      guardedLogitPath eta M C w N := by
  have h := fixedBiasBinaryPath_eventually_eq (logitProblem eta) M C
    (logit_feasible_zero eta M C) w (fixedBiasLogit_stay_step eta) 0
    (fixedBiasLogitPath_value_le_zero eta M C w)
  rw [← guardedLogitPath_eq_fixedBiasBinaryPath] at h
  exact h

/-- The actual raw path converges to its finite eventual value. -/
theorem guardedLogitPath_tendsto_eventual_value (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∃ N, Tendsto (guardedLogitPath eta M C w) atTop
      (𝓝 (guardedLogitPath eta M C w N)) := by
  have h := fixedBiasBinaryPath_tendsto_eventual_value (logitProblem eta) M C
    (logit_feasible_zero eta M C) w (fixedBiasLogit_stay_step eta) 0
    (fixedBiasLogitPath_value_le_zero eta M C w)
  rw [← guardedLogitPath_eq_fixedBiasBinaryPath] at h
  exact h

end Hagi.Contracts.GuardedLogitProgress
