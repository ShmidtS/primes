/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.GuardedLogitTrajectory
set_option linter.style.header false

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
open Filter Topology

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

/-- Every actual recursive logistic-CE drop is either zero or at least one. -/
theorem guardedLogitDrop_eq_zero_or_one_le (eta : ℝ) (M C : ℕ) (w : ℝ)
    (t : ℕ) :
    guardedLogitDrop eta M C w t = 0 ∨
      1 ≤ guardedLogitDrop eta M C w t := by
  classical
  by_cases hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2)
      (guardedLogitPath eta M C w t) M C (0 : Fin 2)
  · right
    have hnext := guardedLogitNext_eq_update_of_any_upgrade eta M C
      (guardedLogitPath eta M C w t) hup
    have hmargin := (logitUpgrade_one_spec eta M C
      (guardedLogitPath eta M C w t) hup).2
    unfold guardedLogitDrop
    rw [guardedLogitPath_succ, hnext]
    exact hmargin
  · left
    unfold guardedLogitDrop
    rw [guardedLogitPath_succ,
      guardedLogitNext_of_no_upgrade eta M C _ hup, sub_self]

private theorem guardedLogitPath_next_eq_current_of_drop_lt_one
    (eta : ℝ) (M C : ℕ) (w : ℝ) (t : ℕ)
    (hlt : guardedLogitDrop eta M C w t < 1) :
    guardedLogitNext eta M C (guardedLogitPath eta M C w t) =
      guardedLogitPath eta M C w t := by
  classical
  by_cases hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2)
      (guardedLogitPath eta M C w t) M C (0 : Fin 2)
  · exfalso
    have hnext := guardedLogitNext_eq_update_of_any_upgrade eta M C
      (guardedLogitPath eta M C w t) hup
    have hmargin := (logitUpgrade_one_spec eta M C
      (guardedLogitPath eta M C w t) hup).2
    have hpos : 0 < guardedLogitDrop eta M C w t := by
      unfold guardedLogitDrop
      rw [guardedLogitPath_succ, hnext]
      linarith only [hmargin]
    rcases guardedLogitDrop_eq_zero_or_one_le eta M C w t with hzero | hone
    · linarith only [hpos, hzero]
    · linarith only [hlt, hone]
  · exact guardedLogitNext_of_no_upgrade eta M C _ hup

/-- Number of outer steps with strictly positive actual logistic-CE decrease.
This counts no estimator evaluations, primitive operations, or wall-clock
work. -/
noncomputable def guardedLogitProgressCount (eta : ℝ) (M C : ℕ) (w : ℝ)
    (T : ℕ) : ℕ := by
  classical
  exact {t ∈ Finset.range T | 0 < guardedLogitDrop eta M C w t}.card

/-- The real-valued number of strictly positive CE-improvement steps is at
most the initial logistic CE, by the discrete drop floor and exact telescope. -/
theorem guardedLogitProgressCount_le_logitCE (eta : ℝ) (M C : ℕ) (w : ℝ)
    (T : ℕ) :
    (guardedLogitProgressCount eta M C w T : ℝ) ≤
      logitCE (guardedLogitPath eta M C w 0) := by
  classical
  have hcard : guardedLogitProgressCount eta M C w T =
      ∑ t ∈ Finset.range T,
        if 0 < guardedLogitDrop eta M C w t then 1 else 0 := by
    unfold guardedLogitProgressCount
    exact (Finset.sum_boole
      (fun t => 0 < guardedLogitDrop eta M C w t) (Finset.range T)).symm
  rw [hcard, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc
    (∑ t ∈ Finset.range T,
        if 0 < guardedLogitDrop eta M C w t then (1 : ℝ) else 0) ≤
        ∑ t ∈ Finset.range T, guardedLogitDrop eta M C w t := by
      apply Finset.sum_le_sum
      intro t _ht
      by_cases hpos : 0 < guardedLogitDrop eta M C w t
      · rw [ite_eq_left hpos]
        rcases guardedLogitDrop_eq_zero_or_one_le eta M C w t with hzero | hone
        · linarith only [hpos, hzero]
        · exact hone
      · rw [ite_eq_right hpos]
        exact guardedLogitDrop_nonneg eta M C w t
    _ = logitCE (guardedLogitPath eta M C w 0) -
        logitCE (guardedLogitPath eta M C w T) :=
      guardedLogitDrop_sum_range eta M C w T
    _ ≤ logitCE (guardedLogitPath eta M C w 0) :=
      sub_le_self _ (logitCE_nonneg _)

/-- If the initial logistic CE is below one, the guarded raw path never moves.
This is a conservative no-small-update guarantee, not an optimality claim. -/
theorem guardedLogitPath_forall_eq_of_CE_lt_one (eta : ℝ) (M C : ℕ) (w : ℝ)
    (hsmall : logitCE (guardedLogitPath eta M C w 0) < 1) :
    ∀ t, guardedLogitPath eta M C w t = w := by
  intro t
  induction t with
  | zero => exact guardedLogitPath_zero eta M C w
  | succ t ih =>
      have hce : logitCE (guardedLogitPath eta M C w t) < 1 :=
        lt_of_le_of_lt
          (guardedLogitPath_logitCE_antitone eta M C w (Nat.zero_le t)) hsmall
      have hdrop : guardedLogitDrop eta M C w t < 1 := by
        calc
          guardedLogitDrop eta M C w t ≤
              logitCE (guardedLogitPath eta M C w t) := by
            unfold guardedLogitDrop
            exact sub_le_self _ (logitCE_nonneg _)
          _ < 1 := hce
      rw [guardedLogitPath_succ,
        guardedLogitPath_next_eq_current_of_drop_lt_one eta M C w t hdrop]
      exact ih

/-- Eventually every actual raw guarded-logit successor equals its current
state; the proof uses convergence of nonnegative drops to zero at radius one. -/
theorem guardedLogitPath_eventually_succ_eq (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∃ N, ∀ t ≥ N,
      guardedLogitPath eta M C w (t + 1) = guardedLogitPath eta M C w t := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1
    (guardedLogitDrop_tendsto_zero eta M C w)) 1 zero_lt_one
  have hdrop : ∀ t ≥ N, guardedLogitDrop eta M C w t < 1 := by
    intro t ht
    have hdist := hN t ht
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (guardedLogitDrop_nonneg eta M C w t)] at hdist
    exact hdist
  refine ⟨N, fun t ht => ?_⟩
  rw [guardedLogitPath_succ]
  exact guardedLogitPath_next_eq_current_of_drop_lt_one eta M C w t (hdrop t ht)

/-- The actual raw path is eventually equal to one finite path state. -/
theorem guardedLogitPath_eventually_eq (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∃ N, ∀ t ≥ N, guardedLogitPath eta M C w t =
      guardedLogitPath eta M C w N := by
  obtain ⟨N, hN⟩ := guardedLogitPath_eventually_succ_eq eta M C w
  refine ⟨N, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [hN n hmn]
      exact ih

/-- The actual raw path converges to its finite eventual value. -/
theorem guardedLogitPath_tendsto_eventual_value (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∃ N, Tendsto (guardedLogitPath eta M C w) atTop
      (𝓝 (guardedLogitPath eta M C w N)) := by
  obtain ⟨N, hN⟩ := guardedLogitPath_eventually_eq eta M C w
  refine ⟨N, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with t ht
  exact (hN t ht).symm

end Hagi.Contracts.GuardedLogitProgress
