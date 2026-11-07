/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.GuardedRobustTrajectory
set_option linter.style.header false
set_option relaxedAutoImplicit false

/-!
# Discrete progress for fixed-bias two-action guarded paths

For a two-action controller whose stay action is the identity, the estimate
`value - 1 / 2` and guard radius `1 / 2` give a deterministic discrete
alternative: every actual one-step value gain is zero or at least one. The
number of positive gains is therefore bounded by any supplied upper value
bound minus the initial value. A gap below one freezes the path; in general,
gains tending to zero imply eventual constancy and convergence to the eventual
state.

These are finite-model quality statements only. They do not assert a global
optimum, estimator calibration, physical resource bounds, or convergence for
an arbitrary finite action family.
-/

namespace Hagi.Unified.FixedBiasBinaryProgress

open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection
open Hagi.Unified.GuardedRobustTrajectory
open Filter Topology

variable {S : Type*}

/-- The true controller value with the constant pessimistic bias `-1 / 2`. -/
noncomputable def fixedBiasBinaryValueEstimate (p : ControllerProblem (Fin 2) S)
    (s : S) : ℝ :=
  p.value s - 1 / 2

/-- The absolute pointwise error of the fixed-bias estimate is exactly `1/2`. -/
theorem fixedBiasBinaryValueEstimate_error (p : ControllerProblem (Fin 2) S)
    (s : S) :
    |p.value s - fixedBiasBinaryValueEstimate p s| = 1 / 2 := by
  unfold fixedBiasBinaryValueEstimate
  norm_num

/-- The parent guarded robust path with the same fixed-bias estimate and
constant radius at every step. No new path recursion is introduced. -/
noncomputable def fixedBiasBinaryPath (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) : ℕ → S :=
  guardedRobustPath p (fun _ => fixedBiasBinaryValueEstimate p)
    (fun _ => 1 / 2) M C (0 : Fin 2) h0 s0

@[simp] theorem fixedBiasBinaryPath_zero (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) :
    fixedBiasBinaryPath p M C h0 s0 0 = s0 := by
  simp only [fixedBiasBinaryPath, guardedRobustPath_zero]

@[simp] theorem fixedBiasBinaryPath_succ (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (t : ℕ) :
    fixedBiasBinaryPath p M C h0 s0 (t + 1) =
      guardedRobustNext p (fixedBiasBinaryValueEstimate p) (1 / 2)
        (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2) h0 := by
  simp only [fixedBiasBinaryPath, guardedRobustPath_succ]

/-- The parent actual value gain for the fixed-bias path. -/
noncomputable def fixedBiasBinaryGain (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (t : ℕ) : ℝ :=
  guardedRobustGain p (fun _ => fixedBiasBinaryValueEstimate p)
    (fun _ => 1 / 2) M C (0 : Fin 2) h0 s0 t

/-- The fixed-bias gain is the actual successor value minus current value. -/
theorem fixedBiasBinaryGain_eq_sub (p : ControllerProblem (Fin 2) S)
    [DecidablePred p.safe] (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C)
    (s0 : S) (t : ℕ) :
    fixedBiasBinaryGain p M C h0 s0 t =
      p.value (fixedBiasBinaryPath p M C h0 s0 (t + 1)) -
        p.value (fixedBiasBinaryPath p M C h0 s0 t) := rfl

private theorem fixedBiasBinaryPath_error_bound
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (t : ℕ) (a : Fin 2) (_ha : a ∈ feasible p M C) :
    |p.value (p.step a (fixedBiasBinaryPath p M C h0 s0 t)) -
      fixedBiasBinaryValueEstimate p
        (p.step a (fixedBiasBinaryPath p M C h0 s0 t))| ≤ 1 / 2 :=
  le_of_eq (fixedBiasBinaryValueEstimate_error p _)

private theorem fixedBiasBinaryPath_quality_monotone
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) :
    Monotone (fun t => p.value (fixedBiasBinaryPath p M C h0 s0 t)) := by
  exact guardedRobustPath_quality_monotone p
    (fun _ => fixedBiasBinaryValueEstimate p) (fun _ => 1 / 2)
    M C (0 : Fin 2) h0 s0 hid
    (fixedBiasBinaryPath_error_bound p M C h0 s0)

private theorem fixedBiasBinaryGain_nonneg
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ) :
    0 ≤ fixedBiasBinaryGain p M C h0 s0 t := by
  exact guardedRobustGain_nonneg p (fun _ => fixedBiasBinaryValueEstimate p)
    (fun _ => 1 / 2) M C (0 : Fin 2) h0 s0 hid
    (fixedBiasBinaryPath_error_bound p M C h0 s0) t

/-- In two actions, an active fixed-bias upgrade is precisely an action-one
witness with actual value gain at least one over the identity stay state. -/
private theorem fixedBiasBinaryUpgrade_spec
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (s : S) (hid : ∀ s, p.step (0 : Fin 2) s = s)
    (hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      s M C (0 : Fin 2)) :
    (1 : Fin 2) ∈ feasible p M C ∧
      1 ≤ p.value (p.step (1 : Fin 2) s) - p.value s := by
  obtain ⟨a, ha, hmargin⟩ := hup
  have ha_one : a = 1 := by
    have hval : a.val = 0 ∨ a.val = 1 := by omega
    rcases hval with hzero | hone
    · exfalso
      have ha_zero : a = 0 := Fin.ext hzero
      subst a
      rw [hid] at hmargin
      unfold fixedBiasBinaryValueEstimate at hmargin
      linarith
    · exact Fin.ext hone
  subst a
  refine ⟨ha, ?_⟩
  rw [hid] at hmargin
  unfold fixedBiasBinaryValueEstimate at hmargin
  linarith

private theorem fixedBiasBinaryNext_eq_step_one_of_upgrade
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s)
    (hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      s M C (0 : Fin 2)) :
    guardedRobustNext p (fixedBiasBinaryValueEstimate p) (1 / 2)
      s M C (0 : Fin 2) h0 = p.step (1 : Fin 2) s := by
  have hspec := fixedBiasBinaryUpgrade_spec p M C s hid hup
  have hm0 : (0 : Fin 2) ∈ feasible
      (withEstimatedValue p (fixedBiasBinaryValueEstimate p)) M C :=
    (mem_feasible_withEstimatedValue p _).mpr h0
  have hm1 : (1 : Fin 2) ∈ feasible
      (withEstimatedValue p (fixedBiasBinaryValueEstimate p)) M C :=
    (mem_feasible_withEstimatedValue p _).mpr hspec.1
  have hvalue : fixedBiasBinaryValueEstimate p (p.step (0 : Fin 2) s) <
      fixedBiasBinaryValueEstimate p (p.step (1 : Fin 2) s) := by
    rw [hid]
    unfold fixedBiasBinaryValueEstimate
    linarith only [hspec.2]
  have hselection := selection_eq_one_of_value_lt
    (withEstimatedValue p (fixedBiasBinaryValueEstimate p)) s M C hm0 hm1 hvalue
  unfold guardedRobustNext
  rw [ite_eq_left hup]
  change p.step (selection
    (withEstimatedValue p (fixedBiasBinaryValueEstimate p))
    s M C (0 : Fin 2) hm0) s = p.step (1 : Fin 2) s
  rw [hselection]

private theorem fixedBiasBinaryPath_succ_eq_step_one_of_upgrade
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ)
    (hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2)) :
    fixedBiasBinaryPath p M C h0 s0 (t + 1) =
      p.step (1 : Fin 2) (fixedBiasBinaryPath p M C h0 s0 t) := by
  rw [fixedBiasBinaryPath_succ]
  exact fixedBiasBinaryNext_eq_step_one_of_upgrade p M C h0 _ hid hup

private theorem fixedBiasBinaryPath_succ_eq_current_of_no_upgrade
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ)
    (hup : ¬ estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2)) :
    fixedBiasBinaryPath p M C h0 s0 (t + 1) =
      fixedBiasBinaryPath p M C h0 s0 t := by
  rw [fixedBiasBinaryPath_succ,
    guardedRobustNext_of_no_upgrade p (fixedBiasBinaryValueEstimate p)
      (1 / 2) _ M C (0 : Fin 2) h0 hup, hid]

/-- Every actual fixed-bias path gain is either zero or at least one. -/
theorem fixedBiasBinaryGain_eq_zero_or_one_le
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ) :
    fixedBiasBinaryGain p M C h0 s0 t = 0 ∨
      1 ≤ fixedBiasBinaryGain p M C h0 s0 t := by
  classical
  by_cases hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2)
  · right
    rw [fixedBiasBinaryGain_eq_sub,
      fixedBiasBinaryPath_succ_eq_step_one_of_upgrade p M C h0 s0 hid t hup]
    exact (fixedBiasBinaryUpgrade_spec p M C _ hid hup).2
  · left
    rw [fixedBiasBinaryGain_eq_sub,
      fixedBiasBinaryPath_succ_eq_current_of_no_upgrade p M C h0 s0 hid t hup,
      sub_self]

private theorem fixedBiasBinaryNext_eq_current_of_gain_lt_one
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (t : ℕ)
    (hlt : fixedBiasBinaryGain p M C h0 s0 t < 1) :
    guardedRobustNext p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2) h0 =
        fixedBiasBinaryPath p M C h0 s0 t := by
  classical
  by_cases hup : estimatedUpgrade p (fixedBiasBinaryValueEstimate p) (1 / 2)
      (fixedBiasBinaryPath p M C h0 s0 t) M C (0 : Fin 2)
  · exfalso
    have hone : 1 ≤ fixedBiasBinaryGain p M C h0 s0 t := by
      rw [fixedBiasBinaryGain_eq_sub,
        fixedBiasBinaryPath_succ_eq_step_one_of_upgrade p M C h0 s0 hid t hup]
      exact (fixedBiasBinaryUpgrade_spec p M C _ hid hup).2
    linarith only [hlt, hone]
  · rw [guardedRobustNext_of_no_upgrade p (fixedBiasBinaryValueEstimate p)
      (1 / 2) _ M C (0 : Fin 2) h0 hup, hid]

/-- Number of outer steps with strictly positive actual value gain. This is
not a count of estimator evaluations, operations, or wall-clock work. -/
noncomputable def fixedBiasBinaryProgressCount
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S) (T : ℕ) : ℕ := by
  classical
  exact {t ∈ Finset.range T | 0 < fixedBiasBinaryGain p M C h0 s0 t}.card

/-- The real-valued positive-gain count is at most the supplied upper value
bound minus the actual initial path value. -/
theorem fixedBiasBinaryProgressCount_le
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B) (T : ℕ) :
    (fixedBiasBinaryProgressCount p M C h0 s0 T : ℝ) ≤
      B - p.value (fixedBiasBinaryPath p M C h0 s0 0) := by
  classical
  have hcard : fixedBiasBinaryProgressCount p M C h0 s0 T =
      ∑ t ∈ Finset.range T,
        if 0 < fixedBiasBinaryGain p M C h0 s0 t then 1 else 0 := by
    unfold fixedBiasBinaryProgressCount
    exact (Finset.sum_boole
      (fun t => 0 < fixedBiasBinaryGain p M C h0 s0 t) (Finset.range T)).symm
  rw [hcard, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc
    (∑ t ∈ Finset.range T,
        if 0 < fixedBiasBinaryGain p M C h0 s0 t then (1 : ℝ) else 0) ≤
        ∑ t ∈ Finset.range T, fixedBiasBinaryGain p M C h0 s0 t := by
      apply Finset.sum_le_sum
      intro t _ht
      by_cases hpos : 0 < fixedBiasBinaryGain p M C h0 s0 t
      · rw [ite_eq_left hpos]
        rcases fixedBiasBinaryGain_eq_zero_or_one_le p M C h0 s0 hid t with
          hzero | hone
        · linarith only [hpos, hzero]
        · exact hone
      · rw [ite_eq_right hpos]
        exact fixedBiasBinaryGain_nonneg p M C h0 s0 hid t
    _ = p.value (fixedBiasBinaryPath p M C h0 s0 T) -
        p.value (fixedBiasBinaryPath p M C h0 s0 0) := by
      exact guardedRobustGain_sum_range p
        (fun _ => fixedBiasBinaryValueEstimate p) (fun _ => 1 / 2)
        M C (0 : Fin 2) h0 s0 T
    _ ≤ B - p.value (fixedBiasBinaryPath p M C h0 s0 0) :=
      sub_le_sub_right (hB T) _

/-- If the supplied value gap is below one, every step stays at the initial
state. This uses monotonicity and the discrete gain floor, not resource caps. -/
theorem fixedBiasBinaryPath_forall_eq_of_gap_lt_one
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B)
    (hsmall : B - p.value (fixedBiasBinaryPath p M C h0 s0 0) < 1) :
    ∀ t, fixedBiasBinaryPath p M C h0 s0 t = s0 := by
  intro t
  induction t with
  | zero => exact fixedBiasBinaryPath_zero p M C h0 s0
  | succ t ih =>
      have hinitial : p.value (fixedBiasBinaryPath p M C h0 s0 0) ≤
          p.value (fixedBiasBinaryPath p M C h0 s0 t) :=
        fixedBiasBinaryPath_quality_monotone p M C h0 s0 hid (Nat.zero_le t)
      have hgain : fixedBiasBinaryGain p M C h0 s0 t < 1 := by
        rw [fixedBiasBinaryGain_eq_sub]
        have hnext := hB (t + 1)
        linarith only [hinitial, hnext, hsmall]
      rw [fixedBiasBinaryPath_succ,
        fixedBiasBinaryNext_eq_current_of_gain_lt_one p M C h0 s0 hid t hgain]
      exact ih

/-- Actual gains tending to zero force every sufficiently late successor to
stay at its current state. -/
theorem fixedBiasBinaryPath_eventually_succ_eq
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B) :
    ∃ N, ∀ t ≥ N,
      fixedBiasBinaryPath p M C h0 s0 (t + 1) =
        fixedBiasBinaryPath p M C h0 s0 t := by
  have htendsto : Tendsto (fixedBiasBinaryGain p M C h0 s0) atTop (𝓝 0) := by
    exact guardedRobustGain_tendsto_zero p
      (fun _ => fixedBiasBinaryValueEstimate p) (fun _ => 1 / 2)
      M C (0 : Fin 2) h0 s0 hid (fixedBiasBinaryPath_error_bound p M C h0 s0)
      B hB
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htendsto) 1 zero_lt_one
  have hgain : ∀ t ≥ N, fixedBiasBinaryGain p M C h0 s0 t < 1 := by
    intro t ht
    have hdist := hN t ht
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (fixedBiasBinaryGain_nonneg p M C h0 s0 hid t)] at hdist
    exact hdist
  refine ⟨N, fun t ht => ?_⟩
  rw [fixedBiasBinaryPath_succ]
  exact fixedBiasBinaryNext_eq_current_of_gain_lt_one p M C h0 s0 hid t
    (hgain t ht)

/-- A fixed-bias guarded path is eventually equal to one of its own states. -/
theorem fixedBiasBinaryPath_eventually_eq
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B) :
    ∃ N, ∀ t ≥ N, fixedBiasBinaryPath p M C h0 s0 t =
      fixedBiasBinaryPath p M C h0 s0 N := by
  obtain ⟨N, hN⟩ := fixedBiasBinaryPath_eventually_succ_eq p M C h0 s0 hid B hB
  refine ⟨N, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [hN n hmn]
      exact ih

/-- With any topology on the state space, the path converges to its eventual
state. No identification with a global optimum is made. -/
theorem fixedBiasBinaryPath_tendsto_eventual_value [TopologicalSpace S]
    (p : ControllerProblem (Fin 2) S) [DecidablePred p.safe]
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step (0 : Fin 2) s = s) (B : ℝ)
    (hB : ∀ t, p.value (fixedBiasBinaryPath p M C h0 s0 t) ≤ B) :
    ∃ N, Tendsto (fixedBiasBinaryPath p M C h0 s0) atTop
      (𝓝 (fixedBiasBinaryPath p M C h0 s0 N)) := by
  obtain ⟨N, hN⟩ := fixedBiasBinaryPath_eventually_eq p M C h0 s0 hid B hB
  refine ⟨N, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with t ht
  exact (hN t ht).symm

end Hagi.Unified.FixedBiasBinaryProgress
