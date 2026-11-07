/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.GuardedRobustSelection
set_option linter.style.header false

/-!
# Guarded robust trajectories with fresh estimates

At every time step, the recursive path applies the existing guarded robust
selector to the actual current state, using that step's estimate and error
radius. If the stay action fixes every state and every feasible successor
satisfies the supplied pointwise error bound, actual model quality is monotone.
An upper bound on actual quality then gives convergence to its conditional
supremum.

The actual successive quality gains are nonnegative, telescope exactly, and
are summable with total at most the supplied quality bound minus initial
quality. These are deterministic statements about model quality only. They do
not assert convergence of states or parameters, estimator calibration,
optimality, stochastic performance, or physical safety.
-/

namespace Hagi.Unified.GuardedRobustTrajectory

open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection
open Filter Topology

variable {A : Type} {S : Type*} [Fintype A]

/-- The guarded recursive path from `s0`, with fresh `estimate t` and `eps t`
used for the successor selected at time `t`. -/
noncomputable def guardedRobustPath (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) : ℕ → S
  | 0 => s0
  | t + 1 => guardedRobustNext p (estimate t) (eps t)
      (guardedRobustPath p estimate eps M C stay h0 s0 t) M C stay h0

@[simp] theorem guardedRobustPath_zero (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) :
    guardedRobustPath p estimate eps M C stay h0 s0 0 = s0 := rfl

@[simp] theorem guardedRobustPath_succ (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) (t : ℕ) :
    guardedRobustPath p estimate eps M C stay h0 s0 (t + 1) =
      guardedRobustNext p (estimate t) (eps t)
        (guardedRobustPath p estimate eps M C stay h0 s0 t) M C stay h0 := rfl

/-- Every recursive successor is the actual successor of an original feasible
action at the actual current path state. -/
theorem guardedRobustPath_succ_exists (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) (t : ℕ) :
    ∃ a ∈ feasible p M C,
      guardedRobustPath p estimate eps M C stay h0 s0 (t + 1) =
        p.step a (guardedRobustPath p estimate eps M C stay h0 s0 t) := by
  rw [guardedRobustPath_succ]
  exact guardedRobustNext_exists p (estimate t) (eps t)
    (guardedRobustPath p estimate eps M C stay h0 s0 t) M C stay h0

/-- Fresh feasible-successor error bounds and an identity stay action imply
that actual model quality does not decrease at any recursive step. -/
theorem guardedRobustPath_quality_step (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t) (t : ℕ) :
    p.value (guardedRobustPath p estimate eps M C stay h0 s0 t) ≤
      p.value (guardedRobustPath p estimate eps M C stay h0 s0 (t + 1)) := by
  rw [guardedRobustPath_succ]
  have hstay := guardedRobustNext_quality_ge_stay p (estimate t) (eps t)
    (guardedRobustPath p estimate eps M C stay h0 s0 t) M C stay h0
    (h_bounds t)
  rwa [hid] at hstay

/-- Actual quality along the guarded recursive path is monotone. -/
theorem guardedRobustPath_quality_monotone (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t) :
    Monotone (fun t => p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t)) :=
  monotone_nat_of_le_succ
    (guardedRobustPath_quality_step p estimate eps M C stay h0 s0 hid h_bounds)

/-- Bounded monotone actual quality converges to its conditional supremum;
the supremum is not asserted to equal the supplied bound or a global optimum. -/
theorem guardedRobustPath_quality_tendsto_ciSup (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) :
    Tendsto (fun t => p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t)) atTop
      (𝓝 (⨆ t, p.value (guardedRobustPath
        p estimate eps M C stay h0 s0 t))) := by
  apply tendsto_atTop_ciSup
    (guardedRobustPath_quality_monotone p estimate eps M C stay h0 s0 hid h_bounds)
  refine ⟨B, ?_⟩
  rintro x ⟨t, rfl⟩
  exact hB t

/-- The actual one-step gain along the guarded recursive path. -/
noncomputable def guardedRobustGain (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) (t : ℕ) : ℝ :=
  p.value (guardedRobustPath p estimate eps M C stay h0 s0 (t + 1)) -
    p.value (guardedRobustPath p estimate eps M C stay h0 s0 t)

/-- Every actual one-step quality gain is nonnegative. -/
theorem guardedRobustGain_nonneg (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t) (t : ℕ) :
    0 ≤ guardedRobustGain p estimate eps M C stay h0 s0 t :=
  sub_nonneg.mpr
    (guardedRobustPath_quality_step p estimate eps M C stay h0 s0 hid h_bounds t)

/-- Finite actual gains telescope exactly to final minus initial quality. -/
theorem guardedRobustGain_sum_range (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S) (T : ℕ) :
    ∑ t ∈ Finset.range T, guardedRobustGain p estimate eps M C stay h0 s0 t =
      p.value (guardedRobustPath p estimate eps M C stay h0 s0 T) -
        p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) := by
  simpa only [guardedRobustGain] using
    Finset.sum_range_sub
      (fun t => p.value (guardedRobustPath p estimate eps M C stay h0 s0 t)) T

/-- The supplied upper quality bound bounds every finite actual gain sum. -/
theorem guardedRobustGain_sum_range_le (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) (T : ℕ) :
    ∑ t ∈ Finset.range T, guardedRobustGain p estimate eps M C stay h0 s0 t ≤
      B - p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) := by
  calc
    ∑ t ∈ Finset.range T, guardedRobustGain p estimate eps M C stay h0 s0 t =
        p.value (guardedRobustPath p estimate eps M C stay h0 s0 T) -
          p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) :=
      guardedRobustGain_sum_range p estimate eps M C stay h0 s0 T
    _ ≤ B - p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) :=
      sub_le_sub_right (hB T) _

/-- Nonnegative actual gains with uniformly bounded partial sums are summable. -/
theorem guardedRobustGain_summable (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) :
    Summable (guardedRobustGain p estimate eps M C stay h0 s0) :=
  summable_of_sum_range_le
    (guardedRobustGain_nonneg p estimate eps M C stay h0 s0 hid h_bounds)
    (guardedRobustGain_sum_range_le p estimate eps M C stay h0 s0 B hB)

/-- Infinite-time summability forces actual one-step quality gains to zero;
this does not imply stationary states or parameters. -/
theorem guardedRobustGain_tendsto_zero (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) :
    Tendsto (guardedRobustGain p estimate eps M C stay h0 s0) atTop (𝓝 0) :=
  (guardedRobustGain_summable p estimate eps M C stay h0 s0 hid h_bounds
    B hB).tendsto_atTop_zero

/-- Total actual quality gain is at most the supplied bound minus initial
quality; no convergence of the underlying state or parameters is claimed. -/
theorem guardedRobustGain_tsum_le (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : ℕ → S → ℝ) (eps : ℕ → ℝ)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) (s0 : S)
    (hid : ∀ s, p.step stay s = s)
    (h_bounds : ∀ t a, a ∈ feasible p M C →
      |p.value (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t)) -
        estimate t (p.step a (guardedRobustPath
          p estimate eps M C stay h0 s0 t))| ≤ eps t)
    (B : ℝ)
    (hB : ∀ t, p.value (guardedRobustPath
      p estimate eps M C stay h0 s0 t) ≤ B) :
    ∑' t, guardedRobustGain p estimate eps M C stay h0 s0 t ≤
      B - p.value (guardedRobustPath p estimate eps M C stay h0 s0 0) :=
  (guardedRobustGain_summable p estimate eps M C stay h0 s0 hid h_bounds
    B hB).tsum_le_of_sum_range_le
      (guardedRobustGain_sum_range_le p estimate eps M C stay h0 s0 B hB)

end Hagi.Unified.GuardedRobustTrajectory

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
