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
