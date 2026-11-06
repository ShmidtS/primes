/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.ParetoExecution
set_option linter.style.header false

/-!
# Guarded robust selection with baseline non-regression

This additive controller uses the existing robust finite selector only when
some feasible action improves the stay successor's estimated quality by at
least `2 * eps`. Otherwise, it executes the stay successor directly.

Under a pointwise absolute-error bound on all currently feasible successors,
the selected successor's true model quality is no lower than that of the stay
successor. This is a deterministic conditional statement, not a probability,
empirical-performance, or physical-safety claim.
-/

namespace Hagi.Unified.GuardedRobustSelection

open Hagi.Unified.ParetoExecution

variable {A : Type} {S : Type*} [Fintype A]

/-- Some original feasible action has estimated successor quality at least
`2 * eps` above the stay successor's estimated quality. -/
def estimatedUpgrade (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : S → ℝ) (eps : ℝ) (s : S) (M C : ℕ) (stay : A) : Prop :=
  ∃ a ∈ feasible p M C,
    estimate (p.step stay s) + 2 * eps ≤ estimate (p.step a s)

/-- Use the existing robust successor exactly when `estimatedUpgrade` holds;
otherwise return the actual stay successor. -/
noncomputable def guardedRobustNext (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) : S := by
  classical
  exact if estimatedUpgrade p estimate eps s M C stay then
    robustNext p estimate s M C stay h0
  else
    p.step stay s

/-- Without an estimated upgrade, the wrapper executes the stay successor. -/
theorem guardedRobustNext_of_no_upgrade (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (h : ¬ estimatedUpgrade p estimate eps s M C stay) :
    guardedRobustNext p estimate eps s M C stay h0 = p.step stay s := by
  unfold guardedRobustNext
  exact if_neg h

/-- The guarded successor is the actual successor of an original feasible
action, whether the robust branch or the stay branch is taken. -/
theorem guardedRobustNext_exists (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C) :
    ∃ a ∈ feasible p M C,
      guardedRobustNext p estimate eps s M C stay h0 = p.step a s := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · obtain ⟨a, ha, hnext⟩ := robustNext_eq p estimate s M C stay h0
    refine ⟨a, ha, ?_⟩
    unfold guardedRobustNext
    rw [if_pos hup]
    exact hnext
  · exact ⟨stay, h0, guardedRobustNext_of_no_upgrade
      p estimate eps s M C stay h0 hup⟩

/-- Bounded pointwise estimation error and the `2 * eps` upgrade guard imply
true-quality non-regression relative to the actual stay successor. -/
theorem guardedRobustNext_quality_ge_stay (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (herr : ∀ a ∈ feasible p M C,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    p.value (p.step stay s) ≤
      p.value (guardedRobustNext p estimate eps s M C stay h0) := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · have hguard : guardedRobustNext p estimate eps s M C stay h0 =
        robustNext p estimate s M C stay h0 := by
      unfold guardedRobustNext
      rw [if_pos hup]
    obtain ⟨a, ha, hmargin⟩ := hup
    obtain ⟨b, hb, hnext⟩ :=
      guardedRobustNext_exists p estimate eps s M C stay h0
    have hm0 := (mem_feasible_withEstimatedValue p estimate).mpr h0
    have hchoice := selection_quality_optimal (withEstimatedValue p estimate)
      s M C stay hm0 a ((mem_feasible_withEstimatedValue p estimate).mpr ha)
    have hrob : robustNext p estimate s M C stay h0 = p.step b s :=
      hguard.symm.trans hnext
    change estimate (p.step a s) ≤
      estimate (robustNext p estimate s M C stay h0) at hchoice
    rw [hrob] at hchoice
    have hbase := (abs_le.mp (herr stay h0)).2
    have hb_error := (abs_le.mp (herr b hb)).1
    rw [hnext]
    linarith
  · rw [guardedRobustNext_of_no_upgrade p estimate eps s M C stay h0 hup]

end Hagi.Unified.GuardedRobustSelection
