/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.GuardedRobustSelection
import Hagi.Unified.RobustResourceMin
set_option linter.style.header false

/-!
# Guarded minimum-resource selection with baseline protection

When a feasible action has estimated quality at least `2 * eps` above the
stay action, this wrapper uses the existing robust minimum-resource selector.
The explicit one-sided baseline bound `hbase` turns that guard into a
certificate for the actual stay-quality floor. Otherwise it returns `stay`.

Under pointwise error bounds on currently feasible actions, the chosen action
has actual quality no lower than `stay`. Its declared memory-first resource
cost is minimal among the lower-bound-certified competitors specified below,
not among all truly nondecreasing actions or architectures.
-/

namespace Hagi.Unified.GuardedRobustResourceMin

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin
open Hagi.Unified.GuardedRobustSelection Hagi.Unified.RobustResourceMin

variable {A : Type} {S : Type*} [Fintype A]

/-- An estimated upgrade and the one-sided baseline error bound certify the
actual stay-quality floor for the original feasible action `a`. -/
theorem baselineCertificate_of_margin (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay a : A) (ha : a ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (hmargin : estimate (p.step stay s) + 2 * eps ≤ estimate (p.step a s)) :
    qualityEligible (withEstimatedValue p estimate) s M C
      (p.value (p.step stay s) + eps) a := by
  refine ⟨(mem_feasible_withEstimatedValue p estimate).mpr ha, ?_⟩
  change p.value (p.step stay s) + eps ≤ estimate (p.step a s)
  linarith

/-- Use the existing robust minimum-resource action when an estimated upgrade
exists, and otherwise stay. The baseline bound supplies the eligibility
certificate; no additional action or optimization engine is introduced. -/
noncomputable def guardedMinimumResource (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps) : A := by
  classical
  have _ := h0
  exact if h_up : estimatedUpgrade p estimate eps s M C stay then
    robustMinimumResource estimate s M C (p.value (p.step stay s)) eps
      (Classical.choose h_up)
      (baselineCertificate_of_margin p estimate eps s M C stay
        (Classical.choose h_up) (Classical.choose_spec h_up).1 hbase
        (Classical.choose_spec h_up).2)
  else
    stay

/-- Without an estimated upgrade, the guarded action is exactly `stay`. -/
theorem guardedMinimumResource_of_no_upgrade (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (h : ¬ estimatedUpgrade p estimate eps s M C stay) :
    guardedMinimumResource p estimate eps s M C stay h0 hbase = stay := by
  classical
  rw [guardedMinimumResource, dite_eq_right]
  exact h

/-- The guarded action remains feasible for the original problem in both the
upgrade and fallback branches. -/
theorem guardedMinimumResource_feasible (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps) :
    guardedMinimumResource p estimate eps s M C stay h0 hbase ∈
      feasible p M C := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · unfold guardedMinimumResource
    rw [dite_eq_left]
    · exact robustMinimumResource_feasible _ _ _ _ _ _ _ _
    · exact hup
  · rw [guardedMinimumResource_of_no_upgrade
      p estimate eps s M C stay h0 hbase hup]
    exact h0

/-- With estimation errors bounded on currently feasible actions, the guarded
minimum-resource action has actual quality at least that of `stay`. -/
theorem guardedMinimumResource_quality_ge_stay (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (herr : ∀ a ∈ feasible p M C,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    p.value (p.step stay s) ≤ p.value (p.step
      (guardedMinimumResource p estimate eps s M C stay h0 hbase) s) := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · let a0 := Classical.choose hup
    let hcert := baselineCertificate_of_margin p estimate eps s M C stay a0
      (Classical.choose_spec hup).1 hbase (Classical.choose_spec hup).2
    have hquality : p.value (p.step stay s) ≤ p.value (p.step
        (robustMinimumResource estimate s M C (p.value (p.step stay s)) eps
          a0 hcert) s) := by
      have hfeasible := robustMinimumResource_feasible estimate s M C
        (p.value (p.step stay s)) eps a0 hcert
      have hq := (robustMinimumResource_eligible estimate s M C
        (p.value (p.step stay s)) eps a0 hcert).2
      have he := (abs_le.mp (herr _ hfeasible)).1
      change p.value (p.step stay s) + eps ≤ estimate (p.step
        (robustMinimumResource estimate s M C (p.value (p.step stay s)) eps
          a0 hcert) s) at hq
      linarith
    unfold guardedMinimumResource
    rw [dite_eq_left]
    exact hquality
  · rw [guardedMinimumResource_of_no_upgrade
      p estimate eps s M C stay h0 hbase hup]

/-- For any feasible competitor whose actual quality exceeds the stay quality
by at least `2 * eps`, the guarded upgrade has no greater declared resource
cost. This is the existing certified-class minimum, not global optimality. -/
theorem guardedMinimumResource_cost_le (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (h_up : estimatedUpgrade p estimate eps s M C stay)
    (b : A) (hb : b ∈ feasible p M C)
    (hgain : p.value (p.step stay s) + 2 * eps ≤ p.value (p.step b s))
    (herr : ∀ a ∈ feasible p M C,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    resourceCost p (guardedMinimumResource p estimate eps s M C stay h0 hbase) ≤
      resourceCost p b := by
  classical
  have hb_upper := (abs_le.mp (herr b hb)).2
  have hbCert : qualityEligible (withEstimatedValue p estimate) s M C
      (p.value (p.step stay s) + eps) b := by
    refine ⟨(mem_feasible_withEstimatedValue p estimate).mpr hb, ?_⟩
    change p.value (p.step stay s) + eps ≤ estimate (p.step b s)
    linarith
  unfold guardedMinimumResource
  rw [dite_eq_left]
  · exact robustMinimumResource_cost_min _ _ _ _ _ _ _ _ b hbCert
  · exact h_up

end Hagi.Unified.GuardedRobustResourceMin
