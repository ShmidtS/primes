/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
import Hagi.Unified.RobustResourceMin
set_option linter.style.header false

/-!
# RobustCostSensitivity — uncertainty radius and least certified
resource cost (cycle 75)

Increasing epsilon shifts the estimator floor UP, hence shrinks the
lower-bound-certified finite class. If both radius levels have eligible
witnesses, the minimum declared resource cost cannot decrease: the
small-radius minimum can be compared with the selected large-radius
candidate, whose eligibility transfers into the smaller class.

The order remains the explicit `(memory, operations)` Prod.Lex order.
Memory itself is monotone; neither strict monotonicity nor a separate
operations-time/FLOPs monotonicity follows. Both witness hypotheses stay
visible because sufficiently high uncertainty may make the class empty.
This does not optimize over the wider truly-eligible class and does not
measure physical resources or make a statistical confidence assertion.
-/

namespace Hagi.Unified.RobustCostSensitivity

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin
open Hagi.Unified.RobustResourceMin

variable {A : Type} {S : Type*}

/-- Larger radius implies membership in the smaller-radius certified
class. The actual feasibility component is unchanged. -/
theorem robustEligible_mono_epsilon {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps1 eps2 : ℝ)
    (h_eps : eps1 ≤ eps2) {a : A}
    (ha : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps2) a) :
    qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps1) a := by
  exact ⟨ha.1, by linarith [ha.2]⟩

/-- Minimum declared resource cost is nondecreasing as the robustness
radius grows. Both eligible witnesses are required; this is not an
existence assertion for empty certified classes. -/
theorem robustMinimumResource_cost_mono {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps1 eps2 : ℝ) (a1 a2 : A)
    (h_eps : eps1 ≤ eps2)
    (h_small : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps1) a1)
    (h_large : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps2) a2) :
    resourceCost p (robustMinimumResource estimate s M C qfloor eps1 a1 h_small)
      ≤ resourceCost p
          (robustMinimumResource estimate s M C qfloor eps2 a2 h_large) := by
  apply robustMinimumResource_cost_min estimate s M C qfloor eps1 a1 h_small
    (robustMinimumResource estimate s M C qfloor eps2 a2 h_large)
  exact robustEligible_mono_epsilon estimate s M C qfloor eps1 eps2 h_eps
    (robustMinimumResource_eligible estimate s M C qfloor eps2 a2 h_large)

/-- The first memory coordinate is nondecreasing under the same witness
premises. No separate operations monotone claim is made. -/
theorem robustMinimumResource_memory_mono {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps1 eps2 : ℝ) (a1 a2 : A)
    (h_eps : eps1 ≤ eps2)
    (h_small : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps1) a1)
    (h_large : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps2) a2) :
    p.memory (robustMinimumResource estimate s M C qfloor eps1 a1 h_small)
      ≤ p.memory
          (robustMinimumResource estimate s M C qfloor eps2 a2 h_large) := by
  have hcost := robustMinimumResource_cost_mono estimate s M C qfloor
    eps1 eps2 a1 a2 h_eps h_small h_large
  exact Prod.Lex.monotone_fst _ _ hcost

end Hagi.Unified.RobustCostSensitivity
