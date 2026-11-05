/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
import Hagi.Unified.QualityResourceMin
set_option linter.style.header false

/-!
# RobustResourceMin — minimum declared resources under a
bounded-estimation quality floor (cycle 74)

The exact finite policy of cycle 73 requires the successor's objective
value directly. Here only `estimate` may be available, but every actual
successor has error bounded by a uniform `eps`. Use the conservative
eligibility criterion
`qfloor + eps ≤ estimate (p.step a s)`. It implies the true-objective
floor `qfloor ≤ p.value (p.step a s)` by elementary arithmetic.

`robustMinimumResource` directly reuses `minimumResource` on the existing
`withEstimatedValue` problem. Resource costs and actual successors remain
those of `p`; there is no synthetic effect, second minimization engine or
resource exception at the upgrade boundary. The witness supplies
nonemptiness and the error bound supplies all quantitative claims.

Optimality is ONLY among lower-bound-certified candidates. A cheaper
candidate can meet the TRUE floor yet be excluded because its lower
bound cannot certify it. There is therefore no claim of minimum cost
among all truly floor-eligible actions, nor global/NAS/hardware/search
optimality. The absolute-error premise is deterministic; it is not a
statistical confidence level, calibration claim or physical measurement.
-/

namespace Hagi.Unified.RobustResourceMin

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin

variable {A : Type} {S : Type*}

/-- Choose a minimum-resource action in the estimated, conservative
floor class. Safety, caps, and actual step are definitionally unchanged. -/
noncomputable def robustMinimumResource {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) : A :=
  minimumResource (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0

/-- The chosen candidate's estimate meets the shifted floor, and it is
eligible in the original-step / original-resource policy. -/
theorem robustMinimumResource_eligible {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) :
    qualityEligible (withEstimatedValue p estimate) s M C (qfloor + eps)
      (robustMinimumResource estimate s M C qfloor eps a0 h0) :=
  (minimumResource_spec (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0).1

/-- The chosen action still has the original model safety and both exact
resource caps, independent of the quality-estimation error. -/
theorem robustMinimumResource_feasible {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) :
    robustMinimumResource estimate s M C qfloor eps a0 h0 ∈ feasible p M C := by
  have hf := minimumResource_feasible (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0
  exact (mem_feasible_withEstimatedValue p estimate).mp hf

/-- The actual successor meets the true floor. The only estimate-to-truth
connection is the explicitly supplied uniform absolute-error bound. -/
theorem robustMinimumResource_actual_quality_ge {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0)
    (herr : ∀ a, |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    qfloor ≤ p.value (p.step (robustMinimumResource estimate s M C
      qfloor eps a0 h0) s) := by
  have hq := minimumResource_next_quality_ge (withEstimatedValue p estimate)
    s M C (qfloor + eps) a0 h0
  have he := (abs_le.mp (herr (robustMinimumResource estimate s M C
    qfloor eps a0 h0))).1
  change qfloor + eps ≤ estimate (p.step (robustMinimumResource estimate s M C
    qfloor eps a0 h0) s) at hq
  linarith

/-- No lower-bound-certified competitor has smaller declared resource
cost. This deliberately does NOT quantify over every truly eligible b. -/
theorem robustMinimumResource_cost_min {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) :
    ∀ b, qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) b →
      resourceCost p (robustMinimumResource estimate s M C qfloor eps a0 h0)
        ≤ resourceCost p b := by
  intro b hb
  exact minimumResource_cost_min (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0 b hb

/-- With the exact objective as estimator and zero error, this connector
is definitionally the preceding exact minimum-resource selector. No new
algorithm or conservativeness is added in that exact special case. -/
theorem robustMinimumResource_zero_exact {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ)
    (a0 : A) (h0 : qualityEligible p s M C qfloor a0) :
    robustMinimumResource p.value s M C qfloor 0 a0 (by simpa using h0)
      = minimumResource p s M C qfloor a0 h0 := by
  simp [robustMinimumResource, withEstimatedValue, minimumResource]

end Hagi.Unified.RobustResourceMin
