/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
import Hagi.Unified.RobustCostSensitivity
set_option linter.style.header false

/-!
# RobustRadius — exact boundary for estimator-floor admissibility
(cycle 76)

For a given objective floor, the lower-bound-certified class is nonempty
precisely when `eps ≤ maxEstimate − qfloor`, where `maxEstimate` is the
existing finite selector's estimated value on its ACTUAL successor.
The boundary is included; a larger radius has no eligible action.

This reuses `ParetoExecution.selection` over `withEstimatedValue`.
`h_stay` supplies only the nonempty original feasible set, not arbitrary
robust-floor feasibility. Resource caps remain original and no minimum
resource or search-time engine is duplicated.

The scalar margin is not a conic/MIP robust-feasibility-radius algorithm,
an architecture optimum, physical resource certification or statistical
confidence. Actual objective-floor quality still requires the separate
absolute-error hypothesis from the previous connector.
-/

namespace Hagi.Unified.RobustRadius

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin

variable {A : Type} {S : Type*}

/-- Maximum estimated value on an actual successor, computed by the
existing finite selector. Only its value estimate matters in the margin. -/
noncomputable def estimatedMaxValue {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (stay : A) (h_stay : stay ∈ feasible p M C) : ℝ :=
  (withEstimatedValue p estimate).value
    (selectedNext (withEstimatedValue p estimate) s M C stay
      ((mem_feasible_withEstimatedValue p estimate).mpr h_stay))

/-- The selected maximum dominates the estimated value on each actual
successor of every original-feasible candidate. -/
theorem estimatedMaxValue_upper {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (stay : A) (h_stay : stay ∈ feasible p M C)
    {a : A} (ha : a ∈ feasible p M C) :
    estimate (p.step a s) ≤ estimatedMaxValue estimate s M C stay h_stay := by
  have h := selection_quality_optimal (withEstimatedValue p estimate)
    s M C stay ((mem_feasible_withEstimatedValue p estimate).mpr h_stay)
    a ((mem_feasible_withEstimatedValue p estimate).mpr ha)
  exact h

/-- Exact admissibility criterion for existence of a conservative
floor-certified action. Boundary point included. -/
theorem robust_eligible_iff_radius_le_margin {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (stay : A)
    (h_stay : stay ∈ feasible p M C) :
    (∃ a, qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a) ↔
      eps ≤ estimatedMaxValue estimate s M C stay h_stay - qfloor := by
  constructor
  · rintro ⟨a, hfe, hq⟩
    have hb := estimatedMaxValue_upper estimate s M C stay h_stay hfe
    exact sub_nonneg.mp (by linarith : 0 ≤
      estimatedMaxValue estimate s M C stay h_stay - qfloor - eps)
  · intro he
    let hse : stay ∈ feasible (withEstimatedValue p estimate) M C :=
      (mem_feasible_withEstimatedValue p estimate).mpr h_stay
    refine ⟨selection (withEstimatedValue p estimate) s M C stay hse,
      selection_admissible (withEstimatedValue p estimate) s M C stay hse, ?_⟩
    change qfloor + eps ≤ estimate (p.step
      (selection (withEstimatedValue p estimate) s M C stay hse) s)
    dsimp [estimatedMaxValue, selectedNext] at he
    linarith

/-- After the maximum estimated margin, no candidate can be eligible. -/
theorem no_robust_eligible_above_margin {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (stay : A)
    (h_stay : stay ∈ feasible p M C)
    (h_eps : estimatedMaxValue estimate s M C stay h_stay - qfloor < eps) :
    ∀ a, ¬ qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a := by
  intro a ha
  have hb := estimatedMaxValue_upper estimate s M C stay h_stay ha.1
  have hq := ha.2
  linarith

end Hagi.Unified.RobustRadius
