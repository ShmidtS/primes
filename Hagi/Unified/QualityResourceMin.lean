/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
import Hagi.Unified.ParetoExecution
set_option linter.style.header false

/-!
# QualityResourceMin — exact minimum model resources under
an objective floor (cycle 73)

This complements the quality-first `ParetoExecution.selection`:
for a finite candidate family, choose a minimum-cost action whose
ACTUAL successor has `qfloor ≤ p.value (p.step a s)`. Feasibility is
the existing conjunction of model safety and both resource caps.

* `qualityEligible` is exactly the existing `feasible` condition plus
  the objective floor; it is not an externally declared desired effect.
* `resourceCost` is `(memory, operations)` in `ℕ ×ₗ ℕ`, explicitly
  memory-first. No arbitrary scalarization mixes different units.
* `exists_minimum_resource` reuses Mathlib's
  `Finset.exists_min_image`; `minimumResource` is the corresponding
  noncomputable `Classical.choose` witness.
* If the eligible set is empty, no witness can be supplied. The API
  does not fabricate a fallback, a quality improvement, or a feasible
  over-budget action.

This is an exact minimum only within the explicitly supplied finite
family and its model cost/objective. It does not certify a global
architecture optimum, minimal search complexity/FLOPs, physical bytes,
hardware latency, task accuracy, or an executable optimizer over ℝ.
-/

namespace Hagi.Unified.QualityResourceMin

open Prod.Lex Hagi.Unified.ParetoExecution

variable {A : Type} {S : Type*}

/-- The explicit memory-first resource cost in declared model units.
Operations decide only memory ties; no mixed scalar objective. -/
def resourceCost (p : ControllerProblem A S) (a : A) : ℕ ×ₗ ℕ :=
  toLex (p.memory a, p.operations a)

/-- An action is eligible if it belongs to the original finite feasible
family AND its actual successor meets the objective floor. -/
def qualityEligible (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a : A) : Prop :=
  a ∈ feasible p M C ∧ qfloor ≤ p.value (p.step a s)

/-- A nonempty eligible finite family has a minimum resource-cost action,
using Mathlib's existing `Finset.exists_min_image`. -/
theorem exists_minimum_resource (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    ∃ a, qualityEligible p s M C qfloor a
      ∧ ∀ b, qualityEligible p s M C qfloor b →
          resourceCost p a ≤ resourceCost p b := by
  classical
  let U := Finset.univ.filter (qualityEligible p s M C qfloor)
  have hne : U.Nonempty :=
    ⟨a0, Finset.mem_filter.mpr ⟨Finset.mem_univ a0, h0⟩⟩
  obtain ⟨a, ha, hmin⟩ :=
    Finset.exists_min_image U (resourceCost p) hne
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  exact hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)

/-- Exact finite-family selection at minimum declared resource cost.
The eligible witness excludes the empty-family case; the choice is
mathematical selection, not a certified executable search algorithm. -/
noncomputable def minimumResource (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) : A :=
  Classical.choose (exists_minimum_resource p s M C qfloor a0 h0)

/-- Full specification: the selected action is eligible, and no other
eligible action has smaller resource cost. Cost order is the explicitly
supplied memory-first lexicographic order, not a universal preference. -/
theorem minimumResource_spec (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    qualityEligible p s M C qfloor (minimumResource p s M C qfloor a0 h0)
      ∧ ∀ b, qualityEligible p s M C qfloor b →
          resourceCost p (minimumResource p s M C qfloor a0 h0)
            ≤ resourceCost p b :=
  Classical.choose_spec (exists_minimum_resource p s M C qfloor a0 h0)

/-- The selected action retains the original model safety and both
exact resource caps; no objective-floor exception is introduced. -/
theorem minimumResource_feasible (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    minimumResource p s M C qfloor a0 h0 ∈ feasible p M C :=
  (minimumResource_spec p s M C qfloor a0 h0).1.1

/-- Quality is checked at the ACTUAL successor of the selected action,
not at the witness or at synthesized metadata. -/
theorem minimumResource_next_quality_ge (p : ControllerProblem A S)
    [Fintype A] [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ)
    (a0 : A) (h0 : qualityEligible p s M C qfloor a0) :
    qfloor ≤ p.value (p.step (minimumResource p s M C qfloor a0 h0) s) :=
  (minimumResource_spec p s M C qfloor a0 h0).1.2

/-- No eligible action has smaller declared resource cost than the
chosen action. This is class-relative, and the cost is not physical
measurement or a claim of minimum search time. -/
theorem minimumResource_cost_min (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    ∀ b, qualityEligible p s M C qfloor b →
      resourceCost p (minimumResource p s M C qfloor a0 h0)
        ≤ resourceCost p b :=
  (minimumResource_spec p s M C qfloor a0 h0).2

/-- The selected action retains the original model-level safety predicate.
This does not identify that predicate with physical safety. -/
theorem minimumResource_safe (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    p.safe (minimumResource p s M C qfloor a0 h0) :=
  (mem_feasible.mp (minimumResource_feasible p s M C qfloor a0 h0)).1

end Hagi.Unified.QualityResourceMin
