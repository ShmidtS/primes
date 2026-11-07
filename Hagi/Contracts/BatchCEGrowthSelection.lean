/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.BatchCEGrowth
import Hagi.Unified.QualityResourceMin

/-!
Exact finite selection on actual bounded-growth successors.
Resource fields close over the current state and count only its conditional
width-dependent cells and guarded-training operation units. Candidate production,
selector evaluation and physical memory/runtime are outside this accounting.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Contracts.BatchCEGrowthSelection

open Hagi.Contracts.BatchCEGrowth Hagi.Contracts.BudgetedBatchCE
open Hagi.Model.CEExpansion Hagi.State
open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin
open Prod.Lex

variable {A : Type} {V : Type} [Fintype V] {B a r c k capacity : ℕ}

section Candidates

variable
    (Zs : A → (_ : BoundedBatchState V B a r c k capacity) → Fin B → V → ℝ)
    (Ds : A → ∀ S : BoundedBatchState V B a r c k capacity,
      EuclideanSpace ℝ (Fin (S.width + 1)))
    (costs memoryCaps operationCaps : A → ℕ)
    (risks : A → ℝ) (writes : A → Option (Σ _ : ℕ, Fin c → ℝ))

/-- An actual guarded successor for one candidate at the current state. -/
noncomputable def growthCandidateStep (S : BoundedBatchState V B a r c k capacity) (idx : A) :
    BoundedBatchState V B a r c k capacity :=
  boundedGrowStep S (Zs idx S) (Ds idx S) (costs idx)
    (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx)

/-- New logical model/moment and retained-feature cells if this candidate is admitted. -/
noncomputable def growthCandidateMemoryIncrement
    (S : BoundedBatchState V B a r c k capacity) (idx : A) : ℕ := by
  classical
  exact if GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx) then
    growthMemoryIncrement B V
  else 0

/-- Declared guarded-trainer operations if admitted, and zero if rejected. -/
noncomputable def growthCandidateOperationIncrement
    (S : BoundedBatchState V B a r c k capacity) (idx : A) : ℕ := by
  classical
  exact if GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx) then
    growthOperations B V (costs idx)
  else 0

/-- A finite controller problem specialized at the reference state `S`.
Resources are conditional on that same state; the candidate steps use each
input state they are given. -/
noncomputable def growthProblemAt (S : BoundedBatchState V B a r c k capacity) :
    ControllerProblem A (BoundedBatchState V B a r c k capacity) := by
  classical
  exact
    { value := fun T => -growthObjective T
      step := fun idx T => growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes T idx
      memory := fun idx =>
        growthCandidateMemoryIncrement Zs Ds costs memoryCaps operationCaps S idx
      operations := fun idx =>
        growthCandidateOperationIncrement Zs Ds costs memoryCaps operationCaps S idx
      safe := fun idx => ∀ T,
        growthObjective
          (growthCandidateStep Zs Ds costs memoryCaps operationCaps
            risks writes T idx) ≤ growthObjective T }

/-- Cell increments are exactly the change in model/moment plus retained-feature cells. -/
theorem growthCandidate_cell_increment (S : BoundedBatchState V B a r c k capacity) (idx : A) :
    growthCandidateMemoryIncrement Zs Ds costs memoryCaps operationCaps S idx +
        (expandedStateCoefficients * S.width + featurePayloadCells B V S.width) =
      expandedStateCoefficients *
          (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx).width +
        featurePayloadCells B V
          (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx).width := by
  classical
  by_cases hlegal : GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx)
  · have hwidth :
        (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx).width =
          S.width + 1 :=
      (boundedGrowStep_legal_iff_width_succ S (Zs idx S) (Ds idx S) (costs idx)
        (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx)).mp hlegal
    simp only [growthCandidateMemoryIncrement, hlegal, ite_true, hwidth,
      featurePayloadCells, growthMemoryIncrement]
    ring
  · have hnext : growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx = S :=
      boundedGrowStep_of_not_legal S (Zs idx S) (Ds idx S) (costs idx)
        (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal
    simp only [growthCandidateMemoryIncrement, hlegal, ite_false, hnext, zero_add]

/-- The conditional operation increment is exactly added to accumulated declared flops. -/
theorem growthCandidate_flops (S : BoundedBatchState V B a r c k capacity) (idx : A) :
    (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx).state.res.flops =
      S.state.res.flops +
        (growthCandidateOperationIncrement Zs Ds costs memoryCaps operationCaps S idx : ℝ) := by
  classical
  unfold growthCandidateStep
  by_cases hlegal : GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx)
  · rw [boundedGrowStep_flops_of_legal S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal]
    simp only [growthCandidateOperationIncrement, hlegal, ite_true]
  · rw [boundedGrowStep_of_not_legal S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal]
    simp [growthCandidateOperationIncrement, hlegal]

/-- The conditional operation increment is exactly subtracted from real remaining budget. -/
theorem growthCandidate_budget (S : BoundedBatchState V B a r c k capacity) (idx : A) :
    (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx).state.res.budget =
      S.state.res.budget -
        (growthCandidateOperationIncrement Zs Ds costs memoryCaps operationCaps S idx : ℝ) := by
  classical
  unfold growthCandidateStep
  by_cases hlegal : GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx)
  · rw [boundedGrowStep_budget_of_legal S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal]
    simp only [growthCandidateOperationIncrement, hlegal, ite_true]
  · rw [boundedGrowStep_of_not_legal S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal]
    simp [growthCandidateOperationIncrement, hlegal]

/-- Nonnegative remaining budget is retained after either totalized candidate outcome. -/
theorem growthCandidate_budget_nonneg (S : BoundedBatchState V B a r c k capacity)
    (idx : A) (hinitial : 0 ≤ S.state.res.budget) :
    0 ≤
      (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes
        S idx).state.res.budget := by
  classical
  unfold growthCandidateStep
  by_cases hlegal : GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx)
  · exact boundedGrowStep_budget_nonneg_of_legal S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal
  · rw [boundedGrowStep_of_not_legal S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal]
    exact hinitial

/-- Each actual candidate's known-batch CE does not increase. -/
theorem growthCandidate_objective_le (S : BoundedBatchState V B a r c k capacity) (idx : A) :
    growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx) ≤
      growthObjective S := by
  exact batchCEObjective_boundedGrowStep_le S (Zs idx S) (Ds idx S) (costs idx)
    (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx)

/-- The universal model-safety predicate is decidable from each candidate's
proved CE nonincrease, without executing architecture search. -/
noncomputable instance growthProblemAt_decidable_safe
    (S : BoundedBatchState V B a r c k capacity) :
    DecidablePred (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S).safe := by
  intro idx
  exact isTrue (fun T =>
    growthCandidate_objective_le Zs Ds costs memoryCaps operationCaps risks writes T idx)

variable [Fintype A]

/-- All candidates are feasible with their exact conditional resource increments. -/
theorem growthCandidate_mem_feasible (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (idx : A) :
    idx ∈ feasible (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S)
      (growthMemoryIncrement B V) operationBudget := by
  classical
  apply mem_feasible.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro T
    exact growthCandidate_objective_le Zs Ds costs memoryCaps operationCaps risks writes T idx
  · by_cases hlegal : GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx)
        (memoryCaps idx) (operationCaps idx)
    · simp only [growthProblemAt, growthCandidateMemoryIncrement, hlegal, ite_true]
      exact le_rfl
    · simp only [growthProblemAt, growthCandidateMemoryIncrement, hlegal, ite_false]
      exact Nat.zero_le _
  · by_cases hlegal : GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx)
        (memoryCaps idx) (operationCaps idx)
    · simpa only [growthProblemAt, growthCandidateOperationIncrement, hlegal, ite_true] using
        hop idx
    · simp only [growthProblemAt, growthCandidateOperationIncrement, hlegal, ite_false]
      exact Nat.zero_le _

/-- Every supplied candidate is eligible at the empirical nonregression floor. -/
theorem growthCandidate_quality_eligible (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (idx : A) :
    qualityEligible (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) S
      (growthMemoryIncrement B V) operationBudget (-growthObjective S) idx := by
  classical
  refine ⟨growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes S
    operationBudget hop idx, ?_⟩
  exact neg_le_neg
    (growthCandidate_objective_le Zs Ds costs memoryCaps operationCaps risks writes S idx)

/-- The existing exact finite lexicographic selector on this candidate family. -/
noncomputable def growthSelection (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) : A :=
  selection (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) S
    (growthMemoryIncrement B V) operationBudget a0
    (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes S
      operationBudget hop a0)

/-- The actual guarded successor produced by the selected candidate. -/
noncomputable def growthSelectionNext (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    BoundedBatchState V B a r c k capacity :=
  growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S
    (growthSelection
            Zs Ds costs memoryCaps operationCaps risks writes S
            operationBudget hop a0)

/-- Exact CE optimality among the supplied finite candidates under their common caps. -/
theorem growthSelection_objective_le_candidate (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 idx : A) :
    growthObjective (growthSelectionNext Zs Ds costs memoryCaps operationCaps risks writes S
      operationBudget hop a0) ≤
    growthObjective
      (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx) := by
  have h := selection_quality_optimal
    (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) S
    (growthMemoryIncrement B V) operationBudget a0
    (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes S
      operationBudget hop a0)
    idx (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes S
      operationBudget hop idx)
  simpa only [selectedNext, growthProblemAt, growthSelectionNext, growthSelection,
    neg_neg] using neg_le_neg h

/-- Nonregression follows through the supplied witness, not an assumed identity action. -/
theorem growthSelection_objective_le_current (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    growthObjective (growthSelectionNext Zs Ds costs memoryCaps operationCaps risks writes S
      operationBudget hop a0) ≤ growthObjective S := by
  calc
    _ ≤ growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes
        S a0) :=
      growthSelection_objective_le_candidate Zs Ds costs memoryCaps operationCaps risks writes S
        operationBudget hop a0 a0
    _ ≤ growthObjective S :=
      growthCandidate_objective_le Zs Ds costs memoryCaps operationCaps risks writes S a0

/-- Three-coordinate Pareto non-domination within this exact finite family. -/
theorem growthSelection_pareto (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) {idx : A}
    (hquality : growthObjective
        (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx) ≤
      growthObjective (growthSelectionNext Zs Ds costs memoryCaps operationCaps risks writes S
        operationBudget hop a0))
    (hmemory : growthCandidateMemoryIncrement Zs Ds costs memoryCaps operationCaps S idx ≤
      growthCandidateMemoryIncrement Zs Ds costs memoryCaps operationCaps S
        (growthSelection
            Zs Ds costs memoryCaps operationCaps risks writes S
            operationBudget hop a0))
    (hoperations : growthCandidateOperationIncrement Zs Ds costs memoryCaps operationCaps S idx ≤
      growthCandidateOperationIncrement Zs Ds costs memoryCaps operationCaps S
        (growthSelection
            Zs Ds costs memoryCaps operationCaps risks writes S
            operationBudget hop a0)) :
    growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx) =
        growthObjective (growthSelectionNext Zs Ds costs memoryCaps operationCaps risks writes S
          operationBudget hop a0) ∧
      growthCandidateMemoryIncrement Zs Ds costs memoryCaps operationCaps S idx =
        growthCandidateMemoryIncrement Zs Ds costs memoryCaps operationCaps S
          (growthSelection
            Zs Ds costs memoryCaps operationCaps risks writes S
            operationBudget hop a0) ∧
      growthCandidateOperationIncrement Zs Ds costs memoryCaps operationCaps S idx =
        growthCandidateOperationIncrement Zs Ds costs memoryCaps operationCaps S
          (growthSelection
            Zs Ds costs memoryCaps operationCaps risks writes S
            operationBudget hop a0) := by
  have hfeasible := growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes S
    operationBudget hop idx
  have hq := neg_le_neg hquality
  have hmem :
      (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S).memory idx ≤
      (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S).memory
        (selection
          (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) S
          (growthMemoryIncrement B V) operationBudget a0
          (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes
            S operationBudget hop a0)) := by
    simpa only [growthProblemAt, growthSelection] using hmemory
  have hops :
      (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S).operations idx ≤
      (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S).operations
        (selection
          (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) S
          (growthMemoryIncrement B V) operationBudget a0
          (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes
            S operationBudget hop a0)) := by
    simpa only [growthProblemAt, growthSelection] using hoperations
  have hpareto := selection_pareto
    (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) S
    (growthMemoryIncrement B V) operationBudget a0
    (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes S
      operationBudget hop a0)
    hfeasible hq hmem hops
  simpa only [selectedNext, growthProblemAt, growthSelectionNext, growthSelection, neg_inj] using
    hpareto

/-- Exact conditional resource minimum among candidates satisfying the CE floor.
This is a separate resource-first result, not quality-first or three-coordinate optimality. -/
theorem growthMinResource_cost_min (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    ∀ b, qualityEligible (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) S
        (growthMemoryIncrement B V) operationBudget (-growthObjective S) b →
      resourceCost (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S)
        (minimumResource (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) S
          (growthMemoryIncrement B V) operationBudget (-growthObjective S) a0
          (growthCandidate_quality_eligible Zs Ds costs memoryCaps operationCaps risks writes S
            operationBudget hop a0)) ≤
      resourceCost (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) b := by
  exact minimumResource_cost_min
    (growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S) S
    (growthMemoryIncrement B V) operationBudget (-growthObjective S) a0
    (growthCandidate_quality_eligible Zs Ds costs memoryCaps operationCaps risks writes S
      operationBudget hop a0)

end Candidates

end Hagi.Contracts.BatchCEGrowthSelection
