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

section AdmissionYield

variable
    (Zs : A → (_ : BoundedBatchState V B a r c k capacity) → Fin B → V → ℝ)
    (Ds : A → ∀ S : BoundedBatchState V B a r c k capacity,
      EuclideanSpace ℝ (Fin (S.width + 1)))
    (costs memoryCaps operationCaps : A → ℕ)
    (risks : A → ℝ) (writes : A → Option (Σ _ : ℕ, Fin c → ℝ))
    (admissions : ∀ (idx : A) (T : BoundedBatchState V B a r c k capacity),
      GrowthAdmission V T (Zs idx T) (Ds idx T) (costs idx) (memoryCaps idx)
        (operationCaps idx))

/-- Supplied-batch CE margin per one-additive model operation-counter increment. -/
noncomputable def smoothedGrowthYield (S T : BoundedBatchState V B a r c k capacity) : ℝ :=
  (growthObjective S - growthObjective T) / (T.state.res.flops - S.state.res.flops + 1)

/-- Raw admissions are zero-cost unless their constructor is fully verified. -/
noncomputable def growthAdmissionMemoryIncrement
    (S : BoundedBatchState V B a r c k capacity) (idx : A) : ℕ :=
  match admissions idx S with
  | .fullyVerified _ =>
      growthCandidateMemoryIncrement Zs Ds costs memoryCaps operationCaps S idx
  | .conditional _ _ => 0
  | .empiricalOnly _ => 0
  | .budgetViolation _ => 0
  | .unknown => 0

/-- Raw admissions consume no declared guarded-trainer operations unless verified. -/
noncomputable def growthAdmissionOperationIncrement
    (S : BoundedBatchState V B a r c k capacity) (idx : A) : ℕ :=
  match admissions idx S with
  | .fullyVerified _ =>
      growthCandidateOperationIncrement Zs Ds costs memoryCaps operationCaps S idx
  | .conditional _ _ => 0
  | .empiricalOnly _ => 0
  | .budgetViolation _ => 0
  | .unknown => 0

/-- The existing finite problem with actual quarantined steps and reference-state costs. -/
noncomputable def growthAdmissionProblemAt (S : BoundedBatchState V B a r c k capacity) :
    ControllerProblem A (BoundedBatchState V B a r c k capacity) := by
  classical
  exact
    { growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S with
      value := smoothedGrowthYield S
      step := fun idx T => quarantinedGrowStep T (Zs idx T) (Ds idx T) (costs idx)
        (memoryCaps idx) (operationCaps idx) (admissions idx T) (risks idx) (writes idx)
      safe := fun idx => ∀ T,
        growthObjective (quarantinedGrowStep T (Zs idx T) (Ds idx T) (costs idx)
          (memoryCaps idx) (operationCaps idx) (admissions idx T) (risks idx)
          (writes idx)) ≤ growthObjective T
      memory := growthAdmissionMemoryIncrement Zs Ds costs memoryCaps operationCaps admissions S
      operations := growthAdmissionOperationIncrement Zs Ds costs memoryCaps operationCaps
        admissions S }

/-- Quarantined nonincrease decides the model-level safety predicate. -/
noncomputable instance growthAdmissionProblemAt_decidable_safe
    (S : BoundedBatchState V B a r c k capacity) :
    DecidablePred (growthAdmissionProblemAt Zs Ds costs memoryCaps operationCaps risks writes
      admissions S).safe := by
  intro idx
  exact isTrue (fun T => growthObjective_quarantinedGrowStep_le T (Zs idx T) (Ds idx T)
    (costs idx) (memoryCaps idx) (operationCaps idx) (admissions idx T) (risks idx)
    (writes idx))

variable [Fintype A]

/-- Every quarantined candidate is feasible under the common verified-operation cap. -/
theorem growthAdmission_mem_feasible (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (idx : A) :
    idx ∈ feasible (growthAdmissionProblemAt Zs Ds costs memoryCaps operationCaps risks writes
      admissions S) (growthMemoryIncrement B V) operationBudget := by
  classical
  apply mem_feasible.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro T
    exact growthObjective_quarantinedGrowStep_le T (Zs idx T) (Ds idx T) (costs idx)
      (memoryCaps idx) (operationCaps idx) (admissions idx T) (risks idx) (writes idx)
  · cases hadm : admissions idx S with
    | fullyVerified hlegal =>
        simp only [growthAdmissionProblemAt, growthAdmissionMemoryIncrement, hadm,
          growthCandidateMemoryIncrement, hlegal, ite_true]
        exact le_rfl
    | conditional _ _ =>
        simp only [growthAdmissionProblemAt, growthAdmissionMemoryIncrement, hadm]
        exact Nat.zero_le _
    | empiricalOnly _ =>
        simp only [growthAdmissionProblemAt, growthAdmissionMemoryIncrement, hadm]
        exact Nat.zero_le _
    | budgetViolation _ =>
        simp only [growthAdmissionProblemAt, growthAdmissionMemoryIncrement, hadm]
        exact Nat.zero_le _
    | unknown =>
        simp only [growthAdmissionProblemAt, growthAdmissionMemoryIncrement, hadm]
        exact Nat.zero_le _
  · cases hadm : admissions idx S with
    | fullyVerified hlegal =>
        simpa only [growthAdmissionProblemAt, growthAdmissionOperationIncrement, hadm,
          growthCandidateOperationIncrement, hlegal, ite_true] using hop idx
    | conditional _ _ =>
        simp only [growthAdmissionProblemAt, growthAdmissionOperationIncrement, hadm]
        exact Nat.zero_le _
    | empiricalOnly _ =>
        simp only [growthAdmissionProblemAt, growthAdmissionOperationIncrement, hadm]
        exact Nat.zero_le _
    | budgetViolation _ =>
        simp only [growthAdmissionProblemAt, growthAdmissionOperationIncrement, hadm]
        exact Nat.zero_le _
    | unknown =>
        simp only [growthAdmissionProblemAt, growthAdmissionOperationIncrement, hadm]
        exact Nat.zero_le _

/-- Thin reuse of the existing exact finite selector. -/
noncomputable def growthAdmissionSelection (S : BoundedBatchState V B a r c k capacity)
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) : A :=
  selection (growthAdmissionProblemAt Zs Ds costs memoryCaps operationCaps risks writes
    admissions S) S (growthMemoryIncrement B V) operationBudget a0
    (growthAdmission_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes admissions S
      operationBudget hop a0)

/-- The selected actual quarantined successor maximizes yield in this feasible finite bank. -/
theorem growthAdmissionSelection_smoothedGrowthYield_ge_candidate
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 idx : A)
    (hfeasible : idx ∈ feasible
      (growthAdmissionProblemAt Zs Ds costs memoryCaps operationCaps risks writes admissions S)
      (growthMemoryIncrement B V) operationBudget) :
    smoothedGrowthYield S (quarantinedGrowStep S (Zs idx S) (Ds idx S) (costs idx)
        (memoryCaps idx) (operationCaps idx) (admissions idx S) (risks idx) (writes idx)) ≤
      smoothedGrowthYield S (selectedNext
        (growthAdmissionProblemAt Zs Ds costs memoryCaps operationCaps risks writes admissions S)
        S (growthMemoryIncrement B V) operationBudget a0
        (growthAdmission_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes admissions
          S operationBudget hop a0)) :=
  selection_quality_optimal
    (growthAdmissionProblemAt Zs Ds costs memoryCaps operationCaps risks writes admissions S)
    S (growthMemoryIncrement B V) operationBudget a0
    (growthAdmission_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes admissions S
      operationBudget hop a0) idx hfeasible

/-- Selected quarantined safety gives supplied-batch CE nonincrease at the reference state. -/
theorem growthAdmissionSelection_objective_le_current
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    growthObjective (selectedNext
      (growthAdmissionProblemAt Zs Ds costs memoryCaps operationCaps risks writes admissions S)
      S (growthMemoryIncrement B V) operationBudget a0
      (growthAdmission_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes admissions S
        operationBudget hop a0)) ≤ growthObjective S := by
  have hselected := selection_admissible
    (growthAdmissionProblemAt Zs Ds costs memoryCaps operationCaps risks writes admissions S)
    S (growthMemoryIncrement B V) operationBudget a0
    (growthAdmission_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes admissions S
      operationBudget hop a0)
  have hsafe := (mem_feasible.mp hselected).1
  exact hsafe S

omit [Fintype A] in
/-- Actual quarantined successors never decrease the model operation counter. -/
theorem quarantinedGrowStep_flops_sub_nonneg
    (T : BoundedBatchState V B a r c k capacity) (idx : A) :
    0 ≤ (quarantinedGrowStep T (Zs idx T) (Ds idx T) (costs idx) (memoryCaps idx)
      (operationCaps idx) (admissions idx T) (risks idx) (writes idx)).state.res.flops -
        T.state.res.flops := by
  cases admissions idx T with
  | fullyVerified hlegal =>
      rw [quarantinedGrowStep, boundedGrowStep_flops_of_legal T (Zs idx T) (Ds idx T)
        (costs idx) (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal]
      simpa only [add_sub_cancel_left] using
        Nat.cast_nonneg (α := ℝ) (growthOperations B V (costs idx))
  | conditional _ _ => simp only [quarantinedGrowStep, sub_self, le_refl]
  | empiricalOnly _ => simp only [quarantinedGrowStep, sub_self, le_refl]
  | budgetViolation _ => simp only [quarantinedGrowStep, sub_self, le_refl]
  | unknown => simp only [quarantinedGrowStep, sub_self, le_refl]

omit [Fintype A] in
/-- Actual quarantined successors have nonnegative one-additive smoothed yield. -/
theorem smoothedGrowthYield_quarantinedGrowStep_nonneg
    (T : BoundedBatchState V B a r c k capacity) (idx : A) :
    0 ≤ smoothedGrowthYield T (quarantinedGrowStep T (Zs idx T) (Ds idx T) (costs idx)
      (memoryCaps idx) (operationCaps idx) (admissions idx T) (risks idx) (writes idx)) := by
  have hnumerator : 0 ≤ growthObjective T - growthObjective
      (quarantinedGrowStep T (Zs idx T) (Ds idx T) (costs idx) (memoryCaps idx)
        (operationCaps idx) (admissions idx T) (risks idx) (writes idx)) :=
    sub_nonneg.mpr (growthObjective_quarantinedGrowStep_le T (Zs idx T) (Ds idx T)
      (costs idx) (memoryCaps idx) (operationCaps idx) (admissions idx T) (risks idx)
      (writes idx))
  have hflops := quarantinedGrowStep_flops_sub_nonneg Zs Ds costs memoryCaps operationCaps
    risks writes admissions T idx
  exact div_nonneg hnumerator (by linarith)

/-- Equal actual successors have zero smoothed yield without a special zero-denominator case. -/
theorem smoothedGrowthYield_self (S : BoundedBatchState V B a r c k capacity) :
    smoothedGrowthYield S S = 0 := by
  simp [smoothedGrowthYield]

open Filter Topology

/-- The actual quarantined successor selected at the current state. -/
noncomputable def growthAdmissionSelectionNext
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    BoundedBatchState V B a r c k capacity :=
  selectedNext
    (growthAdmissionProblemAt Zs Ds costs memoryCaps operationCaps risks writes admissions S)
    S (growthMemoryIncrement B V) operationBudget a0
    (growthAdmission_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes admissions S
      operationBudget hop a0)

/-- The selected successor is the quarantined step at the selected current-state index. -/
theorem growthAdmissionSelectionNext_eq_quarantinedGrowStep
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes admissions S
        operationBudget hop a0 =
      quarantinedGrowStep S
        (Zs (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions S
          operationBudget hop a0) S)
        (Ds (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions S
          operationBudget hop a0) S)
        (costs (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions S
          operationBudget hop a0))
        (memoryCaps (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps risks writes
          admissions S operationBudget hop a0))
        (operationCaps (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps risks writes
          admissions S operationBudget hop a0))
        (admissions
          (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps risks writes admissions S
            operationBudget hop a0) S)
        (risks (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions S operationBudget hop a0))
        (writes (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions S operationBudget hop a0)) := by
  rfl

/-- Standard iteration of the actual selected successor, with no separate state framework. -/
noncomputable def growthAdmissionSelectionPath
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) (n : ℕ) :
    BoundedBatchState V B a r c k capacity :=
  (fun T => growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes
    admissions T operationBudget hop a0)^[n] S0

/-- Only the selected constructor contributes declared operations;
  bank evaluation is not charged. -/
theorem growthAdmissionSelectionNext_flops
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    (growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes admissions S
        operationBudget hop a0).state.res.flops =
      S.state.res.flops +
        (growthAdmissionOperationIncrement Zs Ds costs memoryCaps operationCaps admissions S
          (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps risks writes admissions S
            operationBudget hop a0) : ℝ) := by
  rw [growthAdmissionSelectionNext_eq_quarantinedGrowStep]
  cases hadm : admissions
      (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps risks writes admissions S
        operationBudget hop a0) S with
  | fullyVerified hlegal =>
      rw [quarantinedGrowStep, boundedGrowStep_flops_of_legal S
        (Zs (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions S
          operationBudget hop a0) S)
        (Ds (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions S
          operationBudget hop a0) S)
        (costs (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions S
          operationBudget hop a0))
        (memoryCaps (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps risks writes
          admissions S operationBudget hop a0))
        (operationCaps (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps risks writes
          admissions S operationBudget hop a0)) (risks _) (writes _) hlegal]
      simp only [growthAdmissionOperationIncrement, hadm, growthCandidateOperationIncrement,
        hlegal, ite_true]
  | conditional _ _ =>
      simp only [quarantinedGrowStep, growthAdmissionOperationIncrement, hadm, Nat.cast_zero,
        add_zero]
  | empiricalOnly _ =>
      simp only [quarantinedGrowStep, growthAdmissionOperationIncrement, hadm, Nat.cast_zero,
        add_zero]
  | budgetViolation _ =>
      simp only [quarantinedGrowStep, growthAdmissionOperationIncrement, hadm, Nat.cast_zero,
        add_zero]
  | unknown =>
      simp only [quarantinedGrowStep, growthAdmissionOperationIncrement, hadm, Nat.cast_zero,
        add_zero]

/-- A positive actual current-state candidate yield forces strict supplied-batch CE progress. -/
theorem growthAdmissionSelectionNext_objective_lt_of_candidate_pos
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 idx : A)
    (hpositive : 0 < smoothedGrowthYield S
      (quarantinedGrowStep S (Zs idx S) (Ds idx S) (costs idx) (memoryCaps idx)
        (operationCaps idx) (admissions idx S) (risks idx) (writes idx))) :
    growthObjective
      (growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps
        risks writes admissions S operationBudget hop a0) < growthObjective S := by
  have hle : smoothedGrowthYield S
      (quarantinedGrowStep S (Zs idx S) (Ds idx S) (costs idx) (memoryCaps idx)
        (operationCaps idx) (admissions idx S) (risks idx) (writes idx)) ≤
      smoothedGrowthYield S (growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps
        risks writes admissions S operationBudget hop a0) := by
    simpa only [growthAdmissionSelectionNext] using
      growthAdmissionSelection_smoothedGrowthYield_ge_candidate
        Zs Ds costs memoryCaps operationCaps risks writes admissions S operationBudget hop a0 idx
        (growthAdmission_mem_feasible Zs Ds costs memoryCaps operationCaps
          risks writes admissions S
          operationBudget hop idx)
  have hselectedPos : 0 < smoothedGrowthYield S
      (growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes admissions S
        operationBudget hop a0) := lt_of_lt_of_le hpositive hle
  have hflops : 0 ≤
      (growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes admissions S
        operationBudget hop a0).state.res.flops - S.state.res.flops := by
    rw [growthAdmissionSelectionNext_eq_quarantinedGrowStep]
    exact quarantinedGrowStep_flops_sub_nonneg Zs Ds costs memoryCaps operationCaps risks writes
      admissions S
      (growthAdmissionSelection Zs Ds costs memoryCaps operationCaps risks writes admissions S
        operationBudget hop a0)
  have hdenom : 0 <
      (growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes admissions S
        operationBudget hop a0).state.res.flops - S.state.res.flops + 1 := by
    linarith
  unfold smoothedGrowthYield at hselectedPos
  have hnumerator : 0 < growthObjective S -
      growthObjective (growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps
        risks writes admissions S operationBudget hop a0) :=
    (div_pos_iff_of_pos_right hdenom).mp hselectedPos
  exact sub_pos.mp hnumerator

/-- Supplied-batch CE is antitone along the selected iterates. -/
theorem growthObjective_iteratedGrowthAdmissionSelection_antitone
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    Antitone (fun n : ℕ => growthObjective
      (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
        operationBudget hop a0 n)) := by
  apply antitone_nat_of_succ_le
  intro n
  unfold growthAdmissionSelectionPath
  rw [Function.iterate_succ_apply']
  simpa only [growthAdmissionSelectionNext] using
    growthAdmissionSelection_objective_le_current Zs Ds costs memoryCaps operationCaps risks writes
      admissions
      (((fun T : BoundedBatchState V B a r c k capacity =>
        growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes admissions T
          operationBudget hop a0)^[n]) S0)
      operationBudget hop a0

/-- Nonnegative initial budget persists along every selected quarantined iterate. -/
theorem iteratedGrowthAdmissionSelection_budget_nonneg
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A)
    (hinitial : 0 ≤ S0.state.res.budget) (n : ℕ) :
    0 ≤ (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
      operationBudget hop a0 n).state.res.budget := by
  unfold growthAdmissionSelectionPath
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      set S := ((fun T : BoundedBatchState V B a r c k capacity =>
        growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes admissions T
          operationBudget hop a0)^[n]) S0
      rw [growthAdmissionSelectionNext_eq_quarantinedGrowStep]
      let idx := growthAdmissionSelection Zs Ds costs memoryCaps operationCaps
        risks writes admissions S operationBudget hop a0
      change 0 ≤ (quarantinedGrowStep S (Zs idx S) (Ds idx S) (costs idx) (memoryCaps idx)
        (operationCaps idx) (admissions idx S) (risks idx) (writes idx)).state.res.budget
      cases admissions idx S with
      | fullyVerified hlegal =>
          exact boundedGrowStep_budget_nonneg_of_legal S (Zs idx S) (Ds idx S) (costs idx)
            (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal
      | conditional _ _ => exact ih
      | empiricalOnly _ => exact ih
      | budgetViolation _ => exact ih
      | unknown => exact ih

/-- Compare a fixed candidate at each selected state, not
  fixed-candidate trajectories or global-horizon optimality. -/
theorem growthAdmissionSelection_sum_smoothedGrowthYield_ge_candidate
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 idx : A) (T : ℕ) :
    (∑ t ∈ Finset.range T, smoothedGrowthYield
      (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
        operationBudget hop a0 t)
      (quarantinedGrowStep
        (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
          operationBudget hop a0 t)
        (Zs idx (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps risks writes
          admissions S0 operationBudget hop a0 t))
        (Ds idx (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps risks writes
          admissions S0 operationBudget hop a0 t))
        (costs idx) (memoryCaps idx) (operationCaps idx)
        (admissions idx (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes
          admissions S0 operationBudget hop a0 t))
        (risks idx) (writes idx))) ≤
      ∑ t ∈ Finset.range T, smoothedGrowthYield
        (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
          operationBudget hop a0 t)
        (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
          operationBudget hop a0 (t + 1)) := by
  have hstep (t : ℕ) :
      growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
          operationBudget hop a0 (t + 1) =
        growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes admissions
          (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
            operationBudget hop a0 t) operationBudget hop a0 := by
    unfold growthAdmissionSelectionPath
    rw [Function.iterate_succ_apply']
  apply Finset.sum_le_sum
  intro t _ht
  rw [hstep]
  simpa only [growthAdmissionSelectionNext] using
    growthAdmissionSelection_smoothedGrowthYield_ge_candidate
      Zs Ds costs memoryCaps operationCaps risks writes admissions
      (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
        operationBudget hop a0 t)
      operationBudget hop a0 idx
      (growthAdmission_mem_feasible Zs Ds costs memoryCaps operationCaps risks writes admissions
        (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
          operationBudget hop a0 t) operationBudget hop idx)

/-- The nonnegative antitone selected path converges only to its own historical infimum. -/
theorem growthObjective_iteratedGrowthAdmissionSelection_tendsto_ciInf
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    Tendsto (fun t : ℕ => growthObjective
      (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
        operationBudget hop a0 t)) atTop
      (𝓝 (⨅ t : ℕ, growthObjective
        (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
          operationBudget hop a0 t))) := by
  exact ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (growthObjective_iteratedGrowthAdmissionSelection_antitone
      Zs Ds costs memoryCaps operationCaps risks writes admissions S0 operationBudget hop a0)
    (fun _ => growthObjective_nonneg _)


end AdmissionYield

section FiniteOpenLoop

variable
    (Zs : A → (_ : BoundedBatchState V B a r c k capacity) → Fin B → V → ℝ)
    (Ds : A → ∀ S : BoundedBatchState V B a r c k capacity,
      EuclideanSpace ℝ (Fin (S.width + 1)))
    (costs memoryCaps operationCaps : A → ℕ)
    (risks : A → ℝ) (writes : A → Option (Σ _ : ℕ, Fin c → ℝ))
    (admissions : ∀ (idx : A) (T : BoundedBatchState V B a r c k capacity),
      GrowthAdmission V T (Zs idx T) (Ds idx T) (costs idx) (memoryCaps idx)
        (operationCaps idx))

/-- One current-state quarantined step and its constructor-aware resource totals. -/
noncomputable def growthAdmissionPlanStep
    (w : BoundedBatchState V B a r c k capacity × ℕ × ℕ) (idx : A) :
    BoundedBatchState V B a r c k capacity × ℕ × ℕ :=
  (quarantinedGrowStep w.1 (Zs idx w.1) (Ds idx w.1) (costs idx) (memoryCaps idx)
      (operationCaps idx) (admissions idx w.1) (risks idx) (writes idx),
    w.2.1 + growthAdmissionMemoryIncrement Zs Ds costs memoryCaps operationCaps
      admissions w.1 idx,
    w.2.2 + growthAdmissionOperationIncrement Zs Ds costs memoryCaps operationCaps
      admissions w.1 idx)

/-- One open-loop rollout step never increases supplied-batch CE. -/
theorem growthAdmissionPlanStep_objective_le
    (w : BoundedBatchState V B a r c k capacity × ℕ × ℕ) (idx : A) :
    growthObjective (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
        risks writes admissions w idx).1 ≤ growthObjective w.1 := by
  exact growthObjective_quarantinedGrowStep_le w.1 (Zs idx w.1) (Ds idx w.1)
    (costs idx) (memoryCaps idx) (operationCaps idx) (admissions idx w.1)
    (risks idx) (writes idx)

/-- All five admission constructors preserve an initially nonnegative budget. -/
theorem growthAdmissionPlanStep_budget_nonneg
    (w : BoundedBatchState V B a r c k capacity × ℕ × ℕ) (idx : A)
    (hinitial : 0 ≤ w.1.state.res.budget) :
    0 ≤ (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
      risks writes admissions w idx).1.state.res.budget := by
  change 0 ≤ (quarantinedGrowStep w.1 (Zs idx w.1) (Ds idx w.1) (costs idx)
    (memoryCaps idx) (operationCaps idx) (admissions idx w.1) (risks idx)
    (writes idx)).state.res.budget
  cases admissions idx w.1 with
  | fullyVerified hlegal =>
      exact boundedGrowStep_budget_nonneg_of_legal w.1 (Zs idx w.1) (Ds idx w.1)
        (costs idx) (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal
  | conditional _ _ => exact hinitial
  | empiricalOnly _ => exact hinitial
  | budgetViolation _ => exact hinitial
  | unknown => exact hinitial

variable [Fintype A]

omit [Fintype A] in
/-- List rollout CE nonincrease needs no operation-cap premise. -/
theorem growthAdmissionPlanFold_objective_le
    (w : BoundedBatchState V B a r c k capacity × ℕ × ℕ) (xs : List A) :
    growthObjective (List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps
        operationCaps risks writes admissions) w xs).1 ≤ growthObjective w.1 := by
  induction xs generalizing w with
  | nil => exact le_rfl
  | cons idx xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (ih (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
        risks writes admissions w idx))
        (growthAdmissionPlanStep_objective_le Zs Ds costs memoryCaps operationCaps
          risks writes admissions w idx)

omit [Fintype A] in
/-- The four-way contract for an arbitrary list and an arbitrary resource accumulator. -/
theorem growthAdmissionPlanFold_contract [Finite A]
    (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget)
    (w : BoundedBatchState V B a r c k capacity × ℕ × ℕ) (xs : List A) :
    growthObjective (List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps
        operationCaps risks writes admissions) w xs).1 ≤ growthObjective w.1 ∧
      (0 ≤ w.1.state.res.budget →
        0 ≤ (List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps
          operationCaps risks writes admissions) w xs).1.state.res.budget) ∧
      (List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
          risks writes admissions) w xs).2.1 ≤
        w.2.1 + xs.length * growthMemoryIncrement B V ∧
      (List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
          risks writes admissions) w xs).2.2 ≤
        w.2.2 + xs.length * operationBudget := by
  let _ := Fintype.ofFinite A
  induction xs generalizing w with
  | nil =>
      simp only [List.foldl_nil, List.length_nil, Nat.zero_mul, Nat.add_zero]
      exact ⟨le_rfl, fun h => h, le_rfl, le_rfl⟩
  | cons idx xs ih =>
      have hstepCE := growthAdmissionPlanStep_objective_le Zs Ds costs memoryCaps
        operationCaps risks writes admissions w idx
      have hstepBudget := growthAdmissionPlanStep_budget_nonneg Zs Ds costs memoryCaps
        operationCaps risks writes admissions w idx
      have hfeasible := growthAdmission_mem_feasible Zs Ds costs memoryCaps operationCaps
        risks writes admissions w.1 operationBudget hop idx
      have hmemStep : growthAdmissionMemoryIncrement Zs Ds costs memoryCaps operationCaps
          admissions w.1 idx ≤ growthMemoryIncrement B V := by
        simpa only [growthAdmissionProblemAt] using (mem_feasible.mp hfeasible).2.1
      have hopsStep : growthAdmissionOperationIncrement Zs Ds costs memoryCaps operationCaps
          admissions w.1 idx ≤ operationBudget := by
        simpa only [growthAdmissionProblemAt] using (mem_feasible.mp hfeasible).2.2
      have h := ih (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
        risks writes admissions w idx)
      have hmem : (List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
          risks writes admissions)
          (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
            risks writes admissions w idx) xs).2.1 ≤
          w.2.1 + growthAdmissionMemoryIncrement Zs Ds costs memoryCaps operationCaps
            admissions w.1 idx + xs.length * growthMemoryIncrement B V := by
        simpa only [growthAdmissionPlanStep, Nat.add_assoc] using h.2.2.1
      have hops : (List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
          risks writes admissions)
          (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
            risks writes admissions w idx) xs).2.2 ≤
          w.2.2 + growthAdmissionOperationIncrement Zs Ds costs memoryCaps operationCaps
            admissions w.1 idx + xs.length * operationBudget := by
        simpa only [growthAdmissionPlanStep, Nat.add_assoc] using h.2.2.2
      simp only [List.foldl_cons]
      refine ⟨le_trans h.1 hstepCE, ?_, ?_, ?_⟩
      · intro hw
        exact h.2.1 (hstepBudget hw)
      · simp only [List.length_cons, Nat.succ_mul]
        omega
      · simp only [List.length_cons, Nat.succ_mul]
        omega

/-- Full plan evaluation from one current state with initially zero declared totals. -/
noncomputable def growthAdmissionPlanRollout {H : ℕ}
    (S : BoundedBatchState V B a r c k capacity) (plan : Fin H → A) :
    BoundedBatchState V B a r c k capacity × ℕ × ℕ :=
  List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
    risks writes admissions) (S, 0, 0) (List.ofFn plan)

/-- Fixed-state finite controller problem whose actions are exact open-loop plans. -/
noncomputable def growthAdmissionPlanProblemAt (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) :
    ControllerProblem (Fin H → A) (BoundedBatchState V B a r c k capacity) := by
  classical
  exact
    { value := fun T => -growthObjective T
      step := fun plan T =>
        (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions T plan).1
      memory := fun plan =>
        (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0 plan).2.1
      operations := fun plan =>
        (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0 plan).2.2
      safe := fun plan => ∀ T,
        growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions T plan).1 ≤ growthObjective T }

/-- Current-state rollout safety supplies the plan-local decidable predicate. -/
noncomputable instance growthAdmissionPlanProblemAt_decidable_safe (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) :
    DecidablePred (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0).safe := by
  intro plan
  apply isTrue
  intro T
  exact growthAdmissionPlanFold_objective_le Zs Ds costs memoryCaps operationCaps
    risks writes admissions (T, 0, 0) (List.ofFn plan)

/-- Every supplied plan is safe and has its two horizon-scaled resource caps. -/
theorem growthAdmissionPlan_mem_feasible (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (plan : Fin H → A) :
    plan ∈ feasible (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps operationCaps
        risks writes admissions H S0)
      (H * growthMemoryIncrement B V) (H * operationBudget) := by
  apply mem_feasible.mpr
  have h := growthAdmissionPlanFold_contract Zs Ds costs memoryCaps operationCaps
    risks writes admissions operationBudget hop (S0, 0, 0) (List.ofFn plan)
  refine ⟨?_, ?_, ?_⟩
  · intro T
    exact growthAdmissionPlanFold_objective_le Zs Ds costs memoryCaps operationCaps
      risks writes admissions (T, 0, 0) (List.ofFn plan)
  · simpa only [growthAdmissionPlanProblemAt, growthAdmissionPlanRollout,
      List.length_ofFn, Nat.zero_add] using h.2.2.1
  · simpa only [growthAdmissionPlanProblemAt, growthAdmissionPlanRollout,
      List.length_ofFn, Nat.zero_add] using h.2.2.2

/-- Exact existing finite selection, with a constant supplied action as its witness. -/
noncomputable def growthAdmissionPlanSelection (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) : Fin H → A :=
  selection (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0) S0
    (H * growthMemoryIncrement B V) (H * operationBudget) (fun _ : Fin H => a0)
    (growthAdmissionPlan_mem_feasible Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0 operationBudget hop (fun _ : Fin H => a0))

/-- The selected plan has minimum terminal supplied-batch CE among all feasible plans. -/
theorem growthAdmissionPlanSelection_objective_le (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A)
    (plan : Fin H → A)
    (hfeasible : plan ∈ feasible (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps
        operationCaps risks writes admissions H S0)
      (H * growthMemoryIncrement B V) (H * operationBudget)) :
    growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0
        (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions H S0 operationBudget hop a0)).1 ≤
      growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0 plan).1 := by
  have h := selection_quality_optimal
    (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0) S0
    (H * growthMemoryIncrement B V) (H * operationBudget) (fun _ : Fin H => a0)
    (growthAdmissionPlan_mem_feasible Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0 operationBudget hop (fun _ : Fin H => a0)) plan hfeasible
  change -growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
      risks writes admissions S0 plan).1 ≤
    -growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
      risks writes admissions S0
      (selection (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps operationCaps
          risks writes admissions H S0) S0
        (H * growthMemoryIncrement B V) (H * operationBudget) (fun _ : Fin H => a0)
        (growthAdmissionPlan_mem_feasible Zs Ds costs memoryCaps operationCaps
          risks writes admissions H S0 operationBudget hop (fun _ : Fin H => a0)))).1 at h
  simpa only [growthAdmissionPlanSelection] using neg_le_neg_iff.mp h

/-- Selected declared memory is bounded by the horizon-scaled cap. -/
theorem growthAdmissionPlanSelection_memory_le (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps risks writes admissions S0
        (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions H S0 operationBudget hop a0)).2.1 ≤
      H * growthMemoryIncrement B V := by
  have h := selection_memory_le
    (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0) S0
    (H * growthMemoryIncrement B V) (H * operationBudget) (fun _ : Fin H => a0)
    (growthAdmissionPlan_mem_feasible Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0 operationBudget hop (fun _ : Fin H => a0))
  simpa only [growthAdmissionPlanProblemAt, growthAdmissionPlanSelection] using h

/-- Selected declared operations are bounded by the horizon-scaled cap. -/
theorem growthAdmissionPlanSelection_operations_le (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps risks writes admissions S0
        (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions H S0 operationBudget hop a0)).2.2 ≤
      H * operationBudget := by
  have h := selection_operations_le
    (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0) S0
    (H * growthMemoryIncrement B V) (H * operationBudget) (fun _ : Fin H => a0)
    (growthAdmissionPlan_mem_feasible Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0 operationBudget hop (fun _ : Fin H => a0))
  simpa only [growthAdmissionPlanProblemAt, growthAdmissionPlanSelection] using h

/-- A nonnegative initial real budget survives the entire selected rollout. -/
theorem growthAdmissionPlanSelection_budget_nonneg (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A)
    (hinitial : 0 ≤ S0.state.res.budget) :
    0 ≤ (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
      risks writes admissions S0
      (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
        risks writes admissions H S0 operationBudget hop a0)).1.state.res.budget := by
  exact (growthAdmissionPlanFold_contract Zs Ds costs memoryCaps operationCaps
    risks writes admissions operationBudget hop (S0, 0, 0)
    (List.ofFn (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0 operationBudget hop a0))).2.1 hinitial

/-- Full terminal-objective/resource lex comparison against any feasible plan. -/
theorem growthAdmissionPlanSelection_lt_or_eq_and_resource_lex (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A)
    (plan : Fin H → A)
    (hfeasible : plan ∈ feasible (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps
        operationCaps risks writes admissions H S0)
      (H * growthMemoryIncrement B V) (H * operationBudget)) :
    growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0
        (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions H S0 operationBudget hop a0)).1 <
        growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0 plan).1 ∨
      (growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
          (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
            risks writes admissions H S0 operationBudget hop a0)).1 =
        growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0 plan).1 ∧
        toLex
          (-((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0 plan).2.1 : ℤ),
            -((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0 plan).2.2 : ℤ)) ≤
        toLex
          (-((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0
              (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
                risks writes admissions H S0 operationBudget hop a0)).2.1 : ℤ),
            -((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0
              (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
                risks writes admissions H S0 operationBudget hop a0)).2.2 : ℤ))) := by
  have h := selection_optimal
    (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0) S0
    (H * growthMemoryIncrement B V) (H * operationBudget) (fun _ : Fin H => a0)
    (growthAdmissionPlan_mem_feasible Zs Ds costs memoryCaps operationCaps
      risks writes admissions H S0 operationBudget hop (fun _ : Fin H => a0)) plan hfeasible
  change toLex
      (-growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0 plan).1,
        toLex
          (-((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0 plan).2.1 : ℤ),
            -((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0 plan).2.2 : ℤ))) ≤
    toLex
      (-growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
          (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
            risks writes admissions H S0 operationBudget hop a0)).1,
        toLex
          (-((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0
              (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
                risks writes admissions H S0 operationBudget hop a0)).2.1 : ℤ),
            -((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0
              (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
                risks writes admissions H S0 operationBudget hop a0)).2.2 : ℤ))) at h
  rcases Prod.Lex.toLex_le_toLex.mp h with hlt | ⟨heq, hresources⟩
  · exact Or.inl (neg_lt_neg_iff.mp hlt)
  · exact Or.inr ⟨by linarith, hresources⟩

/-- The finite schedule cardinal is a size fact, not an execution-time bound. -/
theorem fintypeCard_growthAdmissionPlan (H : ℕ) :
    Fintype.card (Fin H → A) = Fintype.card A ^ H := by
  classical
  exact Fintype.card_pi_const A H

end FiniteOpenLoop

section Boundaries

variable
    (Zs : A → (_ : BoundedBatchState V B a r c k capacity) → Fin B → V → ℝ)
    (Ds : A → ∀ S : BoundedBatchState V B a r c k capacity,
      EuclideanSpace ℝ (Fin (S.width + 1)))
    (costs memoryCaps operationCaps : A → ℕ)
    (risks : A → ℝ) (writes : A → Option (Σ _ : ℕ, Fin c → ℝ))

/-- At zero horizon the rollout is the original state with zero accumulated totals. -/
theorem growthAdmissionPlanRollout_zero
    (admissions : ∀ (idx : A) (T : BoundedBatchState V B a r c k capacity),
      GrowthAdmission V T (Zs idx T) (Ds idx T) (costs idx) (memoryCaps idx)
        (operationCaps idx))
    (S : BoundedBatchState V B a r c k capacity) (plan : Fin 0 → A) :
    growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
      risks writes admissions S plan = (S, 0, 0) := by
  rfl

/-- Entirely unknown plans hold at every step and consume zero declared resources. -/
theorem growthAdmissionPlanRollout_unknown {H : ℕ}
    (S : BoundedBatchState V B a r c k capacity) (plan : Fin H → A) :
    growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps risks writes
      (fun _ _ => .unknown) S plan = (S, 0, 0) := by
  unfold growthAdmissionPlanRollout
  generalize List.ofFn plan = xs
  induction xs generalizing S with
  | nil => rfl
  | cons idx xs ih =>
      rw [List.foldl_cons]
      change List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
        risks writes (fun _ _ => .unknown)) (S, 0, 0) xs = (S, 0, 0)
      exact ih S

/-- Empirical metadata alone is also a literal hold with zero declared resources. -/
theorem growthAdmissionPlanRollout_empiricalOnly {H : ℕ} (testRuns : ℕ)
    (S : BoundedBatchState V B a r c k capacity) (plan : Fin H → A) :
    growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps risks writes
      (fun _ _ => .empiricalOnly testRuns) S plan = (S, 0, 0) := by
  unfold growthAdmissionPlanRollout
  generalize List.ofFn plan = xs
  induction xs generalizing S with
  | nil => rfl
  | cons idx xs ih =>
      rw [List.foldl_cons]
      change List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
        risks writes (fun _ _ => .empiricalOnly testRuns)) (S, 0, 0) xs = (S, 0, 0)
      exact ih S

end Boundaries

section RealizedGreedyTrace

variable
    (Zs : A → (_ : BoundedBatchState V B a r c k capacity) → Fin B → V → ℝ)
    (Ds : A → ∀ S : BoundedBatchState V B a r c k capacity,
      EuclideanSpace ℝ (Fin (S.width + 1)))
    (costs memoryCaps operationCaps : A → ℕ)
    (risks : A → ℝ) (writes : A → Option (Σ _ : ℕ, Fin c → ℝ))
    (admissions : ∀ (idx : A) (T : BoundedBatchState V B a r c k capacity),
      GrowthAdmission V T (Zs idx T) (Ds idx T) (costs idx) (memoryCaps idx)
        (operationCaps idx))

variable [Fintype A]

/-- The action selected at each state actually reached by the current-state selector. -/
noncomputable def growthAdmissionSelectionTrace (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) : Fin H → A :=
  fun t => growthAdmissionSelection Zs Ds costs memoryCaps operationCaps risks writes admissions
    (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps risks writes admissions S0
      operationBudget hop a0 t.val) operationBudget hop a0

/-- Rolling out the realized trace preserves the selected path and arbitrary resource totals. -/
theorem growthAdmissionSelectionTrace_fold_state
    (w : BoundedBatchState V B a r c k capacity × ℕ × ℕ) (H : ℕ) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    (List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
        risks writes admissions) w
      (List.ofFn (growthAdmissionSelectionTrace Zs Ds costs memoryCaps operationCaps
        risks writes admissions H w.1 operationBudget hop a0))).1 =
      growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps risks writes admissions
        w.1 operationBudget hop a0 H := by
  induction H generalizing w with
  | zero => rfl
  | succ H ih =>
      rw [List.ofFn_succ, List.foldl_cons]
      have hstep :
          (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps risks writes admissions w
            (growthAdmissionSelectionTrace Zs Ds costs memoryCaps operationCaps risks writes
              admissions (H + 1) w.1 operationBudget hop a0 0)).1 =
            growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes
              admissions w.1 operationBudget hop a0 := by
        simp only [growthAdmissionSelectionTrace, Fin.val_zero, growthAdmissionSelectionPath,
          Function.iterate_zero_apply, growthAdmissionPlanStep]
        rw [growthAdmissionSelectionNext_eq_quarantinedGrowStep]
      have htail :
          (fun i : Fin H => growthAdmissionSelectionTrace Zs Ds costs memoryCaps operationCaps
              risks writes admissions (H + 1) w.1 operationBudget hop a0 i.succ) =
            growthAdmissionSelectionTrace Zs Ds costs memoryCaps operationCaps risks writes
              admissions H
                (growthAdmissionSelectionNext Zs Ds costs memoryCaps operationCaps risks writes
                  admissions w.1 operationBudget hop a0) operationBudget hop a0 := by
        funext i
        simp only [growthAdmissionSelectionTrace, Fin.val_succ, growthAdmissionSelectionPath,
          Function.iterate_succ_apply]
      rw [htail, growthAdmissionSelectionPath, Function.iterate_succ_apply]
      simpa only [hstep, growthAdmissionSelectionPath] using
        ih (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps risks writes admissions w
          (growthAdmissionSelectionTrace Zs Ds costs memoryCaps operationCaps risks writes
            admissions (H + 1) w.1 operationBudget hop a0 0))

/-- Exact finite open-loop selection has terminal CE no larger than the realized greedy path. -/
theorem growthAdmissionPlanSelection_objective_le_realized_path (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A) :
    growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0
        (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions H S0 operationBudget hop a0)).1 ≤
      growthObjective (growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0 operationBudget hop a0 H) := by
  have hstate := growthAdmissionSelectionTrace_fold_state Zs Ds costs memoryCaps operationCaps
    risks writes admissions (S0, 0, 0) H operationBudget hop a0
  change (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps risks writes admissions
    S0 (growthAdmissionSelectionTrace Zs Ds costs memoryCaps operationCaps risks writes admissions
      H S0 operationBudget hop a0)).1 =
    growthAdmissionSelectionPath Zs Ds costs memoryCaps operationCaps risks writes admissions S0
      operationBudget hop a0 H at hstate
  have hfeasible := growthAdmissionPlan_mem_feasible Zs Ds costs memoryCaps operationCaps
    risks writes admissions H S0 operationBudget hop
    (growthAdmissionSelectionTrace Zs Ds costs memoryCaps operationCaps risks writes admissions
      H S0 operationBudget hop a0)
  have hle := growthAdmissionPlanSelection_objective_le Zs Ds costs memoryCaps operationCaps
    risks writes admissions H S0 operationBudget hop a0
    (growthAdmissionSelectionTrace Zs Ds costs memoryCaps operationCaps risks writes admissions
      H S0 operationBudget hop a0) hfeasible
  rw [hstate] at hle
  exact hle

end RealizedGreedyTrace

section PlanResourceAccounting

variable
    (Zs : A → (_ : BoundedBatchState V B a r c k capacity) → Fin B → V → ℝ)
    (Ds : A → ∀ S : BoundedBatchState V B a r c k capacity,
      EuclideanSpace ℝ (Fin (S.width + 1)))
    (costs memoryCaps operationCaps : A → ℕ)
    (risks : A → ℝ) (writes : A → Option (Σ _ : ℕ, Fin c → ℝ))
    (admissions : ∀ (idx : A) (T : BoundedBatchState V B a r c k capacity),
      GrowthAdmission V T (Zs idx T) (Ds idx T) (costs idx) (memoryCaps idx)
        (operationCaps idx))

/-- One arbitrary plan step adds exactly its constructor-aware declared operations. -/
theorem growthAdmissionPlanStep_flops
    (w : BoundedBatchState V B a r c k capacity × ℕ × ℕ) (idx : A) :
    (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps risks writes admissions
        w idx).1.state.res.flops =
      w.1.state.res.flops +
        (growthAdmissionOperationIncrement Zs Ds costs memoryCaps operationCaps
          admissions w.1 idx : ℝ) := by
  change (quarantinedGrowStep w.1 (Zs idx w.1) (Ds idx w.1) (costs idx)
      (memoryCaps idx) (operationCaps idx) (admissions idx w.1) (risks idx)
      (writes idx)).state.res.flops =
    w.1.state.res.flops +
      (growthAdmissionOperationIncrement Zs Ds costs memoryCaps operationCaps
        admissions w.1 idx : ℝ)
  cases hadm : admissions idx w.1 with
  | fullyVerified _ =>
      simpa only [quarantinedGrowStep, growthAdmissionOperationIncrement, hadm,
        growthCandidateStep] using
        (growthCandidate_flops Zs Ds costs memoryCaps operationCaps risks writes w.1 idx)
  | conditional _ _ =>
      simp only [quarantinedGrowStep, growthAdmissionOperationIncrement, hadm,
        Nat.cast_zero, add_zero]
  | empiricalOnly _ =>
      simp only [quarantinedGrowStep, growthAdmissionOperationIncrement, hadm,
        Nat.cast_zero, add_zero]
  | budgetViolation _ =>
      simp only [quarantinedGrowStep, growthAdmissionOperationIncrement, hadm,
        Nat.cast_zero, add_zero]
  | unknown =>
      simp only [quarantinedGrowStep, growthAdmissionOperationIncrement, hadm,
        Nat.cast_zero, add_zero]

/-- Exact declared-flops balance for a fold from arbitrary memory/operation totals. -/
theorem growthAdmissionPlanFold_flops
    (w : BoundedBatchState V B a r c k capacity × ℕ × ℕ) (xs : List A) :
    (List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
        risks writes admissions) w xs).1.state.res.flops + (w.2.2 : ℝ) =
      w.1.state.res.flops +
        ((List.foldl (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
          risks writes admissions) w xs).2.2 : ℝ) := by
  induction xs generalizing w with
  | nil => simp only [List.foldl_nil]
  | cons idx xs ih =>
      rw [List.foldl_cons]
      have hfold := ih (growthAdmissionPlanStep Zs Ds costs memoryCaps operationCaps
        risks writes admissions w idx)
      rw [growthAdmissionPlanStep_flops Zs Ds costs memoryCaps operationCaps
        risks writes admissions w idx] at hfold
      simp only [growthAdmissionPlanStep, Nat.cast_add] at hfold ⊢
      linarith only [hfold]

/-- A rollout from zero declared totals ends with initial flops plus final operations. -/
theorem growthAdmissionPlanRollout_flops {H : ℕ}
    (S : BoundedBatchState V B a r c k capacity) (plan : Fin H → A) :
    (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps risks writes admissions
        S plan).1.state.res.flops =
      S.state.res.flops +
        ((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S plan).2.2 : ℝ) := by
  have h := growthAdmissionPlanFold_flops Zs Ds costs memoryCaps operationCaps
    risks writes admissions (S, 0, 0) (List.ofFn plan)
  simpa only [growthAdmissionPlanRollout, Nat.cast_zero, add_zero] using h


/-- At equal terminal CE and declared memory, exact plan selection also uses no
more terminal real declared flops than any feasible alternative plan. -/
theorem growthAdmissionPlanSelection_flops_le_of_objective_eq_and_memory_eq
    [Fintype A] (H : ℕ)
    (S0 : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 : A)
    (plan : Fin H → A)
    (hfeasible : plan ∈ feasible (growthAdmissionPlanProblemAt Zs Ds costs memoryCaps
        operationCaps risks writes admissions H S0)
      (H * growthMemoryIncrement B V) (H * operationBudget))
    (hce :
      growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
        (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions H S0 operationBudget hop a0)).1 =
      growthObjective (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0 plan).1)
    (hmemory :
      (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0
        (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
          risks writes admissions H S0 operationBudget hop a0)).2.1 =
      (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0 plan).2.1) :
    (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0
      (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
        risks writes admissions H S0 operationBudget hop a0)).1.state.res.flops ≤
      (growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0 plan).1.state.res.flops := by
  rcases growthAdmissionPlanSelection_lt_or_eq_and_resource_lex Zs Ds costs memoryCaps
      operationCaps risks writes admissions H S0 operationBudget hop a0 plan hfeasible with
    hce_lt | ⟨_, hresources⟩
  · exact (ne_of_lt hce_lt hce).elim
  · rcases Prod.Lex.toLex_le_toLex.mp hresources with hmemory_lt | ⟨_, hoperations⟩
    · rw [hmemory] at hmemory_lt
      exact (lt_irrefl _ hmemory_lt).elim
    · have hopsZ :
          ((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0
            (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
              risks writes admissions H S0 operationBudget hop a0)).2.2 : ℤ) ≤
          ((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0 plan).2.2 : ℤ) := by
        exact neg_le_neg_iff.mp hoperations
      have hopsReal :
          ((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0
            (growthAdmissionPlanSelection Zs Ds costs memoryCaps operationCaps
              risks writes admissions H S0 operationBudget hop a0)).2.2 : ℝ) ≤
          ((growthAdmissionPlanRollout Zs Ds costs memoryCaps operationCaps
              risks writes admissions S0 plan).2.2 : ℝ) := by
        exact_mod_cast hopsZ
      rw [growthAdmissionPlanRollout_flops Zs Ds costs memoryCaps operationCaps
        risks writes admissions S0 (growthAdmissionPlanSelection Zs Ds costs memoryCaps
          operationCaps risks writes admissions H S0 operationBudget hop a0),
        growthAdmissionPlanRollout_flops Zs Ds costs memoryCaps operationCaps
          risks writes admissions S0 plan]
      linarith only [hopsReal]

end PlanResourceAccounting

end Hagi.Contracts.BatchCEGrowthSelection
