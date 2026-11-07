/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.BatchCEStepCertificate

set_option linter.style.header false

/-
Function-preserving growth with explicit capacity and exact narrow rejection.
The dependent batch carrier retains data at its actual current width. Its
logical scalar-cell counters include the retained new feature block, while the
operation counter is the exact Nat-cast Cycle138 guard cost. These counters do
not claim physical bytes, CUDA memory, latency or a globally optimal architecture.
-/

namespace Hagi.Contracts.BatchCEGrowth

open Hagi.Contracts.BatchCEStep Hagi.Contracts.CEStep
open Hagi.Contracts.BudgetedBatchCE Hagi.Model.BatchCEDescent
open Hagi.Model.CEExpansion Hagi.State

/-- A current batch, model and optimizer at one explicitly bounded width. -/
structure BoundedBatchState (V : Type) [Fintype V]
    (B a r c k capacity : ℕ) where
  width : ℕ
  features : Fin B → Matrix V (Fin width) ℝ
  labels : Fin B → V
  state : TrainState width a r c k
  width_le_capacity : width ≤ capacity

/-- Logical scalar cells in a retained batch feature cache of the given width. -/
def featurePayloadCells (B : ℕ) (V : Type) [Fintype V] (width : ℕ) : ℕ :=
  expandedFeatureEvaluationCount B V * width

/-- New parameter/moment cells plus new retained feature cells after one width. -/
def growthMemoryIncrement (B : ℕ) (V : Type) [Fintype V] : ℕ :=
  expandedStateCoefficients + expandedFeatureEvaluationCount B V

/-- Operations declared for the guarded expanded half-step using a Nat cost. -/
def growthOperations (B : ℕ) (V : Type) [Fintype V] (trainingCost : ℕ) : ℕ :=
  expandedFeatureEvaluationCount B V + trainingCost

/-- Complete admission before any wider state is constructed.
Nat/Real cost agreement is explicit in the fourth premise. -/
def GrowthLegal (V : Type) [Fintype V] {B a r c k capacity : ℕ}
    (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ) : Prop :=
  S.width + 1 ≤ capacity ∧
    growthMemoryIncrement B V ≤ memoryLimit ∧
    growthOperations B V trainingCost ≤ operationLimit ∧
    ((growthOperations B V trainingCost : ℕ) : ℝ) ≤ S.state.res.budget ∧
    (Nonempty (Fin B) ∧ ∀ b,
      dirAction (expandedFeatures (S.features b) (Z b))
        (coreParameters (expandedTrainState S.state)) (S.labels b) D < 0)

private theorem growthLegal_expandedCost
    {V : Type} [Fintype V] {B a r c k capacity : ℕ}
    {S : BoundedBatchState V B a r c k capacity}
    {Z : Fin B → V → ℝ} {D : EuclideanSpace ℝ (Fin (S.width + 1))}
    {trainingCost memoryLimit operationLimit : ℕ}
    (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit) :
    0 ≤ (trainingCost : ℝ) ∧
      (expandedFeatureEvaluationCount B V : ℝ) + (trainingCost : ℝ) ≤
        S.state.res.budget := by
  refine ⟨by positivity, ?_⟩
  simpa only [growthOperations, Nat.cast_add] using h.2.2.2.1

/-- The actual wider state admitted by a complete growth certificate. -/
noncomputable def grownBatchState
    {V : Type} [Fintype V] {B a r c k capacity : ℕ}
    (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit) :
    BoundedBatchState V B a r c k capacity where
  width := S.width + 1
  features := fun b => expandedFeatures (S.features b) (Z b)
  labels := S.labels
  state := expandedHalfTrainStep S.features S.labels Z D S.state
    (trainingCost : ℝ) opRisk write
  width_le_capacity := h.1

/-- Full prechecking gives literal old-state rejection, not a widened fallback. -/
noncomputable def boundedGrowStep
    {V : Type} [Fintype V] {B a r c k capacity : ℕ}
    (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    BoundedBatchState V B a r c k capacity := by
  classical
  exact if h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit then
    grownBatchState S Z D trainingCost memoryLimit operationLimit opRisk write h
  else S

variable {V : Type} [Fintype V] {B a r c k capacity : ℕ}
variable (S : BoundedBatchState V B a r c k capacity)
variable (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
variable (trainingCost memoryLimit operationLimit : ℕ)
variable (opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))

/-- Each added width retains exactly one additional feature cell per sample/class. -/
theorem featurePayloadCells_succ (width : ℕ) :
    featurePayloadCells B V (width + 1) =
      featurePayloadCells B V width + expandedFeatureEvaluationCount B V := by
  simp [featurePayloadCells, Nat.mul_succ]

/-- A legal bounded step is definitionally the actual wider batch state. -/
theorem boundedGrowStep_of_legal
    (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit) :
    boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write =
      grownBatchState S Z D trainingCost memoryLimit operationLimit opRisk write h := by
  unfold boundedGrowStep
  exact dite_eq_left h

/-- Any rejected admission preserves the literal whole batch/state record. -/
theorem boundedGrowStep_of_not_legal
    (h : ¬GrowthLegal V S Z D trainingCost memoryLimit operationLimit) :
    boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write = S := by
  unfold boundedGrowStep
  exact dite_eq_right h

/-- One policy call either preserves width or adds exactly one coordinate. -/
theorem boundedGrowStep_width_le
    (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).width ≤
      S.width + 1 := by
  by_cases h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit
  · rw [boundedGrowStep_of_legal S Z D trainingCost memoryLimit operationLimit
      opRisk write h]
    change S.width + 1 ≤ S.width + 1
    rfl
  · rw [boundedGrowStep_of_not_legal S Z D trainingCost memoryLimit operationLimit
      opRisk write h]
    omega

/-- The successor retains the caller's width capacity invariant. -/
theorem boundedGrowStep_width_le_capacity :
    (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).width ≤
      capacity :=
  (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).width_le_capacity

/-- The admitted batch has exact empirical CE descent on every sample. -/
theorem batchSampleCE_boundedGrowStep_lt_of_legal
    (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit) (b : Fin B) :
    batchSampleCE (boundedGrowStep S Z D trainingCost memoryLimit operationLimit
      opRisk write).features
        (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).labels b
        (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).state <
      batchSampleCE S.features S.labels b S.state := by
  rw [boundedGrowStep_of_legal S Z D trainingCost memoryLimit operationLimit opRisk write h]
  exact batchSampleCE_expandedHalfTrainStep_lt S.features S.labels Z D S.state
    (trainingCost : ℝ) opRisk write (growthLegal_expandedCost h) h.2.2.2.2 b

/-- Even totalized rejected admission cannot increase empirical CE on a sample. -/
theorem batchSampleCE_boundedGrowStep_le (b : Fin B) :
    batchSampleCE (boundedGrowStep S Z D trainingCost memoryLimit operationLimit
      opRisk write).features
        (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).labels b
        (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).state ≤
      batchSampleCE S.features S.labels b S.state := by
  by_cases h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit
  · exact (batchSampleCE_boundedGrowStep_lt_of_legal S Z D trainingCost memoryLimit
      operationLimit opRisk write h b).le
  · rw [boundedGrowStep_of_not_legal S Z D trainingCost memoryLimit operationLimit
      opRisk write h]

/-- Complete admission strictly lowers the actual arithmetic-mean batch CE. -/
theorem batchCEObjective_boundedGrowStep_lt_of_legal
    (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit) :
    batchCEObjective (boundedGrowStep S Z D trainingCost memoryLimit operationLimit
      opRisk write).features
        (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).labels
        (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).state <
      batchCEObjective S.features S.labels S.state := by
  have hstrict := batchSampleCE_boundedGrowStep_lt_of_legal S Z D trainingCost
    memoryLimit operationLimit opRisk write h
  obtain ⟨b0⟩ := h.2.2.2.2.1
  have hsum :
      (∑ b, batchSampleCE (boundedGrowStep S Z D trainingCost memoryLimit operationLimit
        opRisk write).features
          (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).labels b
          (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).state) <
        ∑ b, batchSampleCE S.features S.labels b S.state := by
    apply Finset.sum_lt_sum
    · intro b _hb
      exact (hstrict b).le
    · exact ⟨b0, Finset.mem_univ b0, hstrict b0⟩
  have hBnat : 0 < B := by
    simpa only [Fintype.card_fin] using Fintype.card_pos_iff.mpr ⟨b0⟩
  have hB : 0 < (B : ℝ) := by exact_mod_cast hBnat
  exact div_lt_div_of_pos_right hsum hB

/-- Empirical batch CE is nonincreasing including all rejected branches and B=0. -/
theorem batchCEObjective_boundedGrowStep_le :
    batchCEObjective (boundedGrowStep S Z D trainingCost memoryLimit operationLimit
      opRisk write).features
        (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).labels
        (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).state ≤
      batchCEObjective S.features S.labels S.state := by
  by_cases h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit
  · exact (batchCEObjective_boundedGrowStep_lt_of_legal S Z D trainingCost memoryLimit
      operationLimit opRisk write h).le
  · rw [boundedGrowStep_of_not_legal S Z D trainingCost memoryLimit operationLimit
      opRisk write h]

/-- Accepted guard work charges exact declared operation units to real flops. -/
theorem boundedGrowStep_flops_of_legal
    (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit) :
    (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).state.res.flops =
      S.state.res.flops + (growthOperations B V trainingCost : ℝ) := by
  rw [boundedGrowStep_of_legal S Z D trainingCost memoryLimit operationLimit opRisk write h]
  simpa only [grownBatchState, growthOperations, Nat.cast_add] using
    expandedHalfTrainStep_flops_of_active S.features S.labels Z D S.state
      (trainingCost : ℝ) opRisk write (growthLegal_expandedCost h) h.2.2.2.2

/-- Accepted guard work subtracts exact declared operation units from real budget. -/
theorem boundedGrowStep_budget_of_legal
    (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit) :
    (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).state.res.budget =
      S.state.res.budget - (growthOperations B V trainingCost : ℝ) := by
  have hcost := growthLegal_expandedCost h
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + (trainingCost : ℝ) ≤
      (expandedTrainState S.state).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have hactive := batchDirectionHalfTrainStep_of_active
    (fun b => expandedFeatures (S.features b) (Z b)) S.labels (fun _ => D)
    (expandedTrainState S.state) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write ⟨add_nonneg (by positivity) hcost.1, hbudget⟩ h.2.2.2.2
  rw [boundedGrowStep_of_legal S Z D trainingCost memoryLimit operationLimit opRisk write h]
  change (expandedHalfTrainStep S.features S.labels Z D S.state
    (trainingCost : ℝ) opRisk write).res.budget =
      S.state.res.budget - (growthOperations B V trainingCost : ℝ)
  unfold expandedHalfTrainStep
  rw [hactive, trainStep_budget]
  simp only [batchDirectionHalfTrainInput, expandedTrainState,
    growthOperations, Nat.cast_add]

/-- Legal bounded growth leaves nonnegative remaining real compute budget. -/
theorem boundedGrowStep_budget_nonneg_of_legal
    (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit) :
    0 ≤ (boundedGrowStep S Z D trainingCost memoryLimit operationLimit
      opRisk write).state.res.budget := by
  rw [boundedGrowStep_budget_of_legal S Z D trainingCost memoryLimit operationLimit
    opRisk write h]
  have hb := h.2.2.2.1
  linarith

end Hagi.Contracts.BatchCEGrowth
