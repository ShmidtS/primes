/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.BatchCEBudgetGuard
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Unified.ParetoExecution
import Natural

set_option linter.style.header false

/-!
# Function-preserving batch CE growth with exact capacity counters

Canon (C524, v5 W2): also hosts the merged sections (namespaces and
FQNs preserved, module files removed):
`Hagi.Contracts.BatchCEGrowthSelection` (growth candidate selection,
admission-yield, finite open-loop) and `Hagi.Contracts.NaturalLean`
(interop check of the pinned Natural tactics with growth proofs).
-/
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
open Hagi.Model.CEExpansion Hagi.State Hagi.Model

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

open Filter Topology

/-- Every bounded transition either preserves width or adds exactly one. -/
theorem boundedGrowStep_width_eq_or
    (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).width =
        S.width ∨
      (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).width =
        S.width + 1 := by
  by_cases h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit
  · right
    rw [boundedGrowStep_of_legal S Z D trainingCost memoryLimit operationLimit
      opRisk write h]
    rfl
  · left
    rw [boundedGrowStep_of_not_legal S Z D trainingCost memoryLimit operationLimit
      opRisk write h]

/-- Width is nondecreasing across either admission outcome. -/
theorem boundedGrowStep_width_mono
    (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    S.width ≤
      (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).width := by
  rcases boundedGrowStep_width_eq_or S Z D trainingCost memoryLimit operationLimit
    opRisk write with h | h
  · rw [h]
  · rw [h]
    omega

/-- A legal batch and its labels force a positive declared operation increment. -/
theorem growthOperations_pos_of_legal
    (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ)
    (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit) :
    0 < growthOperations B V trainingCost := by
  obtain ⟨b0⟩ := h.2.2.2.2.1
  have hB : 0 < B := by
    simpa only [Fintype.card_fin] using Fintype.card_pos_iff.mpr ⟨b0⟩
  have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨S.labels b0⟩
  unfold growthOperations expandedFeatureEvaluationCount
  exact Nat.add_pos_left (Nat.mul_pos hB hV) trainingCost

/-- Exact one-width increment is equivalent to the complete admission gate. -/
theorem boundedGrowStep_legal_iff_width_succ
    (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    GrowthLegal V S Z D trainingCost memoryLimit operationLimit ↔
      (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write).width =
        S.width + 1 := by
  constructor
  · intro h
    rw [boundedGrowStep_of_legal S Z D trainingCost memoryLimit operationLimit
      opRisk write h]
    rfl
  · intro hwidth
    by_cases h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit
    · exact h
    · rw [boundedGrowStep_of_not_legal S Z D trainingCost memoryLimit operationLimit
        opRisk write h] at hwidth
      omega

/-- Every transition preserves budget plus accumulated declared operations. -/
theorem boundedGrowStep_budget_add_flops
    (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk
      write).state.res.budget +
        (boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk
          write).state.res.flops =
      S.state.res.budget + S.state.res.flops := by
  by_cases h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit
  · rw [boundedGrowStep_budget_of_legal S Z D trainingCost memoryLimit operationLimit
      opRisk write h, boundedGrowStep_flops_of_legal S Z D trainingCost memoryLimit
      operationLimit opRisk write h]
    ring
  · rw [boundedGrowStep_of_not_legal S Z D trainingCost memoryLimit operationLimit
      opRisk write h]

/-- Number of indices strictly before `T` at which a width sequence increases by one. -/
def widthIncrementCount (width : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | T + 1 => widthIncrementCount width T +
      if width (T + 1) = width T + 1 then 1 else 0

@[simp] theorem widthIncrementCount_zero (width : ℕ → ℕ) :
    widthIncrementCount width 0 = 0 := rfl

@[simp] theorem widthIncrementCount_succ (width : ℕ → ℕ) (T : ℕ) :
    widthIncrementCount width (T + 1) = widthIncrementCount width T +
      if width (T + 1) = width T + 1 then 1 else 0 := rfl

private theorem widthIncrementCount_add_initial_of_step
    (width : ℕ → ℕ)
    (hstep : ∀ t, width (t + 1) = width t ∨ width (t + 1) = width t + 1)
    (T : ℕ) :
    widthIncrementCount width T + width 0 = width T := by
  induction T with
  | zero => simp
  | succ T ih =>
      by_cases hinc : width (T + 1) = width T + 1
      · simp only [widthIncrementCount_succ, hinc, ite_true]
        omega
      · have hsame : width (T + 1) = width T := (hstep T).resolve_right hinc
        simp only [widthIncrementCount_succ, hinc, ite_false]
        omega

/-- Empirical mean CE of a width-carrying state on its own batch. -/
noncomputable def growthObjective (S : BoundedBatchState V B a r c k capacity) : ℝ :=
  batchCEObjective S.features S.labels S.state

/-- Totalized batch CE is nonnegative, including an empty batch. -/
theorem growthObjective_nonneg (S : BoundedBatchState V B a r c k capacity) :
    0 ≤ growthObjective S :=
  batchCEObjective_nonneg S.features S.labels S.state

/-- Target-minus-softmax residual features supplied at the actual current state. -/
noncomputable def residualFeatures {V : Type} [Fintype V]
    {B a r c k capacity : ℕ}
    (S : BoundedBatchState V B a r c k capacity) : Fin B → V → ℝ :=
  fun b v => -(ceResidual (S.features b) (coreParameters S.state) (S.labels b) v)

/-- The unit direction varying only the newly appended readout coefficient. -/
noncomputable def residualDirection {V : Type} [Fintype V]
    {B a r c k capacity : ℕ}
    (S : BoundedBatchState V B a r c k capacity) :
    EuclideanSpace ℝ (Fin (S.width + 1)) :=
  expandedParameters (0 : EuclideanSpace ℝ (Fin S.width)) 1

/-- The current residual direction has exact per-sample squared action. -/
theorem dirAction_residual_expandedParameters_zero_one
    {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (Z : V → ℝ) (t : V)
    (hZ : ∀ v, Z v = -(ceResidual X θ t v)) :
    dirAction (expandedFeatures X Z) (expandedParameters θ 0) t
        (expandedParameters (0 : EuclideanSpace ℝ (Fin d)) 1) =
      -∑ v, (ceResidual X θ t v) ^ 2 := by
  have hzero : ceLogits (expandedFeatures X Z) (expandedParameters θ 0) =
      ceLogits X θ := by
    funext v
    simpa using ceLogits_expandedParameters X θ Z 0 v
  have hres : ceResidual (expandedFeatures X Z) (expandedParameters θ 0) t =
      ceResidual X θ t := by
    unfold ceResidual
    rw [hzero]
  have hdir (v : V) : ceLogits (expandedFeatures X Z)
      (expandedParameters (0 : EuclideanSpace ℝ (Fin d)) 1) v = Z v := by
    simpa [ceLogits, Matrix.mulVec, dotProduct] using
      ceLogits_expandedParameters X (0 : EuclideanSpace ℝ (Fin d)) Z 1 v
  unfold dirAction
  rw [hres]
  calc
    (∑ v, ceResidual X θ t v * ceLogits (expandedFeatures X Z)
        (expandedParameters (0 : EuclideanSpace ℝ (Fin d)) 1) v) =
        ∑ v, ceResidual X θ t v * Z v := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hdir]
    _ = -∑ v, (ceResidual X θ t v) ^ 2 := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hZ]
      ring

/-- A vocabulary with at least two classes gives positive residual energy. -/
theorem residualEnergy_pos {V : Type} [Fintype V] [Nonempty V]
    [Fact (1 < Fintype.card V)] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    0 < ∑ v, (ceResidual X θ t v) ^ 2 := by
  let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp Fact.out
  obtain ⟨v, hvt⟩ := exists_ne t
  have hp : 0 < ceResidual X θ t v := by
    simpa [ceResidual, hvt] using Hagi.Prelude.softDef_pos (ceLogits X θ) v
  exact Finset.sum_pos' (fun w _hw => sq_nonneg (ceResidual X θ t w))
    ⟨v, Finset.mem_univ v, sq_pos_of_pos hp⟩

/-- Explicit resource premises make the residual policy legal at this state. -/
theorem residualGrowthLegal {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} [Nonempty V]
    [Nonempty (Fin B)] [Fact (1 < Fintype.card V)]
    (S : BoundedBatchState V B a r c k capacity)
    (trainingCost memoryLimit operationLimit : ℕ)
    (hcap : S.width + 1 ≤ capacity)
    (hmem : growthMemoryIncrement B V ≤ memoryLimit)
    (hops : growthOperations B V trainingCost ≤ operationLimit)
    (hbudget : (growthOperations B V trainingCost : ℝ) ≤ S.state.res.budget) :
    GrowthLegal V S (residualFeatures S) (residualDirection S)
      trainingCost memoryLimit operationLimit := by
  refine ⟨hcap, hmem, hops, hbudget, inferInstance, ?_⟩
  intro b
  have haction := dirAction_residual_expandedParameters_zero_one
    (X := S.features b) (θ := coreParameters S.state)
    (Z := residualFeatures S b) (t := S.labels b)
    (fun v => rfl)
  rw [coreParameters_expandedTrainState, residualDirection, haction]
  exact neg_lt_zero.mpr (residualEnergy_pos (S.features b) (coreParameters S.state)
    (S.labels b))

/-- An admitted residual step actually learns a positive new readout weight. -/
theorem coreParameters_residualGrowth_last_pos {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} [Nonempty V] [Nonempty (Fin B)]
    [Fact (1 < Fintype.card V)]
    (S : BoundedBatchState V B a r c k capacity)
    (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (h : GrowthLegal V S (residualFeatures S) (residualDirection S)
      trainingCost memoryLimit operationLimit) :
    0 < (coreParameters (grownBatchState S (residualFeatures S)
      (residualDirection S) trainingCost memoryLimit operationLimit opRisk write h).state).ofLp
        (Fin.last S.width) := by
  have hcost : 0 ≤ (trainingCost : ℝ) ∧
      (expandedFeatureEvaluationCount B V : ℝ) + (trainingCost : ℝ) ≤
        S.state.res.budget := by
    refine ⟨by positivity, ?_⟩
    simpa only [growthOperations, Nat.cast_add] using h.2.2.2.1
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤
      (expandedTrainState S.state).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have hlast := coreParameters_expandedHalfTrainStep_last S.features S.labels
    (residualFeatures S) (residualDirection S) S.state (trainingCost : ℝ) opRisk write
    hcost h.2.2.2.2
  have heta := (batchDirectionHalfEta_pos_iff
    (fun b => expandedFeatures (S.features b) (residualFeatures S b))
    (coreParameters (expandedTrainState S.state)) S.labels (residualDirection S)).2
    h.2.2.2.2
  change 0 < (coreParameters (expandedHalfTrainStep S.features S.labels
    (residualFeatures S) (residualDirection S) S.state (trainingCost : ℝ) opRisk write)).ofLp
      (Fin.last S.width)
  rw [hlast]
  simpa [residualDirection, expandedParameters] using heta

section GrowthTrajectory

variable (S0 : BoundedBatchState V B a r c k capacity)
variable (Zs : ℕ → Fin B → V → ℝ)
variable (Ds : (t : ℕ) → (S : BoundedBatchState V B a r c k capacity) →
  EuclideanSpace ℝ (Fin (S.width + 1)))
variable (costs memoryCaps operationCaps : ℕ → ℕ)
variable (risks : ℕ → ℝ) (writes : ℕ → Option (Σ _ : ℕ, Fin c → ℝ))

/-- Repeated actual bounded growth with features and directions at the current width. -/
noncomputable def growthPath
    (S0 : BoundedBatchState V B a r c k capacity)
    (Zs : ℕ → Fin B → V → ℝ)
    (Ds : (t : ℕ) → (S : BoundedBatchState V B a r c k capacity) →
      EuclideanSpace ℝ (Fin (S.width + 1)))
    (costs memoryCaps operationCaps : ℕ → ℕ)
    (risks : ℕ → ℝ) (writes : ℕ → Option (Σ _ : ℕ, Fin c → ℝ)) :
    ℕ → BoundedBatchState V B a r c k capacity
  | 0 => S0
  | t + 1 => boundedGrowStep (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t)
      (Zs t) (Ds t (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t))
      (costs t) (memoryCaps t) (operationCaps t) (risks t) (writes t)

@[simp] theorem growthPath_zero :
    growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes 0 = S0 := rfl

@[simp] theorem growthPath_succ (t : ℕ) :
    growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes (t + 1) =
      boundedGrowStep (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t)
        (Zs t) (Ds t (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t))
        (costs t) (memoryCaps t) (operationCaps t) (risks t) (writes t) := rfl

/-- One recursive step cannot reduce width. -/
theorem growthPath_width_step (t : ℕ) :
    (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width ≤
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes (t + 1)).width := by
  rw [growthPath_succ]
  exact boundedGrowStep_width_mono
    (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t)
    (Zs t) (Ds t (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t))
    (costs t) (memoryCaps t) (operationCaps t) (risks t) (writes t)

/-- Width is monotone along the actual trajectory. -/
theorem growthPath_width_mono :
    Monotone (fun t =>
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width) :=
  monotone_nat_of_le_succ
    (growthPath_width_step S0 Zs Ds costs memoryCaps operationCaps risks writes)

/-- Every trajectory state carries the original capacity bound. -/
theorem growthPath_width_le_capacity (t : ℕ) :
    (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width ≤ capacity :=
  (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width_le_capacity

/-- Bounded monotone natural width eventually attains a fixed finite value. -/
theorem growthPath_width_eventually_constant :
    ∃ width N, ∀ t ≥ N,
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width = width :=
  converges_of_monotone_of_bounded
    (growthPath_width_mono S0 Zs Ds costs memoryCaps operationCaps risks writes)
    (growthPath_width_le_capacity S0 Zs Ds costs memoryCaps operationCaps risks writes)

/-- Once width is constant, every later complete record is literally unchanged.
The terminal width need not equal capacity. -/
theorem growthPath_eventually_constant :
    ∃ N, ∀ t ≥ N, growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t =
      growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes N := by
  obtain ⟨width, N, hwidth⟩ := growthPath_width_eventually_constant
    S0 Zs Ds costs memoryCaps operationCaps risks writes
  refine ⟨N, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      have hnwidth :
          (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes (n + 1)).width =
            (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes n).width := by
        rw [hwidth (n + 1) (by omega), hwidth n hn]
      have hnlegal : ¬GrowthLegal V
          (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes n) (Zs n)
          (Ds n (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes n))
          (costs n) (memoryCaps n) (operationCaps n) := by
        intro hlegal
        have hinc := (boundedGrowStep_legal_iff_width_succ
          (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes n)
          (Zs n) (Ds n (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes n))
          (costs n) (memoryCaps n) (operationCaps n) (risks n) (writes n)).mp hlegal
        rw [← growthPath_succ S0 Zs Ds costs memoryCaps operationCaps risks writes n] at hinc
        omega
      calc
        growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes (n + 1) =
            growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes n := by
          rw [growthPath_succ S0 Zs Ds costs memoryCaps operationCaps risks writes n,
            boundedGrowStep_of_not_legal
              (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes n)
              (Zs n) (Ds n (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes n))
              (costs n) (memoryCaps n) (operationCaps n) (risks n) (writes n) hnlegal]
        _ = growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes N := ih

/-- Actual batch CE does not increase at any recursive step. -/
theorem growthPath_objective_step (t : ℕ) :
    growthObjective (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes (t + 1)) ≤
      growthObjective (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t) := by
  rw [growthPath_succ]
  exact batchCEObjective_boundedGrowStep_le
    (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t)
    (Zs t) (Ds t (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t))
    (costs t) (memoryCaps t) (operationCaps t) (risks t) (writes t)

/-- Actual empirical batch CE is antitone, including every rejected call. -/
theorem growthPath_objective_antitone :
    Antitone (fun t =>
      growthObjective (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t)) :=
  antitone_nat_of_succ_le
    (growthPath_objective_step S0 Zs Ds costs memoryCaps operationCaps risks writes)

/-- The actual supplied-batch CE converges to its own historical infimum. -/
theorem growthPath_objective_tendsto_ciInf : Tendsto (fun t =>
      growthObjective (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t)) atTop
    (𝓝 (⨅ t, growthObjective
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t))) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (growthPath_objective_antitone S0 Zs Ds costs memoryCaps operationCaps risks writes)
    (fun t => growthObjective_nonneg
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t))

/-- Once whole states are constant, the actual batch objective is constant too. -/
theorem growthPath_objective_eventually_constant :
    ∃ N, ∀ t ≥ N,
      growthObjective (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t) =
        growthObjective (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes N) := by
  obtain ⟨N, hN⟩ := growthPath_eventually_constant
    S0 Zs Ds costs memoryCaps operationCaps risks writes
  exact ⟨N, fun t ht => by rw [hN t ht]⟩

/-- A late attained state realizes exactly the infimum of this trajectory's CE.
This is not a minimum over other architectures, inputs or held-out distributions. -/
theorem growthPath_objective_ciInf_attainment : ∃ N,
    growthObjective (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes N) =
      ⨅ t, growthObjective (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t) := by
  obtain ⟨N, hN⟩ := growthPath_eventually_constant
    S0 Zs Ds costs memoryCaps operationCaps risks writes
  have hanti := growthPath_objective_antitone
    S0 Zs Ds costs memoryCaps operationCaps risks writes
  refine ⟨N, le_antisymm (le_ciInf ?_) (ciInf_le ?_ N)⟩
  · intro t
    by_cases hNt : N ≤ t
    · rw [hN t hNt]
    · exact hanti (Nat.le_of_lt (Nat.lt_of_not_ge hNt))
  · exact ⟨0, by
      intro x hx
      obtain ⟨t, rfl⟩ := hx
      exact growthObjective_nonneg
        (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t)⟩

/-- The number of one-width increments plus initial width is the actual width.
By `boundedGrowStep_legal_iff_width_succ`, these increments are exactly accepted calls. -/
theorem growthPath_widthIncrementCount_add_initial (T : ℕ) :
    widthIncrementCount (fun t =>
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width) T + S0.width =
        (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T).width := by
  apply widthIncrementCount_add_initial_of_step
  intro t
  rw [growthPath_succ]
  exact boundedGrowStep_width_eq_or
    (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t)
    (Zs t) (Ds t (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t))
    (costs t) (memoryCaps t) (operationCaps t) (risks t) (writes t)

/-- At most the initial remaining capacity of accepted growth calls can occur. -/
theorem growthPath_widthIncrementCount_le_remaining_capacity (T : ℕ) :
    widthIncrementCount (fun t =>
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width) T ≤
        capacity - S0.width := by
  have htelescope := growthPath_widthIncrementCount_add_initial
    S0 Zs Ds costs memoryCaps operationCaps risks writes T
  have hcap := growthPath_width_le_capacity
    S0 Zs Ds costs memoryCaps operationCaps risks writes T
  omega

/-- New parameter/moment cells counted by accepted increments add to the initial cells. -/
theorem growthPath_model_cells_add_initial (T : ℕ) :
    expandedStateCoefficients * widthIncrementCount (fun t =>
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width) T +
        expandedStateCoefficients * S0.width =
      expandedStateCoefficients *
        (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T).width := by
  calc
    expandedStateCoefficients * widthIncrementCount (fun t =>
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width) T +
        expandedStateCoefficients * S0.width =
        expandedStateCoefficients * (widthIncrementCount (fun t =>
          (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width) T +
          S0.width) := (Nat.mul_add _ _ _).symm
    _ = expandedStateCoefficients *
        (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T).width :=
      congrArg (fun width => expandedStateCoefficients * width)
        (growthPath_widthIncrementCount_add_initial
          S0 Zs Ds costs memoryCaps operationCaps risks writes T)

/-- Persistent model/moment cells are bounded by the capacity-scaled coefficient count. -/
theorem growthPath_model_cells_le_capacity (T : ℕ) :
    expandedStateCoefficients *
        (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T).width ≤
      expandedStateCoefficients * capacity :=
  Nat.mul_le_mul_left expandedStateCoefficients
    (growthPath_width_le_capacity S0 Zs Ds costs memoryCaps operationCaps risks writes T)

/-- Retained feature payload is monotone in the current width. -/
theorem growthPath_featurePayloadCells_mono :
    Monotone (fun t => featurePayloadCells B V
      (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes t).width) := by
  intro t u htu
  exact Nat.mul_le_mul_left (expandedFeatureEvaluationCount B V)
    (growthPath_width_mono S0 Zs Ds costs memoryCaps operationCaps risks writes htu)

/-- Retained feature payload stays within the capacity-scaled logical cell bound. -/
theorem growthPath_featurePayloadCells_le_capacity (T : ℕ) :
    featurePayloadCells B V
        (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T).width ≤
      featurePayloadCells B V capacity :=
  Nat.mul_le_mul_left (expandedFeatureEvaluationCount B V)
    (growthPath_width_le_capacity S0 Zs Ds costs memoryCaps operationCaps risks writes T)

/-- Budget plus accumulated declared operations is an exact trajectory invariant. -/
theorem growthPath_budget_add_flops (T : ℕ) :
    (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T).state.res.budget +
        (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T).state.res.flops =
      S0.state.res.budget + S0.state.res.flops := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [growthPath_succ S0 Zs Ds costs memoryCaps operationCaps risks writes T,
        boundedGrowStep_budget_add_flops
          (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T)
          (Zs T) (Ds T (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T))
          (costs T) (memoryCaps T) (operationCaps T) (risks T) (writes T)]
      exact ih

/-- A nonnegative initial budget remains nonnegative along every legal/rejected path. -/
theorem growthPath_budget_nonneg (hinitial : 0 ≤ S0.state.res.budget) (T : ℕ) :
    0 ≤ (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T).state.res.budget := by
  induction T with
  | zero => exact hinitial
  | succ T ih =>
      rw [growthPath_succ S0 Zs Ds costs memoryCaps operationCaps risks writes T]
      by_cases hlegal : GrowthLegal V
          (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T) (Zs T)
          (Ds T (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T))
          (costs T) (memoryCaps T) (operationCaps T)
      · exact boundedGrowStep_budget_nonneg_of_legal
          (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T)
          (Zs T) (Ds T (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T))
          (costs T) (memoryCaps T) (operationCaps T) (risks T) (writes T) hlegal
      · rw [boundedGrowStep_of_not_legal
          (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T)
          (Zs T) (Ds T (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T))
          (costs T) (memoryCaps T) (operationCaps T) (risks T) (writes T) hlegal]
        exact ih

/-- Initial budget bounds cumulative declared operations beyond the initial accumulator. -/
theorem growthPath_flops_le_initial_budget_add_flops
    (hinitial : 0 ≤ S0.state.res.budget) (T : ℕ) :
    (growthPath S0 Zs Ds costs memoryCaps operationCaps risks writes T).state.res.flops ≤
      S0.state.res.budget + S0.state.res.flops := by
  have hbudget := growthPath_budget_nonneg
    S0 Zs Ds costs memoryCaps operationCaps risks writes hinitial T
  have hinvariant := growthPath_budget_add_flops
    S0 Zs Ds costs memoryCaps operationCaps risks writes T
  linarith

end GrowthTrajectory

section ResidualTrajectory

/-- The residual policy evaluated from the completed current state, rather
than from an externally fixed feature sequence. -/
noncomputable def residualPath {V : Type} [Fintype V]
    {B a r c k capacity : ℕ}
    (S0 : BoundedBatchState V B a r c k capacity)
    (costs memoryCaps operationCaps : ℕ → ℕ)
    (risks : ℕ → ℝ) (writes : ℕ → Option (Σ _ : ℕ, Fin c → ℝ)) :
    ℕ → BoundedBatchState V B a r c k capacity
  | 0 => S0
  | t + 1 =>
    let S := residualPath S0 costs memoryCaps operationCaps risks writes t
    boundedGrowStep S (residualFeatures S) (residualDirection S)
      (costs t) (memoryCaps t) (operationCaps t) (risks t) (writes t)

/-- The state-derived residual policy is an exact specialization of the
existing generic bounded growth trajectory. -/
theorem residualPath_eq_growthPath {V : Type} [Fintype V]
    {B a r c k capacity : ℕ}
    (S0 : BoundedBatchState V B a r c k capacity)
    (costs memoryCaps operationCaps : ℕ → ℕ)
    (risks : ℕ → ℝ) (writes : ℕ → Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    residualPath S0 costs memoryCaps operationCaps risks writes t =
      growthPath S0
        (fun u => residualFeatures (residualPath S0 costs memoryCaps operationCaps risks writes u))
        (fun _ S => residualDirection S) costs memoryCaps operationCaps risks writes t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [residualPath, growthPath_succ]
    rw [ih]

/-- Current resources admit the residual update at every supplied path time. -/
theorem residualPath_growthLegal {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} [Nonempty V]
    [Nonempty (Fin B)] [Fact (1 < Fintype.card V)]
    (S0 : BoundedBatchState V B a r c k capacity)
    (costs memoryCaps operationCaps : ℕ → ℕ)
    (risks : ℕ → ℝ) (writes : ℕ → Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ)
    (hcap : (residualPath S0 costs memoryCaps operationCaps risks writes t).width + 1 ≤ capacity)
    (hmem : growthMemoryIncrement B V ≤ memoryCaps t)
    (hops : growthOperations B V (costs t) ≤ operationCaps t)
    (hbudget : (growthOperations B V (costs t) : ℝ) ≤
      (residualPath S0 costs memoryCaps operationCaps risks writes t).state.res.budget) :
    GrowthLegal V (residualPath S0 costs memoryCaps operationCaps risks writes t)
      (residualFeatures (residualPath S0 costs memoryCaps operationCaps risks writes t))
      (residualDirection (residualPath S0 costs memoryCaps operationCaps risks writes t))
      (costs t) (memoryCaps t) (operationCaps t) :=
  residualGrowthLegal (residualPath S0 costs memoryCaps operationCaps risks writes t)
    (costs t) (memoryCaps t) (operationCaps t) hcap hmem hops hbudget

/-- The actual supplied-batch objective remains antitone on this trajectory. -/
theorem residualPath_objective_antitone {V : Type} [Fintype V]
    {B a r c k capacity : ℕ}
    (S0 : BoundedBatchState V B a r c k capacity)
    (costs memoryCaps operationCaps : ℕ → ℕ)
    (risks : ℕ → ℝ) (writes : ℕ → Option (Σ _ : ℕ, Fin c → ℝ)) :
    Antitone (fun t => growthObjective
      (residualPath S0 costs memoryCaps operationCaps risks writes t)) := by
  have hanti := growthPath_objective_antitone S0
    (fun u => residualFeatures (residualPath S0 costs memoryCaps operationCaps risks writes u))
    (fun _ S => residualDirection S) costs memoryCaps operationCaps risks writes
  intro t u htu
  change growthObjective (residualPath S0 costs memoryCaps operationCaps risks writes u) ≤
    growthObjective (residualPath S0 costs memoryCaps operationCaps risks writes t)
  rw [residualPath_eq_growthPath S0 costs memoryCaps operationCaps risks writes t,
    residualPath_eq_growthPath S0 costs memoryCaps operationCaps risks writes u]
  exact hanti htu

/-- The finite bounded trajectory literally stabilizes as a whole state. -/
theorem residualPath_eventually_constant {V : Type} [Fintype V]
    {B a r c k capacity : ℕ}
    (S0 : BoundedBatchState V B a r c k capacity)
    (costs memoryCaps operationCaps : ℕ → ℕ)
    (risks : ℕ → ℝ) (writes : ℕ → Option (Σ _ : ℕ, Fin c → ℝ)) :
    ∃ N, ∀ t ≥ N, residualPath S0 costs memoryCaps operationCaps risks writes t =
      residualPath S0 costs memoryCaps operationCaps risks writes N := by
  obtain ⟨N, hN⟩ := growthPath_eventually_constant S0
    (fun u => residualFeatures (residualPath S0 costs memoryCaps operationCaps risks writes u))
    (fun _ S => residualDirection S) costs memoryCaps operationCaps risks writes
  refine ⟨N, ?_⟩
  intro t ht
  rw [residualPath_eq_growthPath S0 costs memoryCaps operationCaps risks writes t,
    residualPath_eq_growthPath S0 costs memoryCaps operationCaps risks writes N]
  exact hN t ht

/-- Nonnegative initial real budget is preserved by all admitted/rejected steps. -/
theorem residualPath_budget_nonneg {V : Type} [Fintype V]
    {B a r c k capacity : ℕ}
    (S0 : BoundedBatchState V B a r c k capacity)
    (costs memoryCaps operationCaps : ℕ → ℕ)
    (risks : ℕ → ℝ) (writes : ℕ → Option (Σ _ : ℕ, Fin c → ℝ))
    (hinitial : 0 ≤ S0.state.res.budget) (t : ℕ) :
    0 ≤ (residualPath S0 costs memoryCaps operationCaps risks writes t).state.res.budget := by
  rw [residualPath_eq_growthPath S0 costs memoryCaps operationCaps risks writes t]
  exact growthPath_budget_nonneg S0
    (fun u => residualFeatures (residualPath S0 costs memoryCaps operationCaps risks writes u))
    (fun _ S => residualDirection S) costs memoryCaps operationCaps risks writes hinitial t

end ResidualTrajectory

section ProofTier

/-- Evidence levels for one actual bounded-growth admission policy. -/
inductive GrowthAdmission (V : Type) [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ) where
  | fullyVerified (h : GrowthLegal V S Z D trainingCost memoryLimit operationLimit)
  | conditional (debt : Prop)
      (close : debt → GrowthLegal V S Z D trainingCost memoryLimit operationLimit)
  | empiricalOnly (testRuns : ℕ)
  | budgetViolation (h : S.state.res.budget < 0)
  | unknown

/-- Only discharged conditional evidence may become a proof of legality. -/
def GrowthAdmission.debt {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} {S : BoundedBatchState V B a r c k capacity}
    {Z : Fin B → V → ℝ} {D : EuclideanSpace ℝ (Fin (S.width + 1))}
    {trainingCost memoryLimit operationLimit : ℕ}
    (a : GrowthAdmission V S Z D trainingCost memoryLimit operationLimit) : Prop :=
  match a with
  | .fullyVerified _ => True
  | .conditional H _ => H
  | .empiricalOnly _ => False
  | .budgetViolation _ => False
  | .unknown => False

/-- Explicitly discharged debt yields exactly the existing admission proof. -/
theorem GrowthAdmission.proof {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} {S : BoundedBatchState V B a r c k capacity}
    {Z : Fin B → V → ℝ} {D : EuclideanSpace ℝ (Fin (S.width + 1))}
    {trainingCost memoryLimit operationLimit : ℕ}
    (a : GrowthAdmission V S Z D trainingCost memoryLimit operationLimit)
    (h : a.debt) : GrowthLegal V S Z D trainingCost memoryLimit operationLimit := by
  cases a with
  | fullyVerified hLegal => exact hLegal
  | conditional _ close => exact close h
  | empiricalOnly _ => exact False.elim h
  | budgetViolation _ => exact False.elim h
  | unknown => exact False.elim h

/-- Promotion is available only from actual discharged proof debt. -/
def GrowthAdmission.promote {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} {S : BoundedBatchState V B a r c k capacity}
    {Z : Fin B → V → ℝ} {D : EuclideanSpace ℝ (Fin (S.width + 1))}
    {trainingCost memoryLimit operationLimit : ℕ}
    (a : GrowthAdmission V S Z D trainingCost memoryLimit operationLimit)
    (h : a.debt) : GrowthAdmission V S Z D trainingCost memoryLimit operationLimit :=
  .fullyVerified (a.proof h)

/-- Negative current real budget contradicts the existing resource premise. -/
theorem not_growthLegal_of_negative_budget {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} {S : BoundedBatchState V B a r c k capacity}
    {Z : Fin B → V → ℝ} {D : EuclideanSpace ℝ (Fin (S.width + 1))}
    {trainingCost memoryLimit operationLimit : ℕ}
    (hneg : S.state.res.budget < 0) :
    ¬ GrowthLegal V S Z D trainingCost memoryLimit operationLimit := by
  intro hlegal
  have hbudget := hlegal.2.2.2.1
  have hnonneg : (0 : ℝ) ≤
      ((growthOperations B V trainingCost : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- Only fully verified evidence reaches the actual bounded-growth executor. -/
noncomputable def quarantinedGrowStep {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ)
    (admission : GrowthAdmission V S Z D trainingCost memoryLimit operationLimit)
    (opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    BoundedBatchState V B a r c k capacity :=
  match admission with
  | .fullyVerified _ => boundedGrowStep S Z D trainingCost memoryLimit operationLimit
      opRisk write
  | .conditional _ _ => S
  | .empiricalOnly _ => S
  | .budgetViolation _ => S
  | .unknown => S

/-- Explicit promotion delegates to the original bounded transition. -/
theorem quarantinedGrowStep_of_promote {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ)
    (a : GrowthAdmission V S Z D trainingCost memoryLimit operationLimit)
    (h : a.debt) (opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    quarantinedGrowStep S Z D trainingCost memoryLimit operationLimit
        (a.promote h) opRisk write =
      boundedGrowStep S Z D trainingCost memoryLimit operationLimit opRisk write := by
  cases a with
  | fullyVerified _ => rfl
  | conditional _ _ => rfl
  | empiricalOnly _ => exact False.elim h
  | budgetViolation _ => exact False.elim h
  | unknown => exact False.elim h

/-- Any un-promoted constructor retains the complete old batch state. -/
theorem quarantinedGrowStep_of_not_fullyVerified {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ)
    (a : GrowthAdmission V S Z D trainingCost memoryLimit operationLimit)
    (h : ∀ legal, a ≠ .fullyVerified legal) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    quarantinedGrowStep S Z D trainingCost memoryLimit operationLimit a opRisk write = S := by
  cases a with
  | fullyVerified hLegal => exact False.elim (h hLegal rfl)
  | conditional _ _ => rfl
  | empiricalOnly _ => rfl
  | budgetViolation _ => rfl
  | unknown => rfl

/-- After actual debt discharge, the promoted call strictly lowers supplied-batch CE. -/
theorem growthObjective_quarantinedGrowStep_lt_of_promote {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ)
    (a : GrowthAdmission V S Z D trainingCost memoryLimit operationLimit)
    (h : a.debt) (opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    growthObjective (quarantinedGrowStep S Z D trainingCost memoryLimit operationLimit
      (a.promote h) opRisk write) < growthObjective S := by
  rw [quarantinedGrowStep_of_promote S Z D trainingCost memoryLimit operationLimit
    a h opRisk write]
  exact batchCEObjective_boundedGrowStep_lt_of_legal S Z D trainingCost memoryLimit
    operationLimit opRisk write (a.proof h)

end ProofTier

section ResidualAdmissionMargin

/-- The existing worst-sample quadratic residual at the actual common eta. -/
noncomputable def residualStepMargin {V : Type} [Fintype V]
    {B a r c k capacity : ℕ}
    (S : BoundedBatchState V B a r c k capacity) : ℝ := by
  classical
  exact if hB : Nonempty (Fin B) then
    let _ : Nonempty (Fin B) := hB
    batchDirectionMinQuadraticMargin
      (fun b => expandedFeatures (S.features b) (residualFeatures S b))
      (coreParameters (expandedTrainState S.state)) S.labels (residualDirection S)
      (batchDirectionHalfEta
        (fun b => expandedFeatures (S.features b) (residualFeatures S b))
        (coreParameters (expandedTrainState S.state)) S.labels (residualDirection S))
  else 0

/-- The pure residual margin exactly when the complete admission gate holds. -/
noncomputable def residualAdmissionMargin {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (trainingCost memoryLimit operationLimit : ℕ) : ℝ := by
  classical
  exact if h : GrowthLegal V S (residualFeatures S) (residualDirection S)
      trainingCost memoryLimit operationLimit then residualStepMargin S else 0

theorem residualAdmissionMargin_pos_of_legal {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (trainingCost memoryLimit operationLimit : ℕ)
    (h : GrowthLegal V S (residualFeatures S) (residualDirection S)
      trainingCost memoryLimit operationLimit) :
    0 < residualAdmissionMargin S trainingCost memoryLimit operationLimit := by
  classical
  let hcert := h.2.2.2.2
  let _ : Nonempty (Fin B) := hcert.1
  rw [residualAdmissionMargin, dite_eq_left h, residualStepMargin, dite_eq_left hcert.1,
    batchDirectionMinQuadraticMargin, ← Finset.inf'_univ_eq_ciInf]
  apply (Finset.lt_inf'_iff Finset.univ_nonempty).2
  intro b _hb
  exact lt_of_lt_of_le
    (batchDirectionHalfMargin_pos_of_neg
      (fun b => expandedFeatures (S.features b) (residualFeatures S b))
      (coreParameters (expandedTrainState S.state)) S.labels (residualDirection S)
      hcert.2 b)
    (batchDirectionHalfMargin_le_quadraticMargin
      (fun b => expandedFeatures (S.features b) (residualFeatures S b))
      (coreParameters (expandedTrainState S.state)) S.labels (residualDirection S) b)

theorem residualAdmissionMargin_nonneg {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (trainingCost memoryLimit operationLimit : ℕ) :
    0 ≤ residualAdmissionMargin S trainingCost memoryLimit operationLimit := by
  classical
  by_cases h : GrowthLegal V S (residualFeatures S) (residualDirection S)
      trainingCost memoryLimit operationLimit
  · exact (residualAdmissionMargin_pos_of_legal S trainingCost memoryLimit
      operationLimit h).le
  · simp [residualAdmissionMargin, h]

theorem residualAdmissionMargin_le_objective_sub {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    residualAdmissionMargin S trainingCost memoryLimit operationLimit ≤
      growthObjective S - growthObjective
        (boundedGrowStep S (residualFeatures S) (residualDirection S)
          trainingCost memoryLimit operationLimit opRisk write) := by
  classical
  by_cases h : GrowthLegal V S (residualFeatures S) (residualDirection S)
      trainingCost memoryLimit operationLimit
  · let hcert := h.2.2.2.2
    let _ : Nonempty (Fin B) := hcert.1
    have hcost : 0 ≤ (trainingCost : ℝ) ∧
        (expandedFeatureEvaluationCount B V : ℝ) + (trainingCost : ℝ) ≤
          S.state.res.budget :=
      growthLegal_expandedCost h
    have hper (b : Fin B) :
        batchSampleCE
            (fun b => expandedFeatures (S.features b) (residualFeatures S b))
            S.labels b
            (expandedHalfTrainStep S.features S.labels (residualFeatures S)
              (residualDirection S) S.state (trainingCost : ℝ) opRisk write) ≤
          batchSampleCE S.features S.labels b S.state - residualStepMargin S := by
      have hb := batchSampleCE_expandedHalfTrainStep_le_minQuadraticMargin
        S.features S.labels (residualFeatures S) (residualDirection S) S.state
        (trainingCost : ℝ) opRisk write hcost hcert b
      simpa only [residualStepMargin, dite_eq_left hcert.1] using hb
    have hsum :
        (∑ b, batchSampleCE
            (fun b => expandedFeatures (S.features b) (residualFeatures S b))
            S.labels b
            (expandedHalfTrainStep S.features S.labels (residualFeatures S)
              (residualDirection S) S.state (trainingCost : ℝ) opRisk write)) ≤
          ∑ b, (batchSampleCE S.features S.labels b S.state - residualStepMargin S) :=
      Finset.sum_le_sum fun b _hb => hper b
    have hBnat : 0 < B := by
      simpa only [Fintype.card_fin] using Fintype.card_pos_iff.mpr hcert.1
    have hB : 0 < (B : ℝ) := by exact_mod_cast hBnat
    have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
    have hmean :
        (∑ b, batchSampleCE
            (fun b => expandedFeatures (S.features b) (residualFeatures S b))
            S.labels b
            (expandedHalfTrainStep S.features S.labels (residualFeatures S)
              (residualDirection S) S.state (trainingCost : ℝ) opRisk write)) /
            (B : ℝ) ≤
          (∑ b, batchSampleCE S.features S.labels b S.state) / (B : ℝ) -
            residualStepMargin S := by
      calc
        _ ≤ (∑ b, (batchSampleCE S.features S.labels b S.state -
            residualStepMargin S)) / (B : ℝ) := hdiv
        _ = (∑ b, batchSampleCE S.features S.labels b S.state) / (B : ℝ) -
            residualStepMargin S := by
          rw [Finset.sum_sub_distrib, sub_div]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
          field_simp [ne_of_gt hB]
    rw [residualAdmissionMargin, dite_eq_left h,
      boundedGrowStep_of_legal S (residualFeatures S) (residualDirection S)
        trainingCost memoryLimit operationLimit opRisk write h]
    change residualStepMargin S ≤
      (∑ b, batchSampleCE S.features S.labels b S.state) / (B : ℝ) -
        (∑ b, batchSampleCE
          (fun b => expandedFeatures (S.features b) (residualFeatures S b))
          S.labels b
          (expandedHalfTrainStep S.features S.labels (residualFeatures S)
            (residualDirection S) S.state (trainingCost : ℝ) opRisk write)) / (B : ℝ)
    linarith
  · rw [residualAdmissionMargin, dite_eq_right h,
      boundedGrowStep_of_not_legal S (residualFeatures S) (residualDirection S)
        trainingCost memoryLimit operationLimit opRisk write h, sub_self]

theorem residualPath_sum_admissionMargins_le_initial_sub {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S0 : BoundedBatchState V B a r c k capacity)
    (costs memoryCaps operationCaps : ℕ → ℕ) (risks : ℕ → ℝ)
    (writes : ℕ → Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    (∑ t ∈ Finset.range T, residualAdmissionMargin
      (residualPath S0 costs memoryCaps operationCaps risks writes t)
      (costs t) (memoryCaps t) (operationCaps t)) ≤
      growthObjective (residualPath S0 costs memoryCaps operationCaps risks writes 0) -
        growthObjective (residualPath S0 costs memoryCaps operationCaps risks writes T) := by
  apply Hagi.Contracts.ObjectiveTrajectory.sum_drop_le_initial_sub
    (fun t => growthObjective
      (residualPath S0 costs memoryCaps operationCaps risks writes t))
    (fun t => residualAdmissionMargin
      (residualPath S0 costs memoryCaps operationCaps risks writes t)
      (costs t) (memoryCaps t) (operationCaps t)) T
  intro t
  simpa only [residualPath] using
    (residualAdmissionMargin_le_objective_sub
      (residualPath S0 costs memoryCaps operationCaps risks writes t)
      (costs t) (memoryCaps t) (operationCaps t) (risks t) (writes t))


end ResidualAdmissionMargin

section QuantifiedAdmission

/-- Every value of the local admission sum gives nonincreasing supplied-batch CE. -/
theorem growthObjective_quarantinedGrowStep_le {V : Type} [Fintype V]
    {B a r c k capacity : ℕ} (S : BoundedBatchState V B a r c k capacity)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (S.width + 1)))
    (trainingCost memoryLimit operationLimit : ℕ)
    (a : GrowthAdmission V S Z D trainingCost memoryLimit operationLimit)
    (opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    growthObjective (quarantinedGrowStep S Z D trainingCost memoryLimit operationLimit
      a opRisk write) ≤ growthObjective S := by
  cases a with
  | fullyVerified _ =>
      exact batchCEObjective_boundedGrowStep_le S Z D
        trainingCost memoryLimit operationLimit opRisk write
  | conditional _ _ => rfl
  | empiricalOnly _ => rfl
  | budgetViolation _ => rfl
  | unknown => rfl

theorem residualAdmissionMargin_le_growthObjective_sub_quarantinedGrowStep_of_promote
    {V : Type} [Fintype V] {B a r c k capacity : ℕ}
    (S : BoundedBatchState V B a r c k capacity)
    (trainingCost memoryLimit operationLimit : ℕ)
    (a : GrowthAdmission V S (residualFeatures S) (residualDirection S)
      trainingCost memoryLimit operationLimit)
    (h : a.debt) (opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    residualAdmissionMargin S trainingCost memoryLimit operationLimit ≤
      growthObjective S - growthObjective
        (quarantinedGrowStep S (residualFeatures S) (residualDirection S)
          trainingCost memoryLimit operationLimit (a.promote h) opRisk write) := by
  rw [quarantinedGrowStep_of_promote S (residualFeatures S) (residualDirection S)
    trainingCost memoryLimit operationLimit a h opRisk write]
  exact residualAdmissionMargin_le_objective_sub S trainingCost memoryLimit operationLimit
    opRisk write


end QuantifiedAdmission

section IteratedQuarantine

variable {V : Type} [Fintype V] {B a r c k capacity : ℕ}
variable (trainingCost memoryLimit operationLimit : ℕ) (opRisk : ℝ)
  (write : Option (Σ _ : ℕ, Fin c → ℝ))
variable (Zs : (T : BoundedBatchState V B a r c k capacity) → Fin B → V → ℝ)
variable (Ds : (T : BoundedBatchState V B a r c k capacity) →
  EuclideanSpace ℝ (Fin (T.width + 1)))
variable (admissions : (T : BoundedBatchState V B a r c k capacity) →
  GrowthAdmission V T (Zs T) (Ds T) trainingCost memoryLimit operationLimit)
variable (S0 : BoundedBatchState V B a r c k capacity)

/-- Current-state-gated quarantined growth has nonincreasing supplied-batch CE. -/
theorem growthObjective_iteratedQuarantinedGrowStep_antitone :
    Antitone (fun n : ℕ => growthObjective
      (((fun T : BoundedBatchState V B a r c k capacity =>
        quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
          (admissions T) opRisk write)^[n]) S0)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [Function.iterate_succ_apply']
  exact growthObjective_quarantinedGrowStep_le
    (((fun T : BoundedBatchState V B a r c k capacity =>
      quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
        (admissions T) opRisk write)^[n]) S0)
    (Zs (((fun T : BoundedBatchState V B a r c k capacity =>
      quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
        (admissions T) opRisk write)^[n]) S0))
    (Ds (((fun T : BoundedBatchState V B a r c k capacity =>
      quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
        (admissions T) opRisk write)^[n]) S0))
    trainingCost memoryLimit operationLimit
    (admissions (((fun T : BoundedBatchState V B a r c k capacity =>
      quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
        (admissions T) opRisk write)^[n]) S0)) opRisk write

/-- Nonnegative initial budget persists along the exact current-state iterates. -/
theorem iteratedQuarantinedGrowStep_budget_nonneg
    (hinitial : 0 ≤ S0.state.res.budget) (n : ℕ) :
    0 ≤ (((fun T : BoundedBatchState V B a r c k capacity =>
      quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
        (admissions T) opRisk write)^[n]) S0).state.res.budget := by
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      cases admissions (((fun T : BoundedBatchState V B a r c k capacity =>
        quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
          (admissions T) opRisk write)^[n]) S0) with
      | fullyVerified hlegal =>
          exact boundedGrowStep_budget_nonneg_of_legal
            (((fun T : BoundedBatchState V B a r c k capacity =>
              quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
                (admissions T) opRisk write)^[n]) S0)
            (Zs (((fun T : BoundedBatchState V B a r c k capacity =>
              quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
                (admissions T) opRisk write)^[n]) S0))
            (Ds (((fun T : BoundedBatchState V B a r c k capacity =>
              quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
                (admissions T) opRisk write)^[n]) S0))
            trainingCost memoryLimit operationLimit opRisk write hlegal
      | conditional _ _ => exact ih
      | empiricalOnly _ => exact ih
      | budgetViolation _ => exact ih
      | unknown => exact ih

/-- The nonnegative antitone current-state objective path converges to its infimum. -/
theorem growthObjective_iteratedQuarantinedGrowStep_tendsto_ciInf :
    Tendsto (fun t : ℕ => growthObjective
      (((fun T : BoundedBatchState V B a r c k capacity =>
        quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
          (admissions T) opRisk write)^[t]) S0)) atTop
      (𝓝 (⨅ t : ℕ, growthObjective
        (((fun T : BoundedBatchState V B a r c k capacity =>
          quarantinedGrowStep T (Zs T) (Ds T) trainingCost memoryLimit operationLimit
            (admissions T) opRisk write)^[t]) S0))) := by
  exact ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (growthObjective_iteratedQuarantinedGrowStep_antitone
      trainingCost memoryLimit operationLimit opRisk write Zs Ds admissions S0)
    (fun _ => growthObjective_nonneg _)

end IteratedQuarantine

end Hagi.Contracts.BatchCEGrowth

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

/-- Strict actual CE descent admits the candidate and identifies its exact declared resources. -/
theorem growthCandidate_legal_width_succ_flops_of_objective_lt_current
    (S : BoundedBatchState V B a r c k capacity) (idx : A)
    (hlt : growthObjective
      (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx) <
        growthObjective S) :
    GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx) (memoryCaps idx)
        (operationCaps idx) ∧
      (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx).width =
        S.width + 1 ∧
      (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S
        idx).state.res.flops =
        S.state.res.flops + (growthOperations B V (costs idx) : ℝ) := by
  classical
  by_cases hlegal : GrowthLegal V S (Zs idx S) (Ds idx S) (costs idx)
      (memoryCaps idx) (operationCaps idx)
  · refine ⟨hlegal, ?_, ?_⟩
    · exact (boundedGrowStep_legal_iff_width_succ S (Zs idx S) (Ds idx S) (costs idx)
        (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx)).mp hlegal
    · have hflops := growthCandidate_flops Zs Ds costs memoryCaps operationCaps
        risks writes S idx
      simp only [growthCandidateOperationIncrement, hlegal, ite_true] at hflops
      exact hflops
  · have hnext : growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S idx = S :=
      boundedGrowStep_of_not_legal S (Zs idx S) (Ds idx S) (costs idx)
        (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx) hlegal
    rw [hnext] at hlt
    exact (lt_irrefl _ hlt).elim

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

/-- A positive residual admission margin at a supplied comparator gives the
actual canonical selected successor strict descent and its exact resources. -/
theorem growthSelection_legal_width_succ_flops_of_residualAdmissionMargin_pos
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 idx : A)
    (hZ : Zs idx S = residualFeatures S)
    (hD : Ds idx S = residualDirection S)
    (hpositive : 0 < residualAdmissionMargin S (costs idx) (memoryCaps idx)
      (operationCaps idx)) :
    let sel := growthSelection Zs Ds costs memoryCaps operationCaps risks writes S
      operationBudget hop a0
    GrowthLegal V S (Zs sel S) (Ds sel S) (costs sel) (memoryCaps sel)
        (operationCaps sel) ∧
      (growthSelectionNext Zs Ds costs memoryCaps operationCaps risks writes S
        operationBudget hop a0).width = S.width + 1 ∧
      (growthSelectionNext Zs Ds costs memoryCaps operationCaps risks writes S
        operationBudget hop a0).state.res.flops =
        S.state.res.flops + (growthOperations B V (costs sel) : ℝ) := by
  dsimp only
  have hbound :
      residualAdmissionMargin S (costs idx) (memoryCaps idx)
          (operationCaps idx) ≤
        growthObjective S -
          growthObjective (growthCandidateStep Zs Ds costs
            memoryCaps operationCaps risks writes S idx) := by
    simpa only [growthCandidateStep, hZ, hD] using
      (residualAdmissionMargin_le_objective_sub S (costs idx)
        (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx))
  have hcomparator :
      growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S idx) < growthObjective S := by
    linarith only [hbound, hpositive]
  have hselected :=
    lt_of_le_of_lt
      (growthSelection_objective_le_candidate Zs Ds costs memoryCaps operationCaps
        risks writes S operationBudget hop a0 idx) hcomparator
  have hselected' :
      growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S (growthSelection Zs Ds costs memoryCaps operationCaps
          risks writes S operationBudget hop a0)) < growthObjective S := by
    simpa only [growthSelectionNext] using hselected
  have h := growthCandidate_legal_width_succ_flops_of_objective_lt_current
    Zs Ds costs memoryCaps operationCaps risks writes S
    (growthSelection Zs Ds costs memoryCaps operationCaps risks writes S
      operationBudget hop a0) hselected'
  simpa only [growthSelectionNext] using h

/-- Uniform supplied-batch CE error bounds the estimate-selected actual successor;
this supplies neither an estimator nor a held-out accuracy guarantee. -/
theorem growthDominatingSelection_objective_le_candidate_of_uniform_error
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 idx : A)
    (estimate : BoundedBatchState V B a r c k capacity → ℝ) (eps : ℝ)
    (heps : 0 ≤ eps)
    (herr : ∀ idx, |estimate (growthCandidateStep Zs Ds costs memoryCaps operationCaps
      risks writes S idx) -
      growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S idx)| ≤ eps) :
    let p := growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S
    let pE := withEstimatedValue p (fun T => -estimate T)
    let E := scoreDominatingIn pE S (growthMemoryIncrement B V) operationBudget Finset.univ
    let hStayE : a0 ∈ E := Finset.mem_filter.mpr
      ⟨(mem_feasible_withEstimatedValue p (fun T => -estimate T)).mpr
          (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps
            risks writes S operationBudget hop a0),
        a0, Finset.mem_univ a0, le_rfl⟩
    growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S (selectionIn pE S E a0 hStayE)) ≤
      growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S idx) + 2 * eps := by
  classical
  let p := growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S
  let pE := withEstimatedValue p (fun T => -estimate T)
  let E := scoreDominatingIn pE S (growthMemoryIncrement B V) operationBudget Finset.univ
  let hStayE : a0 ∈ E := Finset.mem_filter.mpr
    ⟨(mem_feasible_withEstimatedValue p (fun T => -estimate T)).mpr
        (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps
          risks writes S operationBudget hop a0),
      a0, Finset.mem_univ a0, le_rfl⟩
  have hsub : Finset.univ ⊆ feasible p (growthMemoryIncrement B V) operationBudget := by
    intro i _
    exact growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps
      risks writes S operationBudget hop i
  have herr' : ∀ i : A,
      |p.value (p.step i S) - (fun T => -estimate T) (p.step i S)| ≤ eps := by
    intro i
    simpa only [p, growthProblemAt, neg_sub_neg] using herr i
  have h := robust_quality_lower_selectionIn_scoreDominatingIn p
    (fun T => -estimate T) S (growthMemoryIncrement B V) operationBudget
    Finset.univ a0 (Finset.mem_univ a0) hsub eps heps herr' idx
    (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps
      risks writes S operationBudget hop idx)
  change -growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
      risks writes S idx) - 2 * eps ≤
    -growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
      risks writes S (selectionIn pE S E a0 hStayE)) at h
  linarith

/-- Strict supplied-batch CE progress when the actual candidate margin exceeds
the uniform supplied-batch CE error; no estimator or oracle is supplied. -/
theorem growthDominatingSelection_objective_lt_current_of_margin
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 idx : A)
    (estimate : BoundedBatchState V B a r c k capacity → ℝ) (eps : ℝ)
    (heps : 0 ≤ eps)
    (herr : ∀ idx, |estimate (growthCandidateStep Zs Ds costs memoryCaps operationCaps
      risks writes S idx) -
      growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S idx)| ≤ eps)
    (hmargin : growthObjective
        (growthCandidateStep Zs Ds costs memoryCaps operationCaps risks writes S idx) +
      2 * eps < growthObjective S) :
    let p := growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S
    let pE := withEstimatedValue p (fun T => -estimate T)
    let E := scoreDominatingIn pE S (growthMemoryIncrement B V) operationBudget Finset.univ
    let hStayE : a0 ∈ E := Finset.mem_filter.mpr
      ⟨(mem_feasible_withEstimatedValue p (fun T => -estimate T)).mpr
          (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps
            risks writes S operationBudget hop a0),
        a0, Finset.mem_univ a0, le_rfl⟩
    growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S (selectionIn pE S E a0 hStayE)) < growthObjective S := by
  have h := growthDominatingSelection_objective_le_candidate_of_uniform_error
    Zs Ds costs memoryCaps operationCaps risks writes S operationBudget hop a0 idx
    estimate eps heps herr
  dsimp only at h ⊢
  exact lt_of_le_of_lt h hmargin

/-- Strict supplied-batch CE progress when twice the uniform error is below
the actual residual admission margin of a supplied candidate. -/
theorem growthDominatingSelection_objective_lt_current_of_residualAdmissionMargin
    (S : BoundedBatchState V B a r c k capacity) (operationBudget : ℕ)
    (hop : ∀ i, growthOperations B V (costs i) ≤ operationBudget) (a0 idx : A)
    (estimate : BoundedBatchState V B a r c k capacity → ℝ) (eps : ℝ)
    (heps : 0 ≤ eps)
    (herr : ∀ idx, |estimate (growthCandidateStep Zs Ds costs memoryCaps operationCaps
      risks writes S idx) -
      growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S idx)| ≤ eps)
    (hZ : Zs idx S = residualFeatures S)
    (hD : Ds idx S = residualDirection S)
    (hsep : 2 * eps < residualAdmissionMargin S (costs idx) (memoryCaps idx)
      (operationCaps idx)) :
    let p := growthProblemAt Zs Ds costs memoryCaps operationCaps risks writes S
    let pE := withEstimatedValue p (fun T => -estimate T)
    let E := scoreDominatingIn pE S (growthMemoryIncrement B V) operationBudget Finset.univ
    let hStayE : a0 ∈ E := Finset.mem_filter.mpr
      ⟨(mem_feasible_withEstimatedValue p (fun T => -estimate T)).mpr
          (growthCandidate_mem_feasible Zs Ds costs memoryCaps operationCaps
            risks writes S operationBudget hop a0),
        a0, Finset.mem_univ a0, le_rfl⟩
    growthObjective (growthCandidateStep Zs Ds costs memoryCaps operationCaps
        risks writes S (selectionIn pE S E a0 hStayE)) < growthObjective S := by
  have hbound :
      residualAdmissionMargin S (costs idx) (memoryCaps idx)
          (operationCaps idx) ≤
        growthObjective S -
          growthObjective (growthCandidateStep Zs Ds costs
            memoryCaps operationCaps risks writes S idx) := by
    simpa only [growthCandidateStep, hZ, hD] using
      (residualAdmissionMargin_le_objective_sub S (costs idx)
        (memoryCaps idx) (operationCaps idx) (risks idx) (writes idx))
  have hmargin :
      growthObjective (growthCandidateStep Zs Ds costs memoryCaps
          operationCaps risks writes S idx) +
        2 * eps < growthObjective S := by
    linarith only [hbound, hsep]
  exact growthDominatingSelection_objective_lt_current_of_margin
    Zs Ds costs memoryCaps operationCaps risks writes S
    operationBudget hop a0 idx estimate eps heps herr hmargin

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

/-! Checked interoperability of the pinned Natural tactics with Hagi proofs. -/
namespace Hagi.Contracts

open Hagi.Contracts.BatchCEGrowth Hagi.Contracts.BatchCEGrowthSelection

example {V : Type} [Fintype V] {B a r c k capacity : ℕ}
    (S : BoundedBatchState V B a r c k capacity) :
    smoothedGrowthYield S S = 0 := by
  default_apply smoothedGrowthYield_self

end Hagi.Contracts
