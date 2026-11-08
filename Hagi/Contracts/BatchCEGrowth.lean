/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory

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
    simpa [ceResidual, hvt] using Hagi.Energy.smax_pos (ceLogits X θ) v
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

end Hagi.Contracts.BatchCEGrowth
