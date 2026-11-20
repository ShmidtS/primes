import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Contracts.BatchCEBudgetGuard
import Hagi.Math.Foundations.Telescope
import Hagi.Unified.ParetoExecution
import Hagi.State.TrainState
import Hagi.State.Transition
import Hagi.Contracts.CEStepCertificate
import Hagi.Contracts.BatchCEStepCore
import Hagi.Contracts.BatchCETrajectory.Core


/-!
# BatchCETrajectoryGuardedInput

Guarded input-path abstraction `guardedBatchInputPath*`: per-sample and objective antitonicity, convergence, and budget accounting.
-/

set_option relaxedAutoImplicit false


namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- All direct current-state guarded inputs share the same actual recursive
path. Selection of an input remains separate from the existing guard. -/
noncomputable def guardedBatchInputPath (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) : ℕ → TrainState n a r c k
  | 0 => S
  | t + 1 => guardedBatchTrainStep X y inputFor
      (guardedBatchInputPath X y inputFor S t)

@[simp] theorem guardedBatchInputPath_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) : guardedBatchInputPath X y inputFor S 0 = S := rfl

@[simp] theorem guardedBatchInputPath_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (t : ℕ) :
    guardedBatchInputPath X y inputFor S (t + 1) =
      guardedBatchTrainStep X y inputFor (guardedBatchInputPath X y inputFor S t) := rfl

theorem guardedBatchInputPath_sampleCE_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    Antitone (fun t => batchSampleCE X y b (guardedBatchInputPath X y inputFor S t)) := by
  apply antitone_nat_of_succ_le
  intro t
  exact batchSampleCE_guardedBatchTrainStep_le X y inputFor
    (guardedBatchInputPath X y inputFor S t) b

theorem guardedBatchInputPath_objective_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    Antitone (fun t => batchCEObjective X y (guardedBatchInputPath X y inputFor S t)) := by
  apply antitone_nat_of_succ_le
  intro t
  exact batchCEObjective_guardedBatchTrainStep_le X y inputFor
    (guardedBatchInputPath X y inputFor S t)

theorem guardedBatchInputPath_sampleCE_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    Tendsto (fun t => batchSampleCE X y b (guardedBatchInputPath X y inputFor S t))
      atTop (𝓝 (⨅ t, batchSampleCE X y b
        (guardedBatchInputPath X y inputFor S t))) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (guardedBatchInputPath_sampleCE_antitone X y inputFor S b)
      (fun t => batchSampleCE_nonneg X y b (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_objective_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    Tendsto (fun t => batchCEObjective X y (guardedBatchInputPath X y inputFor S t))
      atTop (𝓝 (⨅ t, batchCEObjective X y (guardedBatchInputPath X y inputFor S t))) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (guardedBatchInputPath_objective_antitone X y inputFor S)
      (fun t => batchCEObjective_nonneg X y (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_sampleCE_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    0 ≤ ⨅ t, batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) :=
  ObjectiveTrajectory.ciInf_nonneg _
    (fun t => batchSampleCE_nonneg X y b (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_objective_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    0 ≤ ⨅ t, batchCEObjective X y (guardedBatchInputPath X y inputFor S t) :=
  ObjectiveTrajectory.ciInf_nonneg _
    (fun t => batchCEObjective_nonneg X y (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (hbudget : 0 ≤ S.res.budget) :
    ∀ t, 0 ≤ (guardedBatchInputPath X y inputFor S t).res.budget := by
  intro t
  induction t with
  | zero => exact hbudget
  | succ t ih => exact guardedBatchTrainStep_budget_nonneg X y inputFor _ ih

/-- A single local actual-margin law produces all finite/infinite sample CE
margin budgets for every direct guarded-input policy. -/
theorem guardedBatchInputPath_margin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k)
    (margin : Fin B → TrainState n a r c k → ℝ)
    (hmargin : ∀ b (T : TrainState n a r c k), 0 ≤ margin b T)
    (hbound : ∀ (T : TrainState n a r c k),
      0 ≤ (inputFor T).opCost ∧ (inputFor T).opCost ≤ T.res.budget →
        ∀ b, batchSampleCE X y b (guardedBatchTrainStep X y inputFor T) ≤
          batchSampleCE X y b T - margin b T)
    (hcost : ∀ t, 0 ≤ (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ∧
      (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ≤
        (guardedBatchInputPath X y inputFor S t).res.budget)
    (b : Fin B) :
    (∀ T, ∑ t ∈ Finset.range T,
        margin b (guardedBatchInputPath X y inputFor S t) ≤ batchSampleCE X y b S) ∧
      Summable (fun t => margin b (guardedBatchInputPath X y inputFor S t)) ∧
      Tendsto (fun t => margin b (guardedBatchInputPath X y inputFor S t)) atTop (𝓝 0) ∧
      ∑' t, margin b (guardedBatchInputPath X y inputFor S t) ≤ batchSampleCE X y b S := by
  have hle (t : ℕ) : margin b (guardedBatchInputPath X y inputFor S t) ≤
      batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) -
        batchSampleCE X y b (guardedBatchInputPath X y inputFor S (t + 1)) := by
    have h := hbound (guardedBatchInputPath X y inputFor S t) (hcost t) b
    rw [guardedBatchInputPath_succ]
    linarith
  exact ObjectiveTrajectory.budget4_of_drop_le
    (fun t => batchSampleCE X y b (guardedBatchInputPath X y inputFor S t))
    (fun t => margin b (guardedBatchInputPath X y inputFor S t))
    (fun t => batchSampleCE_nonneg X y b (guardedBatchInputPath X y inputFor S t))
    (fun t => hmargin b _) (fun t => hle t)

/-- The averaged counterpart of a generic local sample-margin law.  The
only batch denominator is on the averaged current margin. -/
theorem guardedBatchInputPath_meanMargin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k)
    (margin : Fin B → TrainState n a r c k → ℝ)
    (hmargin : ∀ b (T : TrainState n a r c k), 0 ≤ margin b T)
    (hbound : ∀ (T : TrainState n a r c k),
      0 ≤ (inputFor T).opCost ∧ (inputFor T).opCost ≤ T.res.budget →
        ∀ b, batchSampleCE X y b (guardedBatchTrainStep X y inputFor T) ≤
          batchSampleCE X y b T - margin b T)
    (hcost : ∀ t, 0 ≤ (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ∧
      (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ≤
        (guardedBatchInputPath X y inputFor S t).res.budget) :
    (∀ T, ∑ t ∈ Finset.range T,
        ((∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ≤
          batchCEObjective X y S) ∧
      Summable (fun t => (∑ b,
        margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ∧
      Tendsto (fun t => (∑ b,
        margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ))
        atTop (𝓝 0) ∧
      ∑' t, (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) ≤
        batchCEObjective X y S := by
  have hsucc (t : ℕ) : batchCEObjective X y
        (guardedBatchInputPath X y inputFor S (t + 1)) ≤
      batchCEObjective X y (guardedBatchInputPath X y inputFor S t) -
        (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) := by
    have hsum : (∑ b, batchSampleCE X y b
          (guardedBatchInputPath X y inputFor S (t + 1))) ≤
        ∑ b, (batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) -
          margin b (guardedBatchInputPath X y inputFor S t)) := by
      exact Finset.sum_le_sum (fun b _hb => by
        simpa only [guardedBatchInputPath_succ] using
          hbound (guardedBatchInputPath X y inputFor S t) (hcost t) b)
    have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
    unfold batchCEObjective batchLoss
    unfold Hagi.Probability.FiniteFamilyConfidence.empiricalMean
    calc
      (∑ b, batchSampleCE X y b (guardedBatchInputPath X y inputFor S (t + 1))) /
          (B : ℝ) ≤
        (∑ b, (batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) -
          margin b (guardedBatchInputPath X y inputFor S t))) / (B : ℝ) := hdiv
      _ = (∑ b, batchSampleCE X y b (guardedBatchInputPath X y inputFor S t)) /
          (B : ℝ) -
        (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) := by
        rw [Finset.sum_sub_distrib, sub_div]
  have hle (t : ℕ) : (∑ b,
        margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) ≤
      batchCEObjective X y (guardedBatchInputPath X y inputFor S t) -
        batchCEObjective X y (guardedBatchInputPath X y inputFor S (t + 1)) := by
    have h := hsucc t
    linarith [hsucc t]
  exact ObjectiveTrajectory.budget4_of_drop_le
    (fun t => batchCEObjective X y (guardedBatchInputPath X y inputFor S t))
    (fun t => (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ))
    (fun t => batchCEObjective_nonneg X y (guardedBatchInputPath X y inputFor S t))
    (fun t => div_nonneg
      (Finset.sum_nonneg (fun b _hb => hmargin b _)) (Nat.cast_nonneg B))
    (fun t => hle t)

noncomputable def directionBatchState (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : ℕ → TrainState n a r c k :=
  guardedBatchInputPath X y
    (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S

@[simp] theorem directionBatchState_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    directionBatchState X y D S opCost opRisk write 0 = S := rfl

@[simp] theorem directionBatchState_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    directionBatchState X y D S opCost opRisk write (t + 1) =
      batchDirectionTrainStep X y D
        (directionBatchState X y D S opCost opRisk write t) opCost opRisk write := rfl

/-- Actual sample CE and its current local guaranteed margin along the path. -/
noncomputable def directionBatchSampleCE (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) : ℝ :=
  batchSampleCE X y b (directionBatchState X y D S opCost opRisk write t)

noncomputable def directionBatchMargin (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) : ℝ :=
  batchDirectionMargin X
    (coreParameters (directionBatchState X y D S opCost opRisk write t)) y
      (D (directionBatchState X y D S opCost opRisk write t)) b

noncomputable def directionBatchObjective (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  batchCEObjective X y (directionBatchState X y D S opCost opRisk write t)

noncomputable def directionBatchMeanMargin (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  (∑ b, directionBatchMargin X y D S opCost opRisk write b t) / (B : ℝ)

end Hagi.Contracts.BatchCETrajectory

/-!
# BatchCETrajectoryDirection

Arbitrary-direction batch family `directionBatch*`: margins, non-regression, and summability.
-/

set_option relaxedAutoImplicit false


namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}



theorem directionBatchMargin_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) :
    0 ≤ directionBatchMargin X y D S opCost opRisk write b t :=
  batchDirectionMargin_nonneg _ _ _ _ _

theorem directionBatchSampleCE_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) :
    0 ≤ directionBatchSampleCE X y D S opCost opRisk write b t :=
  batchSampleCE_nonneg _ _ _ _

theorem directionBatchObjective_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    0 ≤ directionBatchObjective X y D S opCost opRisk write t :=
  batchCEObjective_nonneg _ _ _

theorem directionBatchMeanMargin_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    0 ≤ directionBatchMeanMargin X y D S opCost opRisk write t :=
  div_nonneg (Finset.sum_nonneg fun b _hb =>
    directionBatchMargin_nonneg X y D S opCost opRisk write b t)
      (Nat.cast_nonneg B)

theorem directionBatchSampleCE_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) :
    directionBatchSampleCE X y D S opCost opRisk write b (t + 1) ≤
      directionBatchSampleCE X y D S opCost opRisk write b t := by
  exact batchSampleCE_batchDirectionTrainStep_le X y D
    (directionBatchState X y D S opCost opRisk write t) opCost opRisk write b

theorem directionBatchObjective_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    directionBatchObjective X y D S opCost opRisk write (t + 1) ≤
      directionBatchObjective X y D S opCost opRisk write t := by
  exact batchCEObjective_batchDirectionTrainStep_le X y D
    (directionBatchState X y D S opCost opRisk write t) opCost opRisk write

theorem directionBatchSampleCE_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    Antitone (directionBatchSampleCE X y D S opCost opRisk write b) :=
  antitone_nat_of_succ_le (directionBatchSampleCE_succ_le
    X y D S opCost opRisk write b)

theorem directionBatchObjective_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Antitone (directionBatchObjective X y D S opCost opRisk write) :=
  antitone_nat_of_succ_le (directionBatchObjective_succ_le
    X y D S opCost opRisk write)

theorem directionBatchSampleCE_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    Tendsto (directionBatchSampleCE X y D S opCost opRisk write b) atTop
      (𝓝 (⨅ t, directionBatchSampleCE X y D S opCost opRisk write b t)) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (directionBatchSampleCE_antitone X y D S opCost opRisk write b)
    (directionBatchSampleCE_nonneg X y D S opCost opRisk write b)

theorem directionBatchObjective_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (directionBatchObjective X y D S opCost opRisk write) atTop
      (𝓝 (⨅ t, directionBatchObjective X y D S opCost opRisk write t)) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (directionBatchObjective_antitone X y D S opCost opRisk write)
    (directionBatchObjective_nonneg X y D S opCost opRisk write)

theorem directionBatchSampleCE_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    0 ≤ ⨅ t, directionBatchSampleCE X y D S opCost opRisk write b t :=
  ObjectiveTrajectory.ciInf_nonneg _
    (directionBatchSampleCE_nonneg X y D S opCost opRisk write b)

theorem directionBatchObjective_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    0 ≤ ⨅ t, directionBatchObjective X y D S opCost opRisk write t :=
  ObjectiveTrajectory.ciInf_nonneg _
    (directionBatchObjective_nonneg X y D S opCost opRisk write)

theorem directionBatchState_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hbudget : 0 ≤ S.res.budget) :
    ∀ t, 0 ≤ (directionBatchState X y D S opCost opRisk write t).res.budget := by
  intro t
  induction t with
  | zero => exact hbudget
  | succ t ih =>
      exact batchDirectionTrainStep_budget_nonneg X y D
        (directionBatchState X y D S opCost opRisk write t)
          opCost opRisk write ih

theorem directionBatchSampleCE_succ_le_margin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) (t : ℕ) :
    directionBatchSampleCE X y D S opCost opRisk write b (t + 1) ≤
      directionBatchSampleCE X y D S opCost opRisk write b t -
        directionBatchMargin X y D S opCost opRisk write b t := by
  exact batchSampleCE_batchDirectionTrainStep_le_margin X y D
    (directionBatchState X y D S opCost opRisk write t) opCost opRisk write
      (hcost t) b

theorem directionBatchObjective_succ_le_margin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (t : ℕ) :
    directionBatchObjective X y D S opCost opRisk write (t + 1) ≤
      directionBatchObjective X y D S opCost opRisk write t -
        directionBatchMeanMargin X y D S opCost opRisk write t := by
  exact batchCEObjective_batchDirectionTrainStep_le_margin_sum X y D
    (directionBatchState X y D S opCost opRisk write t) opCost opRisk write
      (hcost t)

theorem directionBatchMargin_sum_le_initial
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) (T : ℕ) :
    ∑ t ∈ Finset.range T, directionBatchMargin X y D S opCost opRisk write b t ≤
      batchSampleCE X y b S := by
  apply (guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost b).1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMeanMargin_sum_le_initial
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, directionBatchMeanMargin X y D S opCost opRisk write t ≤
      batchCEObjective X y S := by
  apply (guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost).1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMargin_summable
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) :
    Summable (directionBatchMargin X y D S opCost opRisk write b) := by
  apply (guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost b).2.1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMeanMargin_summable
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget) :
    Summable (directionBatchMeanMargin X y D S opCost opRisk write) := by
  apply (guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost).2.1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMargin_tendsto_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) :
    Tendsto (directionBatchMargin X y D S opCost opRisk write b) atTop (𝓝 0) := by
  apply (guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost b).2.2.1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMeanMargin_tendsto_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget) :
    Tendsto (directionBatchMeanMargin X y D S opCost opRisk write) atTop (𝓝 0) := by
  apply (guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost).2.2.1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMargin_tsum_le_initial
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) :
    ∑' t, directionBatchMargin X y D S opCost opRisk write b t ≤ batchSampleCE X y b S := by
  apply (guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost b).2.2.2
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMeanMargin_tsum_le_initial
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget) :
    ∑' t, directionBatchMeanMargin X y D S opCost opRisk write t ≤ batchCEObjective X y S := by
  apply (guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost).2.2.2
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

end Hagi.Contracts.BatchCETrajectory

/-!
# BatchCETrajectoryHalfMinNorm

Half-window quadratic and binding margins, minimum-norm squared-budget bounds, tendsto-zero and best-index statements.
-/

set_option relaxedAutoImplicit false


namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- The stronger half-window policy is the same generic actual guarded path. -/
noncomputable def directionBatchHalfState (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : ℕ → TrainState n a r c k :=
  guardedBatchInputPath X y
    (fun S => batchDirectionHalfTrainInput X y D S opCost opRisk write) S

@[simp] theorem directionBatchHalfState_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    directionBatchHalfState X y D S opCost opRisk write 0 = S := rfl

@[simp] theorem directionBatchHalfState_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    directionBatchHalfState X y D S opCost opRisk write (t + 1) =
      batchDirectionHalfTrainStep X y D
        (directionBatchHalfState X y D S opCost opRisk write t)
          opCost opRisk write := rfl

/-- Each full quadratic margin evaluated at the actual current half-path
state, direction and backbone parameters. -/
noncomputable def directionBatchHalfQuadraticMargin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) : ℝ :=
  batchDirectionQuadraticMargin X
    (coreParameters (directionBatchHalfState X y D S opCost opRisk write t))
    y (D (directionBatchHalfState X y D S opCost opRisk write t))
    (batchDirectionHalfEta X
      (coreParameters (directionBatchHalfState X y D S opCost opRisk write t))
      y (D (directionBatchHalfState X y D S opCost opRisk write t))) b

/-- One arithmetic mean of those current quadratic margins. -/
noncomputable def directionBatchHalfMeanQuadraticMargin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  (∑ b, directionBatchHalfQuadraticMargin
    X y D S opCost opRisk write b t) / (B : ℝ)

theorem directionBatchHalfQuadraticMargin_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) :
    0 ≤ directionBatchHalfQuadraticMargin X y D S opCost opRisk write b t :=
  (batchDirectionHalfMargin_nonneg _ _ _ _ _).trans
    (batchDirectionHalfMargin_le_quadraticMargin _ _ _ _ _)

/-- Actual legal half-window execution supplies exactly the local law expected
by the generic sample-margin budget. No positivity/certified-budget is added. -/
theorem directionBatchHalfQuadraticMargin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) :
    (∀ T, ∑ t ∈ Finset.range T,
        directionBatchHalfQuadraticMargin X y D S opCost opRisk write b t ≤
          batchSampleCE X y b S) ∧
      Summable (directionBatchHalfQuadraticMargin X y D S opCost opRisk write b) ∧
      Tendsto (directionBatchHalfQuadraticMargin
        X y D S opCost opRisk write b) atTop (𝓝 0) ∧
      ∑' t, directionBatchHalfQuadraticMargin X y D S opCost opRisk write b t ≤
        batchSampleCE X y b S := by
  apply guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionHalfTrainInput X y D T opCost opRisk write)
    S _ (fun b T => (batchDirectionHalfMargin_nonneg
      X (coreParameters T) y (D T) b).trans
        (batchDirectionHalfMargin_le_quadraticMargin
          X (coreParameters T) y (D T) b)) ?_ hcost b
  intro T hT
  simpa only [batchDirectionHalfTrainStep] using
    batchSampleCE_batchDirectionHalfTrainStep_le_quadraticMargin
      X y D T opCost opRisk write hT

noncomputable def directionBatchHalfBindingMargin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (b : Fin B) : ℝ := by
  classical
  exact if batchDirectionHalfEta X (coreParameters S) y (D S) =
      4 * (-dirAction (X b) (coreParameters S) (y b) (D S)) /
        (dirRange (X b) (D S)) ^ 2 then
    2 * (-dirAction (X b) (coreParameters S) (y b) (D S)) ^ 2 /
      (dirRange (X b) (D S)) ^ 2
  else 0

/-- The binding mask is nonnegative on the empty batch and whenever the
ordinary totalized half-window is zero, not only on the certified branch. -/
theorem directionBatchHalfBindingMargin_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (b : Fin B) :
    0 ≤ directionBatchHalfBindingMargin X y D S b := by
  classical
  unfold directionBatchHalfBindingMargin
  split_ifs <;> positivity

/-- Some coordinate binds the initial common half-window.  If negative
derivative certificates persist at all actual current states and supplied
transition costs are legal, its masked binding margins inherit the guarded
path's entire finite and infinite budget.  Other coordinates are masked to
zero at each current state rather than claiming the binding identity. -/
theorem exists_directionBatchHalfBindingMargin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) [Nonempty (Fin B)]
    (hneg : ∀ T b, dirAction (X b) (coreParameters T) (y b) (D T) < 0)
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y D S opCost opRisk write t).res.budget) :
    ∃ b : Fin B,
      batchDirectionHalfEta X (coreParameters S) y (D S) =
        4 * (-dirAction (X b) (coreParameters S) (y b) (D S)) /
          (dirRange (X b) (D S)) ^ 2 ∧
      ((∀ T, ∑ t ∈ Finset.range T, directionBatchHalfBindingMargin X y D
          (directionBatchHalfState X y D S opCost opRisk write t) b ≤
        batchSampleCE X y b S) ∧
      Summable (fun t => directionBatchHalfBindingMargin X y D
        (directionBatchHalfState X y D S opCost opRisk write t) b) ∧
      Tendsto (fun t => directionBatchHalfBindingMargin X y D
        (directionBatchHalfState X y D S opCost opRisk write t) b) atTop (𝓝 0) ∧
      ∑' t, directionBatchHalfBindingMargin X y D
        (directionBatchHalfState X y D S opCost opRisk write t) b ≤
        batchSampleCE X y b S) := by
  classical
  obtain ⟨b, hb⟩ := exists_batchDirectionHalfEta_eq_threshold
    X (coreParameters S) y (D S) ⟨inferInstance, hneg S⟩
  refine ⟨b, hb, guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionHalfTrainInput X y D T opCost opRisk write)
    S (fun b T => directionBatchHalfBindingMargin X y D T b)
    (fun b T => directionBatchHalfBindingMargin_nonneg X y D T b)
    ?_ hcost b⟩
  intro T hT b
  by_cases heta : batchDirectionHalfEta X (coreParameters T) y (D T) =
      4 * (-dirAction (X b) (coreParameters T) (y b) (D T)) /
        (dirRange (X b) (D T)) ^ 2
  · have hbase := batchSampleCE_batchDirectionHalfTrainStep_le_quadraticMargin
      X y D T opCost opRisk write hT b
    rw [batchDirectionQuadraticMargin_halfEta_of_eq_threshold
      X (coreParameters T) y (D T) ⟨inferInstance, hneg T⟩ b heta] at hbase
    simpa only [guardedBatchInputPath, batchDirectionHalfTrainStep,
      directionBatchHalfBindingMargin, ite_eq_left heta] using hbase
  · have hbase := batchSampleCE_batchDirectionHalfTrainStep_le
      X y D T opCost opRisk write b
    simpa only [guardedBatchInputPath, batchDirectionHalfTrainStep,
      directionBatchHalfBindingMargin, ite_eq_right heta, sub_zero] using hbase

/-- Finite-prefix and infinite negative-mean full-margin budgets. -/
theorem directionBatchHalfMeanQuadraticMargin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y D S opCost opRisk write t).res.budget) :
    (∀ T, ∑ t ∈ Finset.range T,
        directionBatchHalfMeanQuadraticMargin X y D S opCost opRisk write t ≤
          batchCEObjective X y S) ∧
      Summable (directionBatchHalfMeanQuadraticMargin X y D S opCost opRisk write) ∧
      Tendsto (directionBatchHalfMeanQuadraticMargin
        X y D S opCost opRisk write) atTop (𝓝 0) ∧
      ∑' t, directionBatchHalfMeanQuadraticMargin
        X y D S opCost opRisk write t ≤ batchCEObjective X y S := by
  apply guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionHalfTrainInput X y D T opCost opRisk write)
    S _ (fun b T => (batchDirectionHalfMargin_nonneg
      X (coreParameters T) y (D T) b).trans
        (batchDirectionHalfMargin_le_quadraticMargin
          X (coreParameters T) y (D T) b)) ?_ hcost
  intro T hT
  simpa only [batchDirectionHalfTrainStep] using
    batchSampleCE_batchDirectionHalfTrainStep_le_quadraticMargin
      X y D T opCost opRisk write hT

noncomputable def directionBatchMinNormSquaredBudget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) : ℝ :=
  2 * ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2 /
    ((B : ℝ) * batchFeatureRangeCoefficient X)

theorem directionBatchMinNormSquaredBudget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) :
    0 ≤ directionBatchMinNormSquaredBudget X y S := by
  unfold directionBatchMinNormSquaredBudget
  exact div_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg B) (batchFeatureRangeCoefficient_nonneg X))

/-- The combined minimum-norm KKT and finite feature-range bounds turn at
least one current binding coordinate into a mean full-margin lower bound.
The zero-minimizer branch needs no derivative certificate. -/
theorem directionBatchMinNormSquaredBudget_le_mean
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    directionBatchMinNormSquaredBudget X y S ≤
      directionBatchHalfMeanQuadraticMargin X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write 0 := by
  classical
  by_cases hω : batchGradientMinimizer X (coreParameters S) y = 0
  · have hmean : 0 ≤ directionBatchHalfMeanQuadraticMargin X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write 0 := by
      unfold directionBatchHalfMeanQuadraticMargin
      exact div_nonneg (Finset.sum_nonneg fun b _hb =>
        directionBatchHalfQuadraticMargin_nonneg X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write b 0) (Nat.cast_nonneg B)
    simpa [directionBatchMinNormSquaredBudget, hω] using hmean
  · let _ : Nonempty (Fin B) :=
      nonempty_fin_batch_of_minimizer_ne_zero X (coreParameters S) y hω
    have hN : 0 < ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hω)
    have hC : 0 < batchFeatureRangeCoefficient X :=
      batchFeatureRangeCoefficient_pos_of_minimizer_ne_zero
        X (coreParameters S) y hω
    have hneg : ∀ b, dirAction (X b) (coreParameters S) (y b)
        (-batchGradientMinimizer X (coreParameters S) y) < 0 := by
      intro b
      have hbound := dirAction_neg_batchGradientMinimizer_le
        X (coreParameters S) y b
      linarith only [hbound, hN]
    obtain ⟨b, hb⟩ := exists_batchDirectionHalfEta_eq_threshold
      X (coreParameters S) y (-batchGradientMinimizer X (coreParameters S) y)
      ⟨inferInstance, hneg⟩
    have hR := dirRange_pos_of_dirAction_neg
      (X b) (coreParameters S) (y b)
      (-batchGradientMinimizer X (coreParameters S) y) (hneg b)
    have hrange := dirRange_sq_le_batchFeatureRangeCoefficient_mul_norm_sq
      X (-batchGradientMinimizer X (coreParameters S) y) b
    have hrecip : 1 / batchFeatureRangeCoefficient X ≤
        ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2 /
          (dirRange (X b) (-batchGradientMinimizer X (coreParameters S) y)) ^ 2 := by
      apply (div_le_div_iff₀ hC (sq_pos_of_pos hR)).2
      simpa [mul_comm] using hrange
    have he : ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2 ≤
        -dirAction (X b) (coreParameters S) (y b)
          (-batchGradientMinimizer X (coreParameters S) y) := by
      have hbound := dirAction_neg_batchGradientMinimizer_le
        X (coreParameters S) y b
      linarith only [hbound]
    have hq : 2 * ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2 /
        batchFeatureRangeCoefficient X ≤
      directionBatchHalfQuadraticMargin X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write b 0 := by
      calc
        2 * ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2 /
            batchFeatureRangeCoefficient X =
          (2 * ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2) *
            (1 / batchFeatureRangeCoefficient X) := by ring
        _ ≤ (2 * ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2) *
            (‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2 /
              (dirRange (X b)
                (-batchGradientMinimizer X (coreParameters S) y)) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hrecip (by positivity)
        _ = 2 * (‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2) ^ 2 /
            (dirRange (X b)
              (-batchGradientMinimizer X (coreParameters S) y)) ^ 2 := by ring
        _ ≤ 2 * (-dirAction (X b) (coreParameters S) (y b)
            (-batchGradientMinimizer X (coreParameters S) y)) ^ 2 /
            (dirRange (X b)
              (-batchGradientMinimizer X (coreParameters S) y)) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (by simpa only [pow_two] using
              (mul_self_le_mul_self (sq_nonneg _) he)) (by norm_num)
        _ = directionBatchHalfQuadraticMargin X y
            (fun T => -batchGradientMinimizer X (coreParameters T) y)
            S opCost opRisk write b 0 := by
          symm
          exact batchDirectionQuadraticMargin_halfEta_of_eq_threshold
            X (coreParameters S) y (-batchGradientMinimizer X (coreParameters S) y)
            ⟨inferInstance, hneg⟩ b hb
    have hsum : 2 * ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2 /
        batchFeatureRangeCoefficient X ≤
        ∑ b, directionBatchHalfQuadraticMargin X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write b 0 := hq.trans
      (Finset.single_le_sum (fun c _hc =>
        directionBatchHalfQuadraticMargin_nonneg X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write c 0) (Finset.mem_univ b))
    calc
      directionBatchMinNormSquaredBudget X y S =
          (2 * ‖batchGradientMinimizer X (coreParameters S) y‖ ^ 2 /
            batchFeatureRangeCoefficient X) / (B : ℝ) := by
        unfold directionBatchMinNormSquaredBudget
        ring
      _ ≤ (∑ b, directionBatchHalfQuadraticMargin X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write b 0) / (B : ℝ) :=
        div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
      _ = directionBatchHalfMeanQuadraticMargin X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write 0 := rfl

theorem directionBatchMinNormSquaredBudget_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t).res.budget) :
    (∀ T, ∑ t ∈ Finset.range T, directionBatchMinNormSquaredBudget X y
        (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t) ≤ batchCEObjective X y S) ∧
      Summable (fun t => directionBatchMinNormSquaredBudget X y
        (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t)) ∧
      Tendsto (fun t => directionBatchMinNormSquaredBudget X y
        (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t)) atTop (𝓝 0) ∧
      ∑' t, directionBatchMinNormSquaredBudget X y
        (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t) ≤ batchCEObjective X y S := by
  have hbase := directionBatchHalfMeanQuadraticMargin_budget X y
    (fun T => -batchGradientMinimizer X (coreParameters T) y)
    S opCost opRisk write hcost
  have hfinit : ∀ T, ∑ t ∈ Finset.range T, directionBatchMinNormSquaredBudget X y
      (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t) ≤ batchCEObjective X y S := by
    intro T
    exact (Finset.sum_le_sum (fun t _ht => by
      simpa only [directionBatchHalfMeanQuadraticMargin,
        directionBatchHalfQuadraticMargin, directionBatchHalfState_zero] using
        directionBatchMinNormSquaredBudget_le_mean X y
          (directionBatchHalfState X y
            (fun T => -batchGradientMinimizer X (coreParameters T) y)
            S opCost opRisk write t) opCost opRisk write)).trans (hbase.1 T)
  exact ObjectiveTrajectory.budget4_of_sum_le _ _
    (fun t => directionBatchMinNormSquaredBudget_nonneg X y _) hfinit

/-- Along minimum-norm half-window guarded training, the current minimum-norm
point's square tends to zero on the actual path. This is not global CE
minimization or convergence of arbitrary gradients or parameters. -/
theorem directionBatchMinNormSq_tendsto_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t).res.budget) :
    Tendsto (fun t => ‖batchGradientMinimizer X
      (coreParameters (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t)) y‖ ^ 2) atTop (𝓝 0) := by
  by_cases hB : B = 0
  · subst B
    simp only [batchGradientMinimizer_empty, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact tendsto_const_nhds
  have hBpos : 0 < (B : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hB
  by_cases hC : batchFeatureRangeCoefficient X = 0
  · have hsq : ∀ t, ‖batchGradientMinimizer X
        (coreParameters (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t)) y‖ ^ 2 = 0 := by
      intro t
      have hzero : batchGradientMinimizer X
          (coreParameters (directionBatchHalfState X y
            (fun T => -batchGradientMinimizer X (coreParameters T) y)
            S opCost opRisk write t)) y = 0 := by
        by_contra hn
        have hp := batchFeatureRangeCoefficient_pos_of_minimizer_ne_zero X
          (coreParameters (directionBatchHalfState X y
            (fun T => -batchGradientMinimizer X (coreParameters T) y)
            S opCost opRisk write t)) y hn
        exact (ne_of_gt hp) hC
      simp [hzero]
    simp_rw [hsq]
    exact tendsto_const_nhds
  have hCpos := lt_of_le_of_ne
    (batchFeatureRangeCoefficient_nonneg X) (Ne.symm hC)
  have h_tendsto := (directionBatchMinNormSquaredBudget_budget X y S
    opCost opRisk write hcost).2.2.1
  have hmul := h_tendsto.const_mul ((B : ℝ) * batchFeatureRangeCoefficient X / 2)
  have heq (t : ℕ) : ((B : ℝ) * batchFeatureRangeCoefficient X / 2) *
      directionBatchMinNormSquaredBudget X y
        (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t) =
      ‖batchGradientMinimizer X
        (coreParameters (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t)) y‖ ^ 2 := by
    unfold directionBatchMinNormSquaredBudget
    field_simp [ne_of_gt hBpos, ne_of_gt hCpos]
  simpa only [heq, mul_zero] using hmul

/-- Norm-square convergence of the minimum-norm gradient point lifts to
convergence of that Euclidean point itself. It is not parameter convergence
or convergence of an arbitrary gradient vector or a held-out loss gap. -/
theorem directionBatchMinNorm_tendsto_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t).res.budget) :
    Tendsto (fun t => batchGradientMinimizer X
      (coreParameters (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t)) y) atTop (𝓝 0) := by
  have hsquared := directionBatchMinNormSq_tendsto_zero X y S
    opCost opRisk write hcost
  have hnorm : Tendsto (fun t => ‖batchGradientMinimizer X
      (coreParameters (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t)) y‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsquared.sqrt
  exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm

/-- The squared norm of the current minimum-norm point is summable along the
actual minimum-norm half-window path, with total mass bounded by the initial
supplied-batch CE. Empty batches and zero feature range remain zero cases. -/
theorem directionBatchMinNormSq_summable_and_tsum_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t).res.budget) :
    Summable (fun t => ‖batchGradientMinimizer X
      (coreParameters (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t)) y‖ ^ 2) ∧
      ∑' t, ‖batchGradientMinimizer X
        (coreParameters (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t)) y‖ ^ 2 ≤
        ((B : ℝ) * batchFeatureRangeCoefficient X) * batchCEObjective X y S / 2 := by
  by_cases hB : B = 0
  · subst B
    simp
  have hBpos : 0 < (B : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hB
  by_cases hC : batchFeatureRangeCoefficient X = 0
  · have hsq : ∀ t, ‖batchGradientMinimizer X
        (coreParameters (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t)) y‖ ^ 2 = 0 := by
      intro t
      have hzero : batchGradientMinimizer X
          (coreParameters (directionBatchHalfState X y
            (fun T => -batchGradientMinimizer X (coreParameters T) y)
            S opCost opRisk write t)) y = 0 := by
        by_contra hn
        have hp := batchFeatureRangeCoefficient_pos_of_minimizer_ne_zero X
          (coreParameters (directionBatchHalfState X y
            (fun T => -batchGradientMinimizer X (coreParameters T) y)
            S opCost opRisk write t)) y hn
        exact (ne_of_gt hp) hC
      simp [hzero]
    simp_rw [hsq]
    simp [hC]
  have hCpos := lt_of_le_of_ne
    (batchFeatureRangeCoefficient_nonneg X) (Ne.symm hC)
  have hκ : 0 < (B : ℝ) * batchFeatureRangeCoefficient X := mul_pos hBpos hCpos
  have hbudget : ∀ T, ∑ t ∈ Finset.range T,
      2 * ‖batchGradientMinimizer X
        (coreParameters (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t)) y‖ ^ 2 /
        ((B : ℝ) * batchFeatureRangeCoefficient X) ≤ batchCEObjective X y S := by
    simpa only [directionBatchMinNormSquaredBudget] using
      (directionBatchMinNormSquaredBudget_budget X y S
        opCost opRisk write hcost).1
  exact ObjectiveTrajectory.summable_and_tsum_le_of_sum_two_mul_div_le
    hκ (fun _t => sq_nonneg _) hbudget


end Hagi.Contracts.BatchCETrajectory
