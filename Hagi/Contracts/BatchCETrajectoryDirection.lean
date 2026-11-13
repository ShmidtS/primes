import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Unified.GuardedRobustTrajectory
import Hagi.Contracts.BatchCETrajectoryGuardedInput

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
