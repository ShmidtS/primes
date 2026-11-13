import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Unified.GuardedRobustTrajectory

/-!
# BatchCETrajectoryFixedBatch

Repeated common-direction batch CE transitions on one fixed finite batch, with telemetered loss, antitonicity, and convergence to the real infimum.
-/

set_option relaxedAutoImplicit false


namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}




/-- Execute repeatedly on the same finite batch, recomputing the mean residual
and safe step from every actual successor.  Ledger/write arguments stay fixed
logical inputs to the unmodified ordinary transition. -/
noncomputable def fixedBatchState (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : ℕ → TrainState n a r c k
  | 0 => S
  | t + 1 => batchTrainStep X y (fixedBatchState X y S opCost opRisk write t)
      opCost opRisk write

@[simp] theorem fixedBatchState_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    fixedBatchState X y S opCost opRisk write 0 = S := rfl

@[simp] theorem fixedBatchState_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    fixedBatchState X y S opCost opRisk write (t + 1) =
      batchTrainStep X y (fixedBatchState X y S opCost opRisk write t)
        opCost opRisk write := rfl

/-- The actual mean batch CE along the recursive transition. -/
noncomputable def fixedBatchObjective (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  batchCEObjective X y (fixedBatchState X y S opCost opRisk write t)

@[simp] theorem fixedBatchObjective_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    fixedBatchObjective X y S opCost opRisk write 0 = batchCEObjective X y S := rfl

/-- One recursive successor bounds the actual mean loss by minus the computed
majorizer residual.  This is an inequality, not an assertion that the actual
decrease equals that residual. -/
theorem fixedBatchObjective_succ_le_actual_sub_drop [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    fixedBatchObjective X y S opCost opRisk write (t + 1) ≤
      fixedBatchObjective X y S opCost opRisk write t -
        batchCertifiedDrop X
          (coreParameters (fixedBatchState X y S opCost opRisk write t)) y := by
  have h := batchCertifiedDrop_le_actualDrop X y
    (fixedBatchState X y S opCost opRisk write t) opCost opRisk write
  unfold fixedBatchObjective
  rw [fixedBatchState_succ]
  linarith

/-- Repeated batch updates never increase their supplied-batch objective. -/
theorem fixedBatchObjective_succ_le [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    fixedBatchObjective X y S opCost opRisk write (t + 1) ≤
      fixedBatchObjective X y S opCost opRisk write t := by
  have h := fixedBatchObjective_succ_le_actual_sub_drop X y S
    opCost opRisk write t
  have hnonneg := batchCertifiedDrop_nonneg X
    (coreParameters (fixedBatchState X y S opCost opRisk write t)) y
  linarith

/-- The exact actual objective differences telescope without any positive-range
or nonzero-batch hypothesis. -/
theorem fixedBatchObjective_actual_telescope
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ t ∈ Finset.range T,
        (fixedBatchObjective X y S opCost opRisk write t -
          fixedBatchObjective X y S opCost opRisk write (t + 1)) =
      batchCEObjective X y S - fixedBatchObjective X y S opCost opRisk write T := by
  simpa using Finset.sum_range_sub' (fixedBatchObjective X y S opCost opRisk write) T

/-- Total actual loss decrease over a finite trajectory dominates the total
computed certified residuals.  This does not equal the residuals to extra CE
loss decrease. -/
theorem fixedBatchObjective_sum_certifiedDrop_le_telescope [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ t ∈ Finset.range T, batchCertifiedDrop X
        (coreParameters (fixedBatchState X y S opCost opRisk write t)) y ≤
      batchCEObjective X y S - fixedBatchObjective X y S opCost opRisk write T := by
  exact ObjectiveTrajectory.sum_drop_le_initial_sub
    (fixedBatchObjective X y S opCost opRisk write)
    (fun t => batchCertifiedDrop X
      (coreParameters (fixedBatchState X y S opCost opRisk write t)) y) T
    (fun t => batchCertifiedDrop_le_actualDrop X y
      (fixedBatchState X y S opCost opRisk write t) opCost opRisk write)

/-- Antitonicity follows from per-successor actual loss nonincrease. -/
theorem fixedBatchObjective_antitone [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Antitone (fixedBatchObjective X y S opCost opRisk write) :=
  antitone_nat_of_succ_le (fixedBatchObjective_succ_le X y S opCost opRisk write)

/-- Every trajectory loss is nonnegative, including the raw empty mean. -/
theorem fixedBatchObjective_nonneg [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    0 ≤ fixedBatchObjective X y S opCost opRisk write t :=
  batchLoss_nonneg X (coreParameters (fixedBatchState X y S opCost opRisk write t)) y

/-- The actual fixed-batch mean CE converges to a real lower bound.  Neither
zero infimum nor convergence of parameters/residuals follows from this fact. -/
theorem fixedBatchObjective_tendsto_ciInf [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fixedBatchObjective X y S opCost opRisk write) atTop
      (𝓝 (⨅ t, fixedBatchObjective X y S opCost opRisk write t)) := by
  exact ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg
    (fixedBatchObjective X y S opCost opRisk write)
    (fixedBatchObjective_antitone X y S opCost opRisk write)
    (fixedBatchObjective_nonneg X y S opCost opRisk write)

/-- The actual loss infimum is nonnegative, without being declared optimal. -/
theorem fixedBatchObjective_ciInf_nonneg [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    0 ≤ ⨅ t, fixedBatchObjective X y S opCost opRisk write t :=
  ObjectiveTrajectory.ciInf_nonneg _
    (fixedBatchObjective_nonneg X y S opCost opRisk write)

/-- The empty fixed batch has zero raw mean at every time. -/
theorem fixedBatchObjective_empty [Nonempty V]
    (X : Fin 0 → Matrix V (Fin n) ℝ) (y : Fin 0 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    fixedBatchObjective X y S opCost opRisk write t = 0 := by
  simp [fixedBatchObjective, batchCEObjective, batchLoss,
    Hagi.Probability.FiniteFamilyConfidence.empiricalMean]

end Hagi.Contracts.BatchCETrajectory
