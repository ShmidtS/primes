import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Unified.GuardedRobustTrajectory
import Hagi.Contracts.BatchCETrajectoryMinNorm

/-!
# BatchCETrajectoryFixtures

Concrete identity and sameZero fixtures with computed positive initial drops.
-/

set_option relaxedAutoImplicit false


namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Hagi.Unified.ParetoExecution Hagi.Unified.FixedBiasBinaryProgress
open Hagi.Unified.GuardedRobustTrajectory Hagi.Unified.GuardedRobustSelection
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Actual initial mean CE decrease of the committed same-label guarded step. -/
noncomputable def sameZeroInitialMeanDrop : ℝ :=
  batchCEObjective mixedFeatures sameZeroLabels identityInitialState -
    batchCEObjective mixedFeatures sameZeroLabels identityParetoBatchStep

/-- The proved actual initial drop is strictly positive. -/
theorem sameZeroInitialMeanDrop_pos : 0 < sameZeroInitialMeanDrop := by
  rw [sameZeroInitialMeanDrop, identityParetoBatchStep_eq_batchTrainStep]
  exact sub_pos.mpr (batchCEObjective_batchTrainStep_lt
    mixedFeatures sameZeroLabels identityInitialState (1 / 2) (1 / 4) none
    sameZero_rangeSquare_pos)

/-- A concrete threshold defined from the proved actual drop, not guessed. -/
noncomputable def sameZeroScaledThreshold : ℝ := sameZeroInitialMeanDrop / 2

/-- Half the proved positive actual initial drop is a positive threshold. -/
theorem sameZeroScaledThreshold_pos : 0 < sameZeroScaledThreshold :=
  div_pos sameZeroInitialMeanDrop_pos (by norm_num)

/-- The same-label scaled guarded path, with unit memory cap and two logical
batch-operation cap units. -/
noncomputable def identityScaledBatchCEPath : ℕ → TrainState 2 0 0 0 0 :=
  scaledBiasBinaryPath
    (batchParetoProblem (n := 2) (a := 0) (r := 0) (c := 0) (k := 0)
      mixedFeatures sameZeroLabels (1 / 2) (1 / 4) none)
    sameZeroScaledThreshold 1 2
    (batchPareto_stay_feasible mixedFeatures sameZeroLabels
      (1 / 2) (1 / 4) none 1 2) identityInitialState

/-- The first real threshold upgrade executes `identityParetoBatchStep`, hence
the canonical guarded batch training transition rather than an identity step. -/
theorem identityScaledBatchCEPath_one :
    identityScaledBatchCEPath 1 = identityParetoBatchStep := by
  let p : ControllerProblem (Fin 2) (TrainState 2 0 0 0 0) :=
    batchParetoProblem mixedFeatures sameZeroLabels (1 / 2) (1 / 4) none
  let h0 : (0 : Fin 2) ∈ feasible p 1 2 := by
    dsimp only [p]
    exact batchPareto_stay_feasible mixedFeatures sameZeroLabels
      (1 / 2) (1 / 4) none 1 2
  have h1 : (1 : Fin 2) ∈ feasible p 1 2 := by
    dsimp only [p]
    exact (batchPareto_one_feasible_iff _ _ _ _ _ _ _).mpr (by norm_num)
  have hstep : p.step (1 : Fin 2) identityInitialState =
      identityParetoBatchStep := by
    change budgetedParetoBatchTrainStep mixedFeatures sameZeroLabels
      identityInitialState (1 / 2) (1 / 4) none = identityParetoBatchStep
    rfl
  have hstay : ∀ S : TrainState 2 0 0 0 0, p.step (0 : Fin 2) S = S := by
    intro S
    dsimp only [p]
    exact batchParetoProblem_step_zero _ _ _ _ _ _
  have hdrop : sameZeroScaledThreshold ≤ sameZeroInitialMeanDrop := by
    rw [sameZeroScaledThreshold]
    linarith only [sameZeroInitialMeanDrop_pos]
  change sameZeroScaledThreshold ≤
    batchCEObjective mixedFeatures sameZeroLabels identityInitialState -
      batchCEObjective mixedFeatures sameZeroLabels identityParetoBatchStep at hdrop
  have hup : estimatedUpgrade p
      (scaledBiasBinaryValueEstimate p sameZeroScaledThreshold)
      (sameZeroScaledThreshold / 2)
      (scaledBiasBinaryPath p sameZeroScaledThreshold 1 2 h0
        identityInitialState 0) 1 2 0 := by
    refine ⟨1, h1, ?_⟩
    change (-batchCEObjective mixedFeatures sameZeroLabels
        (p.step 0 (scaledBiasBinaryPath p sameZeroScaledThreshold 1 2 h0
          identityInitialState 0)) - sameZeroScaledThreshold / 2) +
        2 * (sameZeroScaledThreshold / 2) ≤
      -batchCEObjective mixedFeatures sameZeroLabels
        (p.step 1 (scaledBiasBinaryPath p sameZeroScaledThreshold 1 2 h0
          identityInitialState 0)) - sameZeroScaledThreshold / 2
    rw [scaledBiasBinaryPath_zero, hstay, hstep]
    linarith only [hdrop]
  have hnext := scaledBiasBinaryPath_succ_eq_step_one_of_upgrade p
    sameZeroScaledThreshold sameZeroScaledThreshold_pos 1 2 h0
    identityInitialState hstay 0 hup
  rw [scaledBiasBinaryPath_zero] at hnext
  unfold identityScaledBatchCEPath
  exact hnext.trans hstep

/-- Actual initial mean-CE decrease of the accepted singleton minimum-norm
step, measured from the old state to the complete new state. -/
noncomputable def minimumNormIdentityInitialMeanDrop : ℝ :=
  batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
      identityInitialState -
    batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
      identityMinimumNormBatchStep

/-- The committed singleton minimum-norm step has strictly positive actual
initial mean-CE drop. -/
theorem minimumNormIdentityInitialMeanDrop_pos :
    0 < minimumNormIdentityInitialMeanDrop := by
  rw [minimumNormIdentityInitialMeanDrop]
  exact sub_pos.mpr batchCEObjective_identityMinimumNormBatchStep_lt

/-- A threshold defined as half the proved actual singleton initial drop. -/
noncomputable def minimumNormIdentityScaledThreshold : ℝ :=
  minimumNormIdentityInitialMeanDrop / 2

/-- Half the strict singleton initial mean-CE drop is positive. -/
theorem minimumNormIdentityScaledThreshold_pos :
    0 < minimumNormIdentityScaledThreshold :=
  div_pos minimumNormIdentityInitialMeanDrop_pos (by norm_num)

/-- The singleton minimum-norm scaled path. One update consumes one memory
unit and one logical supplied-batch operation unit, matching `B = 1`. -/
noncomputable def identityMinimumNormScaledBatchCEPath :
    ℕ → TrainState 2 0 0 0 0 :=
  scaledBiasBinaryPath
    (minimumNormBatchParetoProblem (n := 2) (a := 0) (r := 0) (c := 0) (k := 0)
      minimumNormIdentityFeatures minimumNormIdentityLabels (1 / 2) (1 / 4) none)
    minimumNormIdentityScaledThreshold 1 1
    (minimumNormBatchPareto_stay_feasible minimumNormIdentityFeatures
      minimumNormIdentityLabels (1 / 2) (1 / 4) none 1 1) identityInitialState

/-- The first threshold upgrade executes the actual accepted current-state
minimum-norm update. It is neither the old mean candidate nor a field-only
identity operation. -/
theorem identityMinimumNormScaledBatchCEPath_one :
    identityMinimumNormScaledBatchCEPath 1 = identityMinimumNormBatchStep := by
  let p : ControllerProblem (Fin 2) (TrainState 2 0 0 0 0) :=
    minimumNormBatchParetoProblem minimumNormIdentityFeatures
      minimumNormIdentityLabels (1 / 2) (1 / 4) none
  let h0 : (0 : Fin 2) ∈ feasible p 1 1 := by
    dsimp only [p]
    exact minimumNormBatchPareto_stay_feasible minimumNormIdentityFeatures
      minimumNormIdentityLabels (1 / 2) (1 / 4) none 1 1
  have h1 : (1 : Fin 2) ∈ feasible p 1 1 := by
    dsimp only [p]
    exact (minimumNormBatchPareto_one_feasible_iff _ _ _ _ _ _ _).mpr (by norm_num)
  have hstep : p.step (1 : Fin 2) identityInitialState =
      identityMinimumNormBatchStep := by
    change batchMinimumNormTrainStep minimumNormIdentityFeatures
      minimumNormIdentityLabels identityInitialState (1 / 2) (1 / 4) none =
        identityMinimumNormBatchStep
    rfl
  have hstay : ∀ S : TrainState 2 0 0 0 0, p.step (0 : Fin 2) S = S := by
    intro S
    dsimp only [p]
    exact minimumNormBatchParetoProblem_step_zero _ _ _ _ _ _
  have hdrop : minimumNormIdentityScaledThreshold ≤
      minimumNormIdentityInitialMeanDrop := by
    rw [minimumNormIdentityScaledThreshold]
    linarith only [minimumNormIdentityInitialMeanDrop_pos]
  change minimumNormIdentityScaledThreshold ≤
    batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
        identityInitialState -
      batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
        identityMinimumNormBatchStep at hdrop
  have hup : estimatedUpgrade p
      (scaledBiasBinaryValueEstimate p minimumNormIdentityScaledThreshold)
      (minimumNormIdentityScaledThreshold / 2)
      (scaledBiasBinaryPath p minimumNormIdentityScaledThreshold 1 1 h0
        identityInitialState 0) 1 1 0 := by
    refine ⟨1, h1, ?_⟩
    change (-batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
        (p.step 0 (scaledBiasBinaryPath p minimumNormIdentityScaledThreshold 1 1 h0
          identityInitialState 0)) - minimumNormIdentityScaledThreshold / 2) +
        2 * (minimumNormIdentityScaledThreshold / 2) ≤
      -batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
        (p.step 1 (scaledBiasBinaryPath p minimumNormIdentityScaledThreshold 1 1 h0
          identityInitialState 0)) - minimumNormIdentityScaledThreshold / 2
    rw [scaledBiasBinaryPath_zero, hstay, hstep]
    linarith only [hdrop]
  have hnext := scaledBiasBinaryPath_succ_eq_step_one_of_upgrade p
    minimumNormIdentityScaledThreshold minimumNormIdentityScaledThreshold_pos
    1 1 h0 identityInitialState hstay 0 hup
  rw [scaledBiasBinaryPath_zero] at hnext
  unfold identityMinimumNormScaledBatchCEPath
  exact hnext.trans hstep

end Hagi.Contracts.BatchCETrajectory
