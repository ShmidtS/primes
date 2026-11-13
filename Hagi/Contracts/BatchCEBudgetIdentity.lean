import Hagi.Contracts.CEStepCertificate
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEExpansion
import Hagi.Model.CEHeldout
import Hagi.Unified.ParetoExecution
import Hagi.Contracts.BatchCEBudgetPareto

/-!
# BatchCEBudgetIdentity

Budgeted batch CE feasibility problems, identity fixture, and the identity minimum-norm step. Split from `BatchCEStepCertificate` (C255).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BudgetedBatchCE

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Model.CEExpansion

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- The same two identical-feature, identical-label samples form a concrete
nonvacuous acceptance probe for the budgeted Pareto guard. -/
noncomputable def identityParetoBatchStep : TrainState 2 0 0 0 0 :=
  budgetedParetoBatchTrainStep mixedFeatures sameZeroLabels
    identityInitialState (1 / 2) (1 / 4) none

/-- Every initial sample has CE `log 2` in the concrete same-label batch. -/
theorem batchSampleCE_sameZero_initial (b : Fin 2) :
    batchSampleCE mixedFeatures sameZeroLabels b identityInitialState =
      Real.log 2 := by
  have hzero : coreParameters identityInitialState = 0 := rfl
  simpa [batchSampleCE, mixedFeatures, sameZeroLabels, hzero] using
    (identity_CE_zero_parameters (0 : Fin 2))

/-- The pointwise guard accepts this concrete transition; it genuinely calls
the existing canonical batch update rather than merely assigning budgets. -/
theorem identityParetoBatchStep_eq_batchTrainStep :
    identityParetoBatchStep = batchTrainStep mixedFeatures sameZeroLabels
      identityInitialState (1 / 2) (1 / 4) none := by
  have hmean := sameZero_batchLoss_after_lt_log_two
  have hzero : coreParameters identityInitialState = 0 := rfl
  unfold batchLoss Hagi.Probability.FiniteFamilyConfidence.empiricalMean at hmean
  rw [Fin.sum_univ_two] at hmean
  simp only [mixedFeatures, sameZeroLabels] at hmean
  unfold identityParetoBatchStep
  apply budgetedParetoBatchTrainStep_of_active
  refine ⟨?_, ?_⟩
  · refine ⟨by norm_num, ?_⟩
    change (1 / 2 : ℝ) ≤ 2
    norm_num
  · intro b
    rw [batchSampleCE_sameZero_initial]
    change Hagi.ceOneHot (sameZeroLabels b)
      (ceLogits (mixedFeatures b)
        (coreParameters (batchTrainStep mixedFeatures sameZeroLabels
          identityInitialState (1 / 2) (1 / 4) none))) ≤ Real.log 2
    rw [coreParameters_batchTrainStep, hzero]
    fin_cases b <;>
      dsimp [mixedFeatures, sameZeroLabels] at * <;>
      linarith only [hmean]

/-- Two generic control successors: identity and the guarded transition
for a training input computed from the current state. -/
noncomputable def guardedBatchParetoStepFun
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (action : Fin 2) (S : TrainState n a r c k) : TrainState n a r c k :=
  if action = 1 then guardedBatchTrainStep X y inputFor S else S

/-- Both generic controller actions non-increase actual supplied-batch
mean CE, using the proved guard for the update and equality for identity. -/
theorem batchCEObjective_guardedBatchParetoStepFun_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (action : Fin 2) (S : TrainState n a r c k) :
    batchCEObjective X y (guardedBatchParetoStepFun X y inputFor action S) ≤
      batchCEObjective X y S := by
  by_cases h : action = 1
  · subst action
    simpa [guardedBatchParetoStepFun] using
      (batchCEObjective_guardedBatchTrainStep_le X y inputFor S)
  · simp [guardedBatchParetoStepFun, h]

/-- The generic finite-batch Pareto controller. Operation indices remain
logical model units, not physical execution measurements. -/
noncomputable def guardedBatchParetoProblem
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) :
    Hagi.Unified.ParetoExecution.ControllerProblem (Fin 2) (TrainState n a r c k) where
  value := fun S => -batchCEObjective X y S
  step := guardedBatchParetoStepFun X y inputFor
  memory := fun action => action.val
  operations := fun action => B * action.val
  safe := fun action => ∀ S : TrainState n a r c k,
    batchCEObjective X y (guardedBatchParetoStepFun X y inputFor action S) ≤
      batchCEObjective X y S

/-- Every generic action is proved safe; no blanket proposition decision
procedure or external safety assertion is introduced. -/
noncomputable instance guardedBatchParetoProblemSafeDecidable
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) :
    DecidablePred (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y inputFor).safe :=
  fun action => isTrue
    (batchCEObjective_guardedBatchParetoStepFun_le X y inputFor action)

/-- The generic controller value is exactly negative actual mean CE. -/
@[simp] theorem guardedBatchParetoProblem_value
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    (guardedBatchParetoProblem X y inputFor).value S =
      -batchCEObjective X y S := rfl

@[simp] theorem guardedBatchParetoProblem_step_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    (guardedBatchParetoProblem X y inputFor).step 0 S = S := by
  simp [guardedBatchParetoProblem, guardedBatchParetoStepFun]

@[simp] theorem guardedBatchParetoProblem_step_one
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    (guardedBatchParetoProblem X y inputFor).step 1 S =
      guardedBatchTrainStep X y inputFor S := by
  simp [guardedBatchParetoProblem, guardedBatchParetoStepFun]

open Hagi.Unified.ParetoExecution

/-- The generic stay action is feasible under every logical cap pair. -/
theorem guardedBatchPareto_stay_feasible
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y inputFor) M C := by
  apply mem_feasible.mpr
  refine ⟨?_, ?_, ?_⟩
  · exact batchCEObjective_guardedBatchParetoStepFun_le X y inputFor 0
  · simp [guardedBatchParetoProblem]
  · simp [guardedBatchParetoProblem]

/-- Generic update feasibility is exactly one memory unit and at most `B`
logical operation units. -/
theorem guardedBatchPareto_one_feasible_iff
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (M C : ℕ) :
    (1 : Fin 2) ∈ feasible (guardedBatchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y inputFor) M C ↔ 1 ≤ M ∧ B ≤ C := by
  constructor
  · intro h
    have hresources := (mem_feasible.mp h).2
    simp only [guardedBatchParetoProblem] at hresources
    omega
  · rintro ⟨hM, hC⟩
    apply mem_feasible.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact batchCEObjective_guardedBatchParetoStepFun_le X y inputFor 1
    · simpa [guardedBatchParetoProblem] using hM
    · simpa [guardedBatchParetoProblem] using hC

/-- The thin minimum-norm specialization of the generic finite-batch Pareto
problem.  The only change is the current-state training input generator. -/
noncomputable def minimumNormBatchParetoProblem
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Hagi.Unified.ParetoExecution.ControllerProblem (Fin 2) (TrainState n a r c k) :=
  guardedBatchParetoProblem X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write)

/-- Safety of both minimum-norm controller actions is inherited from the
generic proof, not from a duplicated proposition decision procedure. -/
noncomputable instance minimumNormBatchParetoProblemSafeDecidable
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    DecidablePred (minimumNormBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write).safe :=
  guardedBatchParetoProblemSafeDecidable X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write)

/-- Minimum-norm controller value is the negative of actual supplied-batch
mean CE. -/
@[simp] theorem minimumNormBatchParetoProblem_value
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (minimumNormBatchParetoProblem X y opCost opRisk write).value S =
      -batchCEObjective X y S :=
  guardedBatchParetoProblem_value X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S

/-- The minimum-norm controller value is nonpositive. -/
theorem minimumNormBatchParetoProblem_value_nonpos
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (minimumNormBatchParetoProblem X y opCost opRisk write).value S ≤ 0 := by
  rw [minimumNormBatchParetoProblem_value]
  exact neg_nonpos.mpr (batchCEObjective_nonneg X y S)

/-- Action zero preserves the state. -/
@[simp] theorem minimumNormBatchParetoProblem_step_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (minimumNormBatchParetoProblem X y opCost opRisk write).step 0 S = S :=
  guardedBatchParetoProblem_step_zero X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S

/-- Action one runs the guarded minimum-norm batch step. -/
@[simp] theorem minimumNormBatchParetoProblem_step_one
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (minimumNormBatchParetoProblem X y opCost opRisk write).step 1 S =
      batchMinimumNormTrainStep X y S opCost opRisk write :=
  guardedBatchParetoProblem_step_one X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S

/-- The stay action is feasible under every logical resource cap pair. -/
theorem minimumNormBatchPareto_stay_feasible
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y opCost opRisk write) M C :=
  guardedBatchPareto_stay_feasible X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) M C

/-- Update feasibility is exactly one memory unit and at most `B` logical
operation units for the minimum-norm controller as well. -/
theorem minimumNormBatchPareto_one_feasible_iff
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (1 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y opCost opRisk write) M C ↔ 1 ≤ M ∧ B ≤ C :=
  guardedBatchPareto_one_feasible_iff X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) M C

/-- The reusable two-sample specialization of the generic finite-batch
Pareto problem, using the explicit current-state segment input. -/
noncomputable def pairMinimumNormBatchParetoProblem
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Hagi.Unified.ParetoExecution.ControllerProblem (Fin 2) (TrainState n a r c k) :=
  guardedBatchParetoProblem X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write)

/-- Both pair-controller actions inherit generic safety; no new safety
decider, resource model or trajectory is constructed. -/
noncomputable instance pairMinimumNormBatchParetoProblemSafeDecidable
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    DecidablePred (pairMinimumNormBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write).safe :=
  guardedBatchParetoProblemSafeDecidable X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write)

/-- The explicit pair controller is exactly the prior minimum-norm
controller, by function extensionality of its current-state input. -/
theorem pairMinimumNormBatchParetoProblem_eq_minimumNormBatchParetoProblem
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    pairMinimumNormBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
        X y opCost opRisk write =
      minimumNormBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
        X y opCost opRisk write := by
  unfold pairMinimumNormBatchParetoProblem minimumNormBatchParetoProblem
  apply congrArg (guardedBatchParetoProblem X y)
  funext S
  exact batchPairMinimumNormTrainInput_eq_batchMinimumNormTrainInput
    X y S opCost opRisk write

/-- The pair-controller value is negative actual supplied-batch mean CE. -/
@[simp] theorem pairMinimumNormBatchParetoProblem_value
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (pairMinimumNormBatchParetoProblem X y opCost opRisk write).value S =
      -batchCEObjective X y S :=
  guardedBatchParetoProblem_value X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) S

/-- The pair-controller stay action is inherited unchanged. -/
@[simp] theorem pairMinimumNormBatchParetoProblem_step_zero
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (pairMinimumNormBatchParetoProblem X y opCost opRisk write).step 0 S = S :=
  guardedBatchParetoProblem_step_zero X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) S

/-- The pair-controller update action is the guarded explicit pair step. -/
@[simp] theorem pairMinimumNormBatchParetoProblem_step_one
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (pairMinimumNormBatchParetoProblem X y opCost opRisk write).step 1 S =
      batchPairMinimumNormTrainStep X y S opCost opRisk write :=
  guardedBatchParetoProblem_step_one X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) S

/-- The pair controller's stay action is feasible under every cap pair. -/
theorem pairMinimumNormBatchPareto_stay_feasible
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (pairMinimumNormBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y opCost opRisk write) M C :=
  guardedBatchPareto_stay_feasible X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) M C

/-- Pair update feasibility retains the generic logical resource condition:
one memory unit and at most two operation-index units. -/
theorem pairMinimumNormBatchPareto_one_feasible_iff
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (1 : Fin 2) ∈ feasible (pairMinimumNormBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y opCost opRisk write) M C ↔
        1 ≤ M ∧ 2 ≤ C :=
  guardedBatchPareto_one_feasible_iff X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) M C

/-- Two control successors: identity and the budget/pointwise-guarded batch
transition with the same supplied optimizer, resource and optional write inputs. -/
noncomputable def batchParetoStepFun
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (action : Fin 2) (S : TrainState n a r c k) : TrainState n a r c k :=
  guardedBatchParetoStepFun X y
    (fun S => batchTrainInput X y S opCost opRisk write) action S

/-- The finite-batch Pareto controller. Its model operation index is `B` per
update action, not a count of physical FLOPs or estimator evaluations. -/
noncomputable def batchParetoProblem
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Hagi.Unified.ParetoExecution.ControllerProblem (Fin 2) (TrainState n a r c k) where
  value := fun S => -batchCEObjective X y S
  step := guardedBatchParetoStepFun X y
    (fun S => batchTrainInput X y S opCost opRisk write)
  memory := fun action => action.val
  operations := fun action => B * action.val
  safe := fun action => ∀ S : TrainState n a r c k,
    batchCEObjective X y (guardedBatchParetoStepFun X y
      (fun S => batchTrainInput X y S opCost opRisk write) action S) ≤
      batchCEObjective X y S

/-- Both finite actions are decided by the proved batch CE guards, not by an
unsubstantiated executable safety certificate. -/
noncomputable instance batchParetoProblemSafeDecidable
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    DecidablePred (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write).safe :=
  guardedBatchParetoProblemSafeDecidable X y
    (fun S => batchTrainInput X y S opCost opRisk write)

@[simp] theorem batchParetoProblem_step_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (batchParetoProblem X y opCost opRisk write).step 0 S = S := by
  exact guardedBatchParetoProblem_step_zero X y
    (fun S => batchTrainInput X y S opCost opRisk write) S

@[simp] theorem batchParetoProblem_step_one
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (batchParetoProblem X y opCost opRisk write).step 1 S =
      budgetedParetoBatchTrainStep X y S opCost opRisk write := by
  exact guardedBatchParetoProblem_step_one X y
    (fun S => batchTrainInput X y S opCost opRisk write) S

open Hagi.Unified.ParetoExecution

/-- The stay action is feasible under every logical resource cap pair. -/
theorem batchPareto_stay_feasible
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y opCost opRisk write) M C := by
  apply mem_feasible.mpr
  refine ⟨?_, ?_, ?_⟩
  · exact batchCEObjective_guardedBatchParetoStepFun_le X y
      (fun S => batchTrainInput X y S opCost opRisk write) 0
  · simp [batchParetoProblem]
  · simp [batchParetoProblem]

/-- Update feasibility is exactly one memory index unit and at most `B`
logical operation-index units. It does not measure physical execution. -/
theorem batchPareto_one_feasible_iff
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (1 : Fin 2) ∈ feasible (batchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y opCost opRisk write) M C ↔ 1 ≤ M ∧ B ≤ C := by
  constructor
  · intro h
    have hresources := (mem_feasible.mp h).2
    simp only [batchParetoProblem] at hresources
    omega
  · rintro ⟨hM, hC⟩
    apply mem_feasible.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact batchCEObjective_guardedBatchParetoStepFun_le X y
        (fun S => batchTrainInput X y S opCost opRisk write) 1
    · simpa [batchParetoProblem] using hM
    · simpa [batchParetoProblem] using hC

/-- A singleton finite batch with the two-class identity feature map. -/
abbrev minimumNormIdentityFeatures : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ => 1

/-- Its sole supplied target is class zero. -/
abbrev minimumNormIdentityLabels : Fin 1 → Fin 2 := fun _ => 0

/-- Exact first raw residual-gradient coordinate at zero initial weights. -/
theorem minimumNormIdentity_residualGradient_zero :
    (batchResidualGradient (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0).ofLp 0 = -1 / 2 := by
  change residualTranspose (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (0 : EuclideanSpace ℝ (Fin 2)) (0 : Fin 2) 0 = -1 / 2
  norm_num [residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

/-- Exact second raw residual-gradient coordinate at zero initial weights. -/
theorem minimumNormIdentity_residualGradient_one :
    (batchResidualGradient (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0).ofLp 1 = 1 / 2 := by
  change residualTranspose (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (0 : EuclideanSpace ℝ (Fin 2)) (0 : Fin 2) 1 = 1 / 2
  norm_num [residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

/-- In a singleton hull, minimum-norm membership itself identifies the
minimizer with the sole raw residual gradient. -/
theorem batchGradientMinimizer_minimumNormIdentity :
    batchGradientMinimizer minimumNormIdentityFeatures
      (coreParameters identityInitialState) minimumNormIdentityLabels =
    batchResidualGradient (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0 := by
  have hmem := batchGradientMinimizer_mem minimumNormIdentityFeatures
    (coreParameters identityInitialState) minimumNormIdentityLabels
  have hrange : Set.range (fun b => batchResidualGradient
      (minimumNormIdentityFeatures b) (coreParameters identityInitialState)
        (minimumNormIdentityLabels b)) =
      {batchResidualGradient (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (coreParameters identityInitialState) 0} := by
    apply Set.range_eq_singleton
    intro b
    fin_cases b
    rfl
  rw [hrange, convexHull_singleton] at hmem
  exact hmem

/-- The singleton raw residual gradient is nonzero at zero initial weights. -/
theorem minimumNormIdentity_residualGradient_ne_zero :
    batchResidualGradient (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0 ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z.ofLp 0) h
  rw [minimumNormIdentity_residualGradient_zero] at hcoord
  norm_num at hcoord

/-- Hence the singleton minimum-norm point is nonzero. -/
theorem batchGradientMinimizer_minimumNormIdentity_ne_zero :
    batchGradientMinimizer minimumNormIdentityFeatures
      (coreParameters identityInitialState) minimumNormIdentityLabels ≠ 0 := by
  rw [batchGradientMinimizer_minimumNormIdentity]
  exact minimumNormIdentity_residualGradient_ne_zero

/-- The concrete minimum-norm guarded candidate, with hypothetical abstract
ledger inputs rather than hardware measurements. -/
noncomputable def identityMinimumNormBatchStep : TrainState 2 0 0 0 0 :=
  batchMinimumNormTrainStep minimumNormIdentityFeatures minimumNormIdentityLabels
    identityInitialState (1 / 2) (1 / 4) none

/-- The positive concrete cost is affordable at the initial declared budget. -/
theorem identityMinimumNormBatchStep_cost_feasible :
    0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ identityInitialState.res.budget := by
  change 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 2
  norm_num

/-- The singleton candidate is genuinely accepted and is the complete
canonical transition on the new current-state input. -/
theorem identityMinimumNormBatchStep_eq_trainStep :
    identityMinimumNormBatchStep =
      trainStep identityInitialState (batchMinimumNormTrainInput
        minimumNormIdentityFeatures minimumNormIdentityLabels identityInitialState
          (1 / 2) (1 / 4) none) :=
  batchMinimumNormTrainStep_of_active minimumNormIdentityFeatures
    minimumNormIdentityLabels identityInitialState (1 / 2) (1 / 4) none
      identityMinimumNormBatchStep_cost_feasible

/-- The accepted concrete step has the actual common minimum-norm parameters. -/
theorem coreParameters_identityMinimumNormBatchStep :
    coreParameters identityMinimumNormBatchStep =
      batchCommonNextParameters minimumNormIdentityFeatures
        (coreParameters identityInitialState) minimumNormIdentityLabels :=
  coreParameters_batchMinimumNormTrainStep minimumNormIdentityFeatures
    minimumNormIdentityLabels identityInitialState (1 / 2) (1 / 4) none
      identityMinimumNormBatchStep_cost_feasible

/-- Every sample of the singleton batch has strict actual CE descent. -/
theorem batchSampleCE_identityMinimumNormBatchStep_lt (b : Fin 1) :
    batchSampleCE minimumNormIdentityFeatures minimumNormIdentityLabels b
      identityMinimumNormBatchStep <
    batchSampleCE minimumNormIdentityFeatures minimumNormIdentityLabels b
      identityInitialState :=
  batchSampleCE_batchMinimumNormTrainStep_lt minimumNormIdentityFeatures
    minimumNormIdentityLabels identityInitialState (1 / 2) (1 / 4) none
      identityMinimumNormBatchStep_cost_feasible
      batchGradientMinimizer_minimumNormIdentity_ne_zero b

/-- The actual singleton mean CE strictly decreases, inherited from the
general strict-sum argument rather than a numerical exponential estimate. -/
theorem batchCEObjective_identityMinimumNormBatchStep_lt :
    batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
      identityMinimumNormBatchStep <
    batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
      identityInitialState :=
  batchCEObjective_batchMinimumNormTrainStep_lt minimumNormIdentityFeatures
    minimumNormIdentityLabels identityInitialState (1 / 2) (1 / 4) none
      identityMinimumNormBatchStep_cost_feasible
      batchGradientMinimizer_minimumNormIdentity_ne_zero

/-- The accepted singleton step adds only its declared abstract input cost to
the existing canonical flops ledger; QP work is not silently included. -/
theorem identityMinimumNormBatchStep_flops :
    identityMinimumNormBatchStep.res.flops =
      identityInitialState.res.flops + (1 / 2 : ℝ) :=
  batchMinimumNormTrainStep_flops_of_active minimumNormIdentityFeatures
    minimumNormIdentityLabels identityInitialState (1 / 2) (1 / 4) none
      identityMinimumNormBatchStep_cost_feasible


end Hagi.Contracts.BudgetedBatchCE
