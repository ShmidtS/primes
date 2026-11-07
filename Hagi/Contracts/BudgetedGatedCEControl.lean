/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.GatedCEStepCertificate
import Hagi.Unified.GuardedRobustSelection
set_option linter.style.header false
set_option relaxedAutoImplicit false

/-!
# Budget-gated two-action control of canonical gated CE

The new transition executes the existing canonical `gatedCETrainStep` only
when `0 ≤ opCost ∧ opCost ≤ S.res.budget`; otherwise it is the identity on the
full `TrainState`. The old transition is unchanged. Actual one-target gated
CE cannot increase in either branch, using the existing safe-step certificate
without a positive-alignment premise. A nonnegative declared budget remains
nonnegative, and stored quality telemetry is preserved.

The `Fin 2` controller has the identity stay action and the budget-gated
update action. Its value is negative actual gated CE. `memory = a.val` and
`operations = 2 * a.val` are logical action-index model units, not resource
counters in `TrainState` or physical measurements. Safety is actual CE
non-regression for every full training state.

The value estimate is the true value with the constant pessimistic bias
`-1 / 2`. Its pointwise absolute error is exactly `1 / 2`, hence it satisfies
the feasible-successor error interface of
`Hagi.Unified.GuardedRobustSelection.guardedRobustNext`. This is exact
deterministic arithmetic, not an IID, probabilistic, or calibration guarantee.
No trajectory, physical-resource, or generalization claim is made here.
-/

namespace Hagi.Contracts.BudgetedGatedCE

open Hagi.State Hagi.Model
open Hagi.Model.GatedCESafeStep
open Hagi.Contracts.GatedCEStep Hagi.Contracts.CEStep
open Hagi.Unified.ParetoExecution

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- Execute the existing canonical gated CE step exactly when its supplied
nonnegative logical cost fits the current declared budget; otherwise stay. -/
noncomputable def budgetedGatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  if 0 ≤ opCost ∧ opCost ≤ S.res.budget then
    gatedCETrainStep X t S opCost opRisk write
  else
    S

/-- In the active budget branch the new step is exactly the old canonical
transition, including its full optimizer, memory, resource, and risk updates. -/
theorem budgetedGatedCETrainStep_of_active (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (h : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    budgetedGatedCETrainStep X t S opCost opRisk write =
      gatedCETrainStep X t S opCost opRisk write := by
  exact ite_eq_left h

/-- A negative or over-budget cost makes the guarded transition the identity
on the entire state. -/
theorem budgetedGatedCETrainStep_of_inactive (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (h : ¬ (0 ≤ opCost ∧ opCost ≤ S.res.budget)) :
    budgetedGatedCETrainStep X t S opCost opRisk write = S := by
  exact ite_eq_right h

/-- Actual gated one-target CE never increases, for every supplied cost,
risk, and optional write. No positive-alignment hypothesis is needed. -/
theorem gatedCEObjective_budgetedGatedCETrainStep_le
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    gatedCEObjective X t (budgetedGatedCETrainStep X t S opCost opRisk write) ≤
      gatedCEObjective X t S := by
  letI : Nonempty V := ⟨t⟩
  by_cases h : 0 ≤ opCost ∧ opCost ≤ S.res.budget
  · rw [budgetedGatedCETrainStep_of_active X t S opCost opRisk write h]
    have hdrop := gatedSafeDrop_le_gatedCETrainStep_drop
      X t S opCost opRisk write
    have hnonneg := gatedSafeDrop_nonneg X (coreParameters S) t
    linarith
  · rw [budgetedGatedCETrainStep_of_inactive X t S opCost opRisk write h]

/-- The guarded transition preserves a nonnegative declared budget. -/
theorem budgetedGatedCETrainStep_budget_nonneg
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hbudget : 0 ≤ S.res.budget) :
    0 ≤ (budgetedGatedCETrainStep X t S opCost opRisk write).res.budget := by
  by_cases h : 0 ≤ opCost ∧ opCost ≤ S.res.budget
  · rw [budgetedGatedCETrainStep_of_active X t S opCost opRisk write h,
      gatedCETrainStep, trainStep_budget, gatedCETrainInput]
    exact sub_nonneg.mpr h.2
  · rw [budgetedGatedCETrainStep_of_inactive X t S opCost opRisk write h]
    exact hbudget

/-- The guarded transition preserves the stored quality telemetry; this is
not an identification of that telemetry with the actual CE objective. -/
theorem qual_budgetedGatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (budgetedGatedCETrainStep X t S opCost opRisk write).qual = S.qual := by
  by_cases h : 0 ≤ opCost ∧ opCost ≤ S.res.budget
  · rw [budgetedGatedCETrainStep_of_active X t S opCost opRisk write h]
    exact qual_gatedCETrainStep X t S opCost opRisk write
  · rw [budgetedGatedCETrainStep_of_inactive X t S opCost opRisk write h]

/-- For nonnegative supplied cost, the declared FLOP ledger is nondecreasing.
This concerns only `res.flops`, not physical hardware work. -/
theorem flops_le_budgetedGatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hcost : 0 ≤ opCost) :
    S.res.flops ≤
      (budgetedGatedCETrainStep X t S opCost opRisk write).res.flops := by
  by_cases h : 0 ≤ opCost ∧ opCost ≤ S.res.budget
  · rw [budgetedGatedCETrainStep_of_active X t S opCost opRisk write h,
      gatedCETrainStep, trainStep_flops, gatedCETrainInput]
    exact le_add_of_nonneg_right hcost
  · rw [budgetedGatedCETrainStep_of_inactive X t S opCost opRisk write h]

/-- The two controller successors: action zero stays, action one executes the
new budget-gated canonical transition. -/
noncomputable def gatedCEStepFun (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (action : Fin 2) (S : TrainState n a r c k) : TrainState n a r c k :=
  if action = 1 then budgetedGatedCETrainStep X t S opCost opRisk write else S

/-- Canonical full-state two-action gated CE controller. -/
noncomputable def gatedCEProblem (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    ControllerProblem (Fin 2) (TrainState n a r c k) where
  value := fun S => -gatedCEObjective X t S
  step := gatedCEStepFun X t opCost opRisk write
  memory := fun action => action.val
  operations := fun action => 2 * action.val
  safe := fun action => ∀ S : TrainState n a r c k,
    gatedCEObjective X t (gatedCEStepFun X t opCost opRisk write action S) ≤
      gatedCEObjective X t S

/-- Classical decidability is confined to the noncomputable controller API. -/
noncomputable instance gatedCEProblemSafeDecidable
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    DecidablePred (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write).safe :=
  fun _ => Classical.propDecidable _

@[simp] theorem gatedCEProblem_step_zero (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (gatedCEProblem X t opCost opRisk write).step 0 S = S := by
  simp [gatedCEProblem, gatedCEStepFun]

@[simp] theorem gatedCEProblem_step_one (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (gatedCEProblem X t opCost opRisk write).step 1 S =
      budgetedGatedCETrainStep X t S opCost opRisk write := by
  simp [gatedCEProblem, gatedCEStepFun]

/-- The identity stay action is feasible under every pair of logical caps. -/
theorem gatedCE_stay_feasible (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) M C := by
  apply mem_feasible.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro S
    rw [show gatedCEStepFun X t opCost opRisk write 0 S = S by
      simp [gatedCEStepFun]]
  · simp [gatedCEProblem]
  · simp [gatedCEProblem]

/-- Action one is feasible exactly when its declared memory and operation
model-unit costs fit: `1 ≤ M` and `2 ≤ C`. -/
theorem gatedCE_one_feasible_iff (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (1 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) M C ↔
      1 ≤ M ∧ 2 ≤ C := by
  constructor
  · intro h
    have hresources := (mem_feasible.mp h).2
    simp only [gatedCEProblem] at hresources
    omega
  · rintro ⟨hM, hC⟩
    apply mem_feasible.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro S
      rw [show gatedCEStepFun X t opCost opRisk write 1 S =
        budgetedGatedCETrainStep X t S opCost opRisk write by
          simp [gatedCEStepFun]]
      exact gatedCEObjective_budgetedGatedCETrainStep_le
        X t S opCost opRisk write
    · simpa [gatedCEProblem] using hM
    · simpa [gatedCEProblem] using hC

/-- Deterministic pessimistic value estimate: true controller value minus the
constant bias `1 / 2`. -/
noncomputable def gatedCEValueEstimate (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) : ℝ :=
  (gatedCEProblem X t opCost opRisk write).value S - 1 / 2

/-- The absolute pointwise value-estimate error is exactly `1 / 2`. -/
theorem gatedCEValueEstimate_error (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    |(gatedCEProblem X t opCost opRisk write).value S -
      gatedCEValueEstimate X t opCost opRisk write S| = 1 / 2 := by
  unfold gatedCEValueEstimate
  norm_num

/-- Exact feasible-successor error bound in the interface consumed by
`Hagi.Unified.GuardedRobustSelection.guardedRobustNext`; feasibility is explicit
and no probability is involved. -/
theorem gatedCEValueEstimate_error_le (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) (M C : ℕ) (action : Fin 2)
    (_ha : action ∈ feasible (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) M C) :
    |(gatedCEProblem X t opCost opRisk write).value
        ((gatedCEProblem X t opCost opRisk write).step action S) -
      gatedCEValueEstimate X t opCost opRisk write
        ((gatedCEProblem X t opCost opRisk write).step action S)| ≤ 1 / 2 :=
  le_of_eq (gatedCEValueEstimate_error X t opCost opRisk write _)

end Hagi.Contracts.BudgetedGatedCE
