import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Unified.StepContract

/-!
# Nonnegative contract for the guarded Pareto batch transition

The actual budget-and-pointwise-CE guard permits both accepted training
steps and complete-state holds.  This adapter records its supplied-batch CE,
risk and resource-budget deltas in the ordinary nonnegative `StepContract`.
The operation cost and risk are abstract supplied inputs rather than physical
measurements.  Nothing here substitutes stored telemetry or parameter norms
for CE, or claims a held-out/optimal training result.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BudgetedParetoStepContract

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Hagi.Unified.StepCert

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Actual CE decrease, risk increment and resource-budget spend of the real
budgeted Pareto step.  Only a nonnegative supplied risk increment is needed:
the existing cost guard rejects negative or unaffordable cost, and holds
legitimately have all three deltas equal to zero. -/
noncomputable def budgetedParetoStepContract
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hOpRisk : 0 ≤ opRisk) :
    StepContract where
  decrease :=
    batchCEObjective X y S -
      batchCEObjective X y (budgetedParetoBatchTrainStep X y S opCost opRisk write)
  riskCost :=
    (budgetedParetoBatchTrainStep X y S opCost opRisk write).saf.risk - S.saf.risk
  budgetSpend :=
    S.res.budget - (budgetedParetoBatchTrainStep X y S opCost opRisk write).res.budget
  hDecreasePos := sub_nonneg.mpr
    (batchCEObjective_budgetedParetoBatchTrainStep_le X y S opCost opRisk write)
  hRiskNonneg := by
    classical
    by_cases h : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
        batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
          batchSampleCE X y b S
    · rw [budgetedParetoBatchTrainStep_of_active X y S opCost opRisk write h,
        batchTrainStep, trainStep_risk, batchTrainInput]
      linarith
    · rw [budgetedParetoBatchTrainStep_of_inactive X y S opCost opRisk write h]
      simp
  hBudgetNonneg := by
    classical
    by_cases h : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
        batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
          batchSampleCE X y b S
    · rw [budgetedParetoBatchTrainStep_of_active X y S opCost opRisk write h,
        batchTrainStep, trainStep_budget, batchTrainInput]
      linarith [h.1.1]
    · rw [budgetedParetoBatchTrainStep_of_inactive X y S opCost opRisk write h]
      simp

end Hagi.Contracts.BudgetedParetoStepContract
