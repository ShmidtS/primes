import Hagi.Contracts.CEStepCertificate
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEExpansion
import Hagi.Model.CEHeldout
import Hagi.Unified.ParetoExecution
import Hagi.Contracts.BatchCEBudgetHalf

/-!
# BatchCEBudgetPareto

Budgeted batch CE explicit pair step and the pointwise-budget Pareto guard. Split from `BatchCEStepCertificate` (C255).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BudgetedBatchCE

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Model.CEExpansion

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- The explicit two-sample input executed through the existing generic
current-state guard.  No second guard or replacement state is introduced. -/
noncomputable def batchPairMinimumNormTrainStep
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  guardedBatchTrainStep X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) S

/-- The explicit pair policy and the prior minimum-norm policy produce the
same complete guarded state, including both acceptance and rejection. -/
theorem batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    batchPairMinimumNormTrainStep X y S opCost opRisk write =
      batchMinimumNormTrainStep X y S opCost opRisk write := by
  unfold batchPairMinimumNormTrainStep batchMinimumNormTrainStep
  apply congrArg (fun inputFor => guardedBatchTrainStep X y inputFor S)
  funext T
  exact batchPairMinimumNormTrainInput_eq_batchMinimumNormTrainInput
    X y T opCost opRisk write

/-- An affordable nonnegative cost admits the explicit pair candidate through
the old minimum-norm acceptance theorem. -/
theorem batchPairMinimumNormTrainStep_of_active
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    batchPairMinimumNormTrainStep X y S opCost opRisk write =
      trainStep S (batchPairMinimumNormTrainInput X y S opCost opRisk write) := by
  calc
    batchPairMinimumNormTrainStep X y S opCost opRisk write =
        batchMinimumNormTrainStep X y S opCost opRisk write :=
      batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep
        X y S opCost opRisk write
    _ = trainStep S (batchMinimumNormTrainInput X y S opCost opRisk write) :=
      batchMinimumNormTrainStep_of_active X y S opCost opRisk write hcost
    _ = trainStep S (batchPairMinimumNormTrainInput X y S opCost opRisk write) := by
      rw [batchPairMinimumNormTrainInput_eq_batchMinimumNormTrainInput]

/-- Failure of the cost side of the generic guard rejects the whole pair
candidate, exactly as for the original minimum-norm candidate. -/
theorem batchPairMinimumNormTrainStep_of_inactive
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ¬ (0 ≤ opCost ∧ opCost ≤ S.res.budget)) :
    batchPairMinimumNormTrainStep X y S opCost opRisk write = S := by
  rw [batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep]
  exact batchMinimumNormTrainStep_of_inactive X y S opCost opRisk write hcost

/-- Every pair sample is nonincreasing under the guarded full transition. -/
theorem batchSampleCE_batchPairMinimumNormTrainStep_le
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin 2) :
    batchSampleCE X y b (batchPairMinimumNormTrainStep X y S opCost opRisk write) ≤
      batchSampleCE X y b S := by
  rw [batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep]
  exact batchSampleCE_batchMinimumNormTrainStep_le X y S opCost opRisk write b

/-- The explicit pair transition non-increases actual supplied-batch mean CE. -/
theorem batchCEObjective_batchPairMinimumNormTrainStep_le
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    batchCEObjective X y (batchPairMinimumNormTrainStep X y S opCost opRisk write) ≤
      batchCEObjective X y S := by
  rw [batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep]
  exact batchCEObjective_batchMinimumNormTrainStep_le X y S opCost opRisk write

/-- The pair transition inherits canonical nonnegative-budget preservation. -/
theorem batchPairMinimumNormTrainStep_budget_nonneg
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hbudget : 0 ≤ S.res.budget) :
    0 ≤ (batchPairMinimumNormTrainStep X y S opCost opRisk write).res.budget := by
  rw [batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep]
  exact batchMinimumNormTrainStep_budget_nonneg
    X y S opCost opRisk write hbudget

/-- The pair transition preserves stored external quality telemetry. -/
theorem qual_batchPairMinimumNormTrainStep
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (batchPairMinimumNormTrainStep X y S opCost opRisk write).qual = S.qual := by
  rw [batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep]
  exact qual_batchMinimumNormTrainStep X y S opCost opRisk write

/-- After acceptance, pair execution has the prior common minimum-norm
parameters.  This is the same update, not an additional optimizer result. -/
theorem coreParameters_batchPairMinimumNormTrainStep
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    coreParameters (batchPairMinimumNormTrainStep X y S opCost opRisk write) =
      batchCommonNextParameters X (coreParameters S) y := by
  rw [batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep]
  exact coreParameters_batchMinimumNormTrainStep X y S opCost opRisk write hcost

/-- At a nonzero prior minimizer, an accepted pair step strictly decreases
every supplied sample's CE. -/
theorem batchSampleCE_batchPairMinimumNormTrainStep_lt
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hω : batchGradientMinimizer X (coreParameters S) y ≠ 0) (b : Fin 2) :
    batchSampleCE X y b (batchPairMinimumNormTrainStep X y S opCost opRisk write) <
      batchSampleCE X y b S := by
  rw [batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep]
  exact batchSampleCE_batchMinimumNormTrainStep_lt
    X y S opCost opRisk write hcost hω b

/-- The same nonzero-minimizer and acceptance hypotheses give strict actual
mean CE descent for the explicit pair step. -/
theorem batchCEObjective_batchPairMinimumNormTrainStep_lt
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hω : batchGradientMinimizer X (coreParameters S) y ≠ 0) :
    batchCEObjective X y (batchPairMinimumNormTrainStep X y S opCost opRisk write) <
      batchCEObjective X y S := by
  rw [batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep]
  exact batchCEObjective_batchMinimumNormTrainStep_lt
    X y S opCost opRisk write hcost hω

/-- Accepted pair execution adds exactly its supplied abstract `opCost`; the
algebraic dual selection does not assert a physical FLOP reduction. -/
theorem batchPairMinimumNormTrainStep_flops_of_active
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    (batchPairMinimumNormTrainStep X y S opCost opRisk write).res.flops =
      S.res.flops + opCost := by
  rw [batchPairMinimumNormTrainStep_eq_batchMinimumNormTrainStep]
  exact batchMinimumNormTrainStep_flops_of_active X y S opCost opRisk write hcost

/-- Accept the canonical batch transition only if nonnegative supplied cost
fits declared budget and every finite-batch component does not increase. -/
noncomputable def budgetedParetoBatchTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  guardedBatchTrainStep X y
    (fun S => batchTrainInput X y S opCost opRisk write) S

/-- In the fully admitted branch, execute the complete canonical transition. -/
theorem budgetedParetoBatchTrainStep_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (h : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
        batchSampleCE X y b S) :
    budgetedParetoBatchTrainStep X y S opCost opRisk write =
      batchTrainStep X y S opCost opRisk write := by
  exact ite_eq_left h

/-- Any rejected budget or pointwise condition returns the whole input state. -/
theorem budgetedParetoBatchTrainStep_of_inactive
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (h : ¬ ((0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
        batchSampleCE X y b S)) :
    budgetedParetoBatchTrainStep X y S opCost opRisk write = S := by
  exact ite_eq_right h

/-- The guarded transition preserves every component CE of the supplied batch;
this is non-regression, not strict descent or a held-out guarantee. -/
theorem batchSampleCE_budgetedParetoBatchTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    batchSampleCE X y b (budgetedParetoBatchTrainStep X y S opCost opRisk write) ≤
      batchSampleCE X y b S := by
  by_cases h : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
        batchSampleCE X y b S
  · rw [budgetedParetoBatchTrainStep_of_active X y S opCost opRisk write h]
    exact h.2 b
  · rw [budgetedParetoBatchTrainStep_of_inactive X y S opCost opRisk write h]

/-- Actual batch-mean CE cannot increase under the pointwise-budget guard. -/
theorem batchCEObjective_budgetedParetoBatchTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    batchCEObjective X y (budgetedParetoBatchTrainStep X y S opCost opRisk write) ≤
      batchCEObjective X y S := by
  by_cases h : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
        batchSampleCE X y b S
  · rw [budgetedParetoBatchTrainStep_of_active X y S opCost opRisk write h]
    exact batchCEObjective_batchTrainStep_le X y S opCost opRisk write
  · rw [budgetedParetoBatchTrainStep_of_inactive X y S opCost opRisk write h]

/-- A nonnegative initial declared budget stays nonnegative; the per-sample
veto supplies an extra reason to stay without compromising this invariant. -/
theorem budgetedParetoBatchTrainStep_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hbudget : 0 ≤ S.res.budget) :
    0 ≤ (budgetedParetoBatchTrainStep X y S opCost opRisk write).res.budget := by
  by_cases h : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
        batchSampleCE X y b S
  · rw [budgetedParetoBatchTrainStep_of_active X y S opCost opRisk write h,
      batchTrainStep, trainStep_budget, batchTrainInput]
    exact sub_nonneg.mpr h.1.2
  · rw [budgetedParetoBatchTrainStep_of_inactive X y S opCost opRisk write h]
    exact hbudget

/-- The guarded canonical step preserves stored telemetry, not conflating it
with actual mean CE or any of the sample CE components. -/
theorem qual_budgetedParetoBatchTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (budgetedParetoBatchTrainStep X y S opCost opRisk write).qual = S.qual := by
  by_cases h : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
        batchSampleCE X y b S
  · rw [budgetedParetoBatchTrainStep_of_active X y S opCost opRisk write h]
    exact qual_batchTrainStep X y S opCost opRisk write
  · rw [budgetedParetoBatchTrainStep_of_inactive X y S opCost opRisk write h]


end Hagi.Contracts.BudgetedBatchCE
