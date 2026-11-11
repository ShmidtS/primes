import Hagi.Contracts.BatchCEStepCertificate

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BudgetedParetoStepCert

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Hagi.Contracts.CEStep
open Hagi.Unified.HonestTransition Hagi.Unified.CertifiedLoop

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Lift the existing strict arithmetic-mean CE certificate to a genuinely
admitted guarded budgeted Pareto successor. The full guard premise excludes
its rejected full-state holds; positive range proves a nonempty batch,
hence supplies vocabulary nonempty through the supplied labels. -/
noncomputable def budgetedParetoStepCert
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (floor : QualityVector) (riskLim : ℝ)
    (hR : 0 < batchRangeSquare X (coreParameters S) y)
    (hOpRisk : 0 ≤ opRisk) (hRiskLim : opRisk ≤ riskLim)
    (hFloor : FloorHeld S floor)
    (hActive : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
        batchSampleCE X y b S) :
    StepCert (batchCEObjective X y) trainMeasured floor riskLim S
      (budgetedParetoBatchTrainStep X y S opCost opRisk write)
      S.res.budget (budgetedParetoBatchTrainStep X y S opCost opRisk write).res.budget := by
  have hBpos : 0 < B :=
    batch_pos_of_rangeSquare_pos X (coreParameters S) y hR
  let _ : Inhabited V := ⟨y ⟨0, hBpos⟩⟩
  let base := batchTrainStepCert X y S opCost opRisk write floor riskLim hR
    hOpRisk hActive.1.1 hRiskLim hFloor hActive.1.2
  refine
    { riskSpend := opRisk
      budgetSpend := opCost
      trans := ?_
      hriskSpend_nn := hOpRisk
      hbudgetSpend_nn := hActive.1.1
      hdec := ?_
      quality := ?_ }
  · rw [budgetedParetoBatchTrainStep_of_active X y S opCost opRisk write hActive]
    exact base.trans
  · rw [budgetedParetoBatchTrainStep_of_active X y S opCost opRisk write hActive]
    exact base.hdec
  · rw [budgetedParetoBatchTrainStep_of_active X y S opCost opRisk write hActive]
    exact base.quality

end Hagi.Contracts.BudgetedParetoStepCert
