import Hagi.Contracts.CEStepCertificate
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEExpansion
import Hagi.Model.CEHeldout
import Hagi.Unified.ParetoExecution
import Hagi.Contracts.BatchCEStepCore

/-!
# BatchCEBudgetGuard

Budgeted batch CE guard: sample CE basics, the generic guarded canonical transition, and the arbitrary-direction step. Split from `BatchCEStepCertificate` (C255).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BudgetedBatchCE

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Model.CEExpansion

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Exact one-sample CE inside the supplied finite batch, evaluated on the
actual current backbone parameters. -/
noncomputable def batchSampleCE (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (b : Fin B) (S : TrainState n a r c k) : ℝ :=
  Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S))

/-- Each sample supplies the inhabited vocabulary for one-target CE;
empty-batch cases do not pretend to have a sample. -/
theorem batchSampleCE_nonneg (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (b : Fin B) (S : TrainState n a r c k) :
    0 ≤ batchSampleCE X y b S := by
  let _ : Nonempty V := ⟨y b⟩
  exact Hagi.Model.CEHeldout.ceOneHot_nonneg _ _

/-- The empty batch keeps the previously established raw zero convention. -/
theorem emptyBatchCEObjective_zero
    (X : Fin 0 → Matrix V (Fin n) ℝ) (y : Fin 0 → V)
    (S : TrainState n a r c k) : batchCEObjective X y S = 0 := by
  exact (empty_batch_convention X (coreParameters S) y).1

/-- The arithmetic mean objective is nonnegative for every batch size; an
empty batch is handled without constructing a target that does not exist. -/
theorem batchCEObjective_nonneg (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) :
    0 ≤ batchCEObjective X y S := by
  cases B with
  | zero => rw [emptyBatchCEObjective_zero]
  | succ B =>
      let _ : Nonempty V := ⟨y 0⟩
      exact Hagi.Contracts.BatchCETrajectory.batchLoss_nonneg
        X (coreParameters S) y

/-- The canonical batch step is non-increasing in actual mean CE without an
extra nonempty-vocabulary premise. Positive range supplies a nonempty batch. -/
theorem batchCEObjective_batchTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    batchCEObjective X y (batchTrainStep X y S opCost opRisk write) ≤
      batchCEObjective X y S := by
  by_cases hR : batchRangeSquare X (coreParameters S) y = 0
  · rw [batchCEObjective_batchTrainStep_eq_of_rangeSquare_eq_zero
      X y S opCost opRisk write hR]
  · have hRpos : 0 < batchRangeSquare X (coreParameters S) y :=
      lt_of_le_of_ne (batchRangeSquare_nonneg X (coreParameters S) y)
        (Ne.symm hR)
    have hBpos : 0 < B :=
      batch_pos_of_rangeSquare_pos X (coreParameters S) y hRpos
    let _ : Nonempty V := ⟨y ⟨0, hBpos⟩⟩
    exact le_of_lt (batchCEObjective_batchTrainStep_lt
      X y S opCost opRisk write hRpos)

/-- Accept a current-state-dependent canonical transition only when its
actual cost is nonnegative and affordable and every supplied sample's CE
at the resulting parameters does not increase. Rejection returns `S`. -/
noncomputable def guardedBatchTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) : TrainState n a r c k :=
  if (0 ≤ (inputFor S).opCost ∧ (inputFor S).opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (trainStep S (inputFor S)) ≤ batchSampleCE X y b S then
    trainStep S (inputFor S)
  else
    S

/-- An admitted current-state input is executed through `trainStep`. -/
theorem guardedBatchTrainStep_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k)
    (h : (0 ≤ (inputFor S).opCost ∧ (inputFor S).opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (trainStep S (inputFor S)) ≤ batchSampleCE X y b S) :
    guardedBatchTrainStep X y inputFor S = trainStep S (inputFor S) := by
  exact ite_eq_left h

/-- In an admitted generic branch, the declared operation-cost ledger gain is
exactly the supplied input cost. -/
theorem guardedBatchTrainStep_flops_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k)
    (h : (0 ≤ (inputFor S).opCost ∧ (inputFor S).opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (trainStep S (inputFor S)) ≤ batchSampleCE X y b S) :
    (guardedBatchTrainStep X y inputFor S).res.flops =
      S.res.flops + (inputFor S).opCost := by
  rw [guardedBatchTrainStep_of_active X y inputFor S h, trainStep_flops]

/-- A rejected current-state input leaves the complete state unchanged. -/
theorem guardedBatchTrainStep_of_inactive
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k)
    (h : ¬ ((0 ≤ (inputFor S).opCost ∧ (inputFor S).opCost ≤ S.res.budget) ∧
      ∀ b, batchSampleCE X y b (trainStep S (inputFor S)) ≤
        batchSampleCE X y b S)) :
    guardedBatchTrainStep X y inputFor S = S := by
  exact ite_eq_right h

/-- The generic guard non-increases every supplied sample's actual CE. -/
theorem batchSampleCE_guardedBatchTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    batchSampleCE X y b (guardedBatchTrainStep X y inputFor S) ≤
      batchSampleCE X y b S := by
  by_cases h : (0 ≤ (inputFor S).opCost ∧ (inputFor S).opCost ≤ S.res.budget) ∧
      ∀ b, batchSampleCE X y b (trainStep S (inputFor S)) ≤
        batchSampleCE X y b S
  · rw [guardedBatchTrainStep_of_active X y inputFor S h]
    exact h.2 b
  · rw [guardedBatchTrainStep_of_inactive X y inputFor S h]

/-- Averaging the guarded component inequalities proves mean CE
non-regression, including the empty-batch division convention. -/
theorem batchCEObjective_guardedBatchTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    batchCEObjective X y (guardedBatchTrainStep X y inputFor S) ≤
      batchCEObjective X y S := by
  by_cases h : (0 ≤ (inputFor S).opCost ∧ (inputFor S).opCost ≤ S.res.budget) ∧
      ∀ b, batchSampleCE X y b (trainStep S (inputFor S)) ≤
        batchSampleCE X y b S
  · rw [guardedBatchTrainStep_of_active X y inputFor S h]
    unfold batchCEObjective batchLoss
    unfold Hagi.Probability.FiniteFamilyConfidence.empiricalMean
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg B)
    exact Finset.sum_le_sum (fun b _hb => h.2 b)
  · rw [guardedBatchTrainStep_of_inactive X y inputFor S h]

/-- Actual canonical accounting preserves a nonnegative initial budget. -/
theorem guardedBatchTrainStep_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (hbudget : 0 ≤ S.res.budget) :
    0 ≤ (guardedBatchTrainStep X y inputFor S).res.budget := by
  by_cases h : (0 ≤ (inputFor S).opCost ∧ (inputFor S).opCost ≤ S.res.budget) ∧
      ∀ b, batchSampleCE X y b (trainStep S (inputFor S)) ≤
        batchSampleCE X y b S
  · rw [guardedBatchTrainStep_of_active X y inputFor S h, trainStep_budget]
    exact sub_nonneg.mpr h.1.2
  · rw [guardedBatchTrainStep_of_inactive X y inputFor S h]
    exact hbudget

/-- The generic guarded canonical step preserves external quality telemetry. -/
theorem qual_guardedBatchTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    (guardedBatchTrainStep X y inputFor S).qual = S.qual := by
  by_cases h : (0 ≤ (inputFor S).opCost ∧ (inputFor S).opCost ≤ S.res.budget) ∧
      ∀ b, batchSampleCE X y b (trainStep S (inputFor S)) ≤
        batchSampleCE X y b S
  · rw [guardedBatchTrainStep_of_active X y inputFor S h,
      trainStep_quality_unchanged]
  · rw [guardedBatchTrainStep_of_inactive X y inputFor S h]

/-- The arbitrary-direction specialization of the existing generic
current-state guard from Cycle125c.  No second guard or transition is
introduced; the direction and all training fields are recomputed at `S`. -/
noncomputable def batchDirectionTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  guardedBatchTrainStep X y
    (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S

/-- The generic pointwise guard protects every supplied sample, including
when the totalized direction certificate fails and selects zero eta. -/
theorem batchSampleCE_batchDirectionTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    batchSampleCE X y b (batchDirectionTrainStep X y D S opCost opRisk write) ≤
      batchSampleCE X y b S :=
  batchSampleCE_guardedBatchTrainStep_le X y
    (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S b

/-- The guarded arbitrary-direction transition non-increases actual supplied-
batch mean CE, including the totalized empty-batch convention. -/
theorem batchCEObjective_batchDirectionTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    batchCEObjective X y (batchDirectionTrainStep X y D S opCost opRisk write) ≤
      batchCEObjective X y S :=
  batchCEObjective_guardedBatchTrainStep_le X y
    (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S

/-- Canonical accounting under the existing guard preserves a nonnegative
initial declared budget. -/
theorem batchDirectionTrainStep_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hbudget : 0 ≤ S.res.budget) :
    0 ≤ (batchDirectionTrainStep X y D S opCost opRisk write).res.budget :=
  guardedBatchTrainStep_budget_nonneg X y
    (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S hbudget

/-- The arbitrary-direction specialization preserves stored external quality
telemetry; this is not a claim that training improves that telemetry. -/
theorem qual_batchDirectionTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (batchDirectionTrainStep X y D S opCost opRisk write).qual = S.qual :=
  qual_guardedBatchTrainStep X y
    (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S

/-- Nonnegative affordable cost and the current negative-derivative
certificate admit the canonical arbitrary-direction candidate.  Strict
model-level CE descent supplies the guard's nonincrease premise. -/
theorem batchDirectionTrainStep_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0) :
    batchDirectionTrainStep X y D S opCost opRisk write =
      trainStep S (batchDirectionTrainInput X y D S opCost opRisk write) := by
  let _ : Nonempty (Fin B) := hcert.1
  apply guardedBatchTrainStep_of_active
  refine ⟨hcost, ?_⟩
  intro b
  change Hagi.ceOneHot (y b) (ceLogits (X b)
      (coreParameters (trainStep S
        (batchDirectionTrainInput X y D S opCost opRisk write)))) ≤
    Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S))
  rw [coreParameters_trainStep_batchDirectionTrainInput]
  exact (ceOneHot_batchDirectionNextParameters_lt
    X (coreParameters S) y (D S) hcert.2 b).le

/-- Failure of the nonnegative/affordable cost condition rejects the complete
candidate through the generic guard, independently of the direction. -/
theorem batchDirectionTrainStep_of_inactive
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ¬ (0 ≤ opCost ∧ opCost ≤ S.res.budget)) :
    batchDirectionTrainStep X y D S opCost opRisk write = S := by
  apply guardedBatchTrainStep_of_inactive
  intro h
  exact hcost h.1

/-- After admission, canonical execution has exactly the model-level
arbitrary-direction parameters at the same current state. -/
theorem coreParameters_batchDirectionTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0) :
    coreParameters (batchDirectionTrainStep X y D S opCost opRisk write) =
      batchDirectionNextParameters X (coreParameters S) y (D S) := by
  rw [batchDirectionTrainStep_of_active X y D S opCost opRisk write hcost hcert]
  exact coreParameters_trainStep_batchDirectionTrainInput
    X y D S opCost opRisk write

/-- Under feasible cost and the complete current certificate, every supplied
sample's actual CE strictly decreases after guarded execution. -/
theorem batchSampleCE_batchDirectionTrainStep_lt
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0) (b : Fin B) :
    batchSampleCE X y b (batchDirectionTrainStep X y D S opCost opRisk write) <
      batchSampleCE X y b S := by
  let _ : Nonempty (Fin B) := hcert.1
  rw [batchDirectionTrainStep_of_active X y D S opCost opRisk write hcost hcert]
  change Hagi.ceOneHot (y b) (ceLogits (X b)
      (coreParameters (trainStep S
        (batchDirectionTrainInput X y D S opCost opRisk write)))) <
    Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S))
  rw [coreParameters_trainStep_batchDirectionTrainInput]
  exact ceOneHot_batchDirectionNextParameters_lt
    X (coreParameters S) y (D S) hcert.2 b

/-- The same feasible-cost/current-certificate hypotheses give strict actual
arithmetic-mean CE descent, transported directly from BatchCEDescent. -/
theorem batchCEObjective_batchDirectionTrainStep_lt
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0) :
    batchCEObjective X y (batchDirectionTrainStep X y D S opCost opRisk write) <
      batchCEObjective X y S := by
  let _ : Nonempty (Fin B) := hcert.1
  rw [batchDirectionTrainStep_of_active X y D S opCost opRisk write hcost hcert]
  rw [batchCEObjective, batchCEObjective,
    coreParameters_trainStep_batchDirectionTrainInput]
  exact batchLoss_batchDirectionNextParameters_lt
    X (coreParameters S) y (D S) hcert.2

/-- With nonnegative affordable cost, the actual guarded arbitrary-direction
step decreases each supplied sample's CE by at least its current local margin.
Without the full derivative certificate the margin vanishes and the existing
generic guard still supplies nonincrease; no whole-state fallback is asserted. -/
theorem batchSampleCE_batchDirectionTrainStep_le_margin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) (b : Fin B) :
    batchSampleCE X y b (batchDirectionTrainStep X y D S opCost opRisk write) ≤
      batchSampleCE X y b S -
        batchDirectionMargin X (coreParameters S) y (D S) b := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0
  · let _ : Nonempty (Fin B) := hcert.1
    rw [batchDirectionTrainStep_of_active X y D S opCost opRisk write hcost hcert]
    change Hagi.ceOneHot (y b) (ceLogits (X b)
        (coreParameters (trainStep S
          (batchDirectionTrainInput X y D S opCost opRisk write)))) ≤
      Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S)) -
        batchDirectionMargin X (coreParameters S) y (D S) b
    rw [coreParameters_trainStep_batchDirectionTrainInput]
    exact ceOneHot_batchDirectionNextParameters_le_margin
      X (coreParameters S) y (D S) b
  · have hmargin : batchDirectionMargin X (coreParameters S) y (D S) b = 0 := by
      simp [batchDirectionMargin,
        batchDirectionSafeEta_eq_zero X (coreParameters S) y (D S) hcert]
    rw [hmargin, sub_zero]
    exact batchSampleCE_batchDirectionTrainStep_le
      X y D S opCost opRisk write b

/-- The actual guarded arbitrary-direction step also decreases arithmetic-mean
CE by at least the arithmetic mean of the current local margins. The same
feasible-cost premise is retained uniformly; zero-denominator and failed
certificate cases need only nonincrease. -/
theorem batchCEObjective_batchDirectionTrainStep_le_margin_sum
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    batchCEObjective X y (batchDirectionTrainStep X y D S opCost opRisk write) ≤
      batchCEObjective X y S -
        (∑ b, batchDirectionMargin X (coreParameters S) y (D S) b) / (B : ℝ) := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0
  · let _ : Nonempty (Fin B) := hcert.1
    rw [batchDirectionTrainStep_of_active X y D S opCost opRisk write hcost hcert]
    rw [batchCEObjective, batchCEObjective,
      coreParameters_trainStep_batchDirectionTrainInput]
    exact batchLoss_batchDirectionNextParameters_le_margin_sum
      X (coreParameters S) y (D S)
  · have hsum : (∑ b, batchDirectionMargin X (coreParameters S) y (D S) b) = 0 := by
      apply Finset.sum_eq_zero
      intro b _hb
      simp [batchDirectionMargin,
        batchDirectionSafeEta_eq_zero X (coreParameters S) y (D S) hcert]
    rw [hsum, zero_div, sub_zero]
    exact batchCEObjective_batchDirectionTrainStep_le
      X y D S opCost opRisk write

/-- Accepted arbitrary-direction execution adds exactly the abstract supplied
`opCost`; direction selection, certificate checks and CE evaluation are not
silently included in this declared ledger increment. -/
theorem batchDirectionTrainStep_flops_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0) :
    (batchDirectionTrainStep X y D S opCost opRisk write).res.flops =
      S.res.flops + opCost := by
  rw [batchDirectionTrainStep_of_active X y D S opCost opRisk write hcost hcert,
    trainStep_flops]
  rfl

/-- Without the complete current certificate the arbitrary-direction step
preserves backbone weights on both guard branches.  An admitted zero-eta
candidate can still update optimizer state and spend its supplied cost; no
complete-state fallback or unspent-budget assertion is made here. -/
theorem coreParameters_batchDirectionTrainStep_eq_of_not_certificate
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcert : ¬ (Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0)) :
    coreParameters (batchDirectionTrainStep X y D S opCost opRisk write) =
      coreParameters S := by
  by_cases h : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b
        (trainStep S (batchDirectionTrainInput X y D S opCost opRisk write)) ≤
      batchSampleCE X y b S
  · rw [batchDirectionTrainStep, guardedBatchTrainStep_of_active X y
      (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S h,
      coreParameters_trainStep_batchDirectionTrainInput]
    exact batchDirectionNextParameters_eq_zero
      X (coreParameters S) y (D S) hcert
  · rw [batchDirectionTrainStep, guardedBatchTrainStep_of_inactive X y
      (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S h]

