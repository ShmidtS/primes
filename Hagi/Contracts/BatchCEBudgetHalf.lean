import Hagi.Contracts.CEStepCertificate
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEExpansion
import Hagi.Model.CEHeldout
import Hagi.Unified.ParetoExecution
import Hagi.Contracts.BatchCEBudgetGuard

/-!
# BatchCEBudgetHalf

Budgeted batch CE half-window and minimum-norm guarded steps. Split from `BatchCEStepCertificate` (C255).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BudgetedBatchCE

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Model.CEExpansion

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Current-state arbitrary direction with the common half-window computed
before any cap, as an input to the same existing guarded canonical transition. -/
noncomputable def batchDirectionHalfTrainInput
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainingInput n c where
  grad j := (-D S).ofLp j
  eta := batchDirectionHalfEta X (coreParameters S) y (D S)
  opCost := opCost
  opRisk := opRisk
  write := write

/-- Canonical execution of the half-window input gives exactly its model-
level direction update at the same current state. -/
theorem coreParameters_trainStep_batchDirectionHalfTrainInput
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    coreParameters (trainStep S
      (batchDirectionHalfTrainInput X y D S opCost opRisk write)) =
      batchDirectionHalfNextParameters X (coreParameters S) y (D S) := by
  apply PiLp.ext
  intro j
  change S.model.weights j -
      batchDirectionHalfEta X (coreParameters S) y (D S) * (-D S).ofLp j =
    S.model.weights j + batchDirectionHalfEta X (coreParameters S) y (D S) *
      (D S).ofLp j
  change S.model.weights j -
      batchDirectionHalfEta X (coreParameters S) y (D S) * -(D S).ofLp j =
    S.model.weights j + batchDirectionHalfEta X (coreParameters S) y (D S) *
      (D S).ofLp j
  ring

/-- Execute the half-window candidate through the existing generic guard,
not through a new acceptance predicate or alternate state update. -/
noncomputable def batchDirectionHalfTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  guardedBatchTrainStep X y
    (fun S => batchDirectionHalfTrainInput X y D S opCost opRisk write) S

/-- Nonnegative affordable current cost and the complete derivative
certificate make the generic guard admit the stronger half-window candidate. -/
theorem batchDirectionHalfTrainStep_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0) :
    batchDirectionHalfTrainStep X y D S opCost opRisk write =
      trainStep S (batchDirectionHalfTrainInput X y D S opCost opRisk write) := by
  let _ : Nonempty (Fin B) := hcert.1
  apply guardedBatchTrainStep_of_active
  refine ⟨hcost, ?_⟩
  intro b
  change Hagi.ceOneHot (y b) (ceLogits (X b)
      (coreParameters (trainStep S
        (batchDirectionHalfTrainInput X y D S opCost opRisk write)))) ≤
    Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S))
  rw [coreParameters_trainStep_batchDirectionHalfTrainInput]
  exact (ceOneHot_batchDirectionHalfNextParameters_lt
    X (coreParameters S) y (D S) hcert.2 b).le

/-- Every actual guarded half-window successor is samplewise nonincreasing,
including totalized empty-batch and rejected-candidate cases. -/
theorem batchSampleCE_batchDirectionHalfTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    batchSampleCE X y b (batchDirectionHalfTrainStep X y D S opCost opRisk write) ≤
      batchSampleCE X y b S :=
  batchSampleCE_guardedBatchTrainStep_le X y
    (fun S => batchDirectionHalfTrainInput X y D S opCost opRisk write) S b

theorem batchCEObjective_batchDirectionHalfTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    batchCEObjective X y (batchDirectionHalfTrainStep X y D S opCost opRisk write) ≤
      batchCEObjective X y S :=
  batchCEObjective_guardedBatchTrainStep_le X y
    (fun S => batchDirectionHalfTrainInput X y D S opCost opRisk write) S

theorem batchDirectionHalfTrainStep_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hbudget : 0 ≤ S.res.budget) :
    0 ≤ (batchDirectionHalfTrainStep X y D S opCost opRisk write).res.budget :=
  guardedBatchTrainStep_budget_nonneg X y
    (fun S => batchDirectionHalfTrainInput X y D S opCost opRisk write) S hbudget

/-- With legal current cost, actual execution lowers each sample's CE by at
least the full new quadratic margin.  A failed derivative certificate zeroes
the margin but does not by itself assert a whole-TrainState hold. -/
theorem batchSampleCE_batchDirectionHalfTrainStep_le_quadraticMargin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) (b : Fin B) :
    batchSampleCE X y b (batchDirectionHalfTrainStep X y D S opCost opRisk write) ≤
      batchSampleCE X y b S -
        batchDirectionQuadraticMargin X (coreParameters S) y (D S)
          (batchDirectionHalfEta X (coreParameters S) y (D S)) b := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0
  · let _ : Nonempty (Fin B) := hcert.1
    rw [batchDirectionHalfTrainStep_of_active X y D S opCost opRisk write hcost hcert]
    change Hagi.ceOneHot (y b) (ceLogits (X b)
        (coreParameters (trainStep S
          (batchDirectionHalfTrainInput X y D S opCost opRisk write)))) ≤
      Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S)) -
        batchDirectionQuadraticMargin X (coreParameters S) y (D S)
          (batchDirectionHalfEta X (coreParameters S) y (D S)) b
    rw [coreParameters_trainStep_batchDirectionHalfTrainInput]
    exact ceOneHot_batchDirectionHalfNextParameters_le_quadraticMargin
      X (coreParameters S) y (D S) b
  · have hmargin :
        batchDirectionQuadraticMargin X (coreParameters S) y (D S)
          (batchDirectionHalfEta X (coreParameters S) y (D S)) b = 0 := by
      simp [batchDirectionQuadraticMargin,
        batchDirectionHalfEta_eq_zero X (coreParameters S) y (D S) hcert]
    rw [hmargin, sub_zero]
    exact batchSampleCE_batchDirectionHalfTrainStep_le
      X y D S opCost opRisk write b

theorem batchCEObjective_batchDirectionHalfTrainStep_le_quadraticMargin_sum
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    batchCEObjective X y (batchDirectionHalfTrainStep X y D S opCost opRisk write) ≤
      batchCEObjective X y S -
        (∑ b, batchDirectionQuadraticMargin X (coreParameters S) y (D S)
          (batchDirectionHalfEta X (coreParameters S) y (D S)) b) / (B : ℝ) := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0
  · let _ : Nonempty (Fin B) := hcert.1
    rw [batchDirectionHalfTrainStep_of_active X y D S opCost opRisk write hcost hcert]
    rw [batchCEObjective, batchCEObjective,
      coreParameters_trainStep_batchDirectionHalfTrainInput]
    exact batchLoss_batchDirectionHalfNextParameters_le_quadraticMargin_sum
      X (coreParameters S) y (D S)
  · have hsum :
        (∑ b, batchDirectionQuadraticMargin X (coreParameters S) y (D S)
          (batchDirectionHalfEta X (coreParameters S) y (D S)) b) = 0 := by
      apply Finset.sum_eq_zero
      intro b _hb
      simp [batchDirectionQuadraticMargin,
        batchDirectionHalfEta_eq_zero X (coreParameters S) y (D S) hcert]
    rw [hsum, zero_div, sub_zero]
    exact batchCEObjective_batchDirectionHalfTrainStep_le
      X y D S opCost opRisk write

/-- An accepted half-window transition has the same declared abstract cost
increment as the canonical transition.  D selection and guard checks are not
falsely absorbed into this increment. -/
theorem batchDirectionHalfTrainStep_flops_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0) :
    (batchDirectionHalfTrainStep X y D S opCost opRisk write).res.flops =
      S.res.flops + opCost := by
  rw [batchDirectionHalfTrainStep_of_active X y D S opCost opRisk write hcost hcert,
    trainStep_flops]
  rfl

/-- Without the derivative certificate the half-window still leaves the
backbone parameters unchanged on either guard branch.  The optimizer, memory
and declared ledger need not be unchanged if a zero-eta candidate is accepted. -/
theorem coreParameters_batchDirectionHalfTrainStep_eq_of_not_certificate
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcert : ¬ (Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) (coreParameters S) (y b) (D S) < 0)) :
    coreParameters (batchDirectionHalfTrainStep X y D S opCost opRisk write) =
      coreParameters S := by
  by_cases h : (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b
        (trainStep S (batchDirectionHalfTrainInput X y D S opCost opRisk write)) ≤
      batchSampleCE X y b S
  · rw [batchDirectionHalfTrainStep, guardedBatchTrainStep_of_active X y
      (fun S => batchDirectionHalfTrainInput X y D S opCost opRisk write) S h,
      coreParameters_trainStep_batchDirectionHalfTrainInput]
    exact batchDirectionHalfNextParameters_eq_zero
      X (coreParameters S) y (D S) hcert
  · rw [batchDirectionHalfTrainStep, guardedBatchTrainStep_of_inactive X y
      (fun S => batchDirectionHalfTrainInput X y D S opCost opRisk write) S h]

/-- The minimum-norm candidate uses the existing current-state guard; no
second acceptance predicate or alternate state transition is introduced. -/
noncomputable def batchMinimumNormTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  guardedBatchTrainStep X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S

/-- Nonnegative affordable cost admits the minimum-norm canonical candidate:
Cycle124 already supplies every component CE comparison. -/
theorem batchMinimumNormTrainStep_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    batchMinimumNormTrainStep X y S opCost opRisk write =
      trainStep S (batchMinimumNormTrainInput X y S opCost opRisk write) := by
  apply guardedBatchTrainStep_of_active
  refine ⟨hcost, ?_⟩
  intro b
  change Hagi.ceOneHot (y b) (ceLogits (X b)
      (coreParameters (trainStep S
        (batchMinimumNormTrainInput X y S opCost opRisk write)))) ≤
    Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S))
  rw [coreParameters_trainStep_batchMinimumNormTrainInput]
  exact ceOneHot_batchCommonNextParameters_le X (coreParameters S) y b

/-- Failure of the nonnegative/affordable cost conjunction rejects the whole
candidate and returns the complete old state. -/
theorem batchMinimumNormTrainStep_of_inactive
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ¬ (0 ≤ opCost ∧ opCost ≤ S.res.budget)) :
    batchMinimumNormTrainStep X y S opCost opRisk write = S := by
  apply guardedBatchTrainStep_of_inactive
  intro h
  exact hcost h.1

/-- The guarded minimum-norm transition non-increases every supplied-sample
CE, whether it is admitted or rejected. -/
theorem batchSampleCE_batchMinimumNormTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    batchSampleCE X y b (batchMinimumNormTrainStep X y S opCost opRisk write) ≤
      batchSampleCE X y b S :=
  batchSampleCE_guardedBatchTrainStep_le X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S b

/-- The guarded minimum-norm transition non-increases actual supplied-batch
mean CE, including the totalized empty-batch convention. -/
theorem batchCEObjective_batchMinimumNormTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    batchCEObjective X y (batchMinimumNormTrainStep X y S opCost opRisk write) ≤
      batchCEObjective X y S :=
  batchCEObjective_guardedBatchTrainStep_le X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S

/-- Canonical accounting under the existing guard preserves a nonnegative
initial declared budget. -/
theorem batchMinimumNormTrainStep_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hbudget : 0 ≤ S.res.budget) :
    0 ≤ (batchMinimumNormTrainStep X y S opCost opRisk write).res.budget :=
  guardedBatchTrainStep_budget_nonneg X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S hbudget

/-- The minimum-norm specialization preserves external quality telemetry. -/
theorem qual_batchMinimumNormTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (batchMinimumNormTrainStep X y S opCost opRisk write).qual = S.qual :=
  qual_guardedBatchTrainStep X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S

/-- After an admitted guarded step, the actual current backbone parameters
are exactly Cycle124's common minimum-norm update. -/
theorem coreParameters_batchMinimumNormTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    coreParameters (batchMinimumNormTrainStep X y S opCost opRisk write) =
      batchCommonNextParameters X (coreParameters S) y := by
  rw [batchMinimumNormTrainStep_of_active X y S opCost opRisk write hcost]
  exact coreParameters_trainStep_batchMinimumNormTrainInput
    X y S opCost opRisk write

/-- At a nonzero minimum-norm point, an admitted guarded step strictly
decreases every supplied-sample CE by the actual Cycle124 comparison. -/
theorem batchSampleCE_batchMinimumNormTrainStep_lt
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hω : batchGradientMinimizer X (coreParameters S) y ≠ 0) (b : Fin B) :
    batchSampleCE X y b (batchMinimumNormTrainStep X y S opCost opRisk write) <
      batchSampleCE X y b S := by
  rw [batchMinimumNormTrainStep_of_active X y S opCost opRisk write hcost]
  change Hagi.ceOneHot (y b) (ceLogits (X b)
      (coreParameters (trainStep S
        (batchMinimumNormTrainInput X y S opCost opRisk write)))) <
    Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S))
  rw [coreParameters_trainStep_batchMinimumNormTrainInput]
  exact ceOneHot_batchCommonNextParameters_lt X (coreParameters S) y hω b

/-- Strict component descent and a positive finite denominator give strict
actual mean CE descent; no strict assertion is made at zero direction. -/
theorem batchCEObjective_batchMinimumNormTrainStep_lt
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hω : batchGradientMinimizer X (coreParameters S) y ≠ 0) :
    batchCEObjective X y (batchMinimumNormTrainStep X y S opCost opRisk write) <
      batchCEObjective X y S := by
  let _ : Nonempty (Fin B) :=
    nonempty_fin_batch_of_minimizer_ne_zero X (coreParameters S) y hω
  obtain ⟨b0⟩ := (inferInstance : Nonempty (Fin B))
  let _ : Nonempty V := ⟨y b0⟩
  have hB : 0 < B := by
    by_contra h
    have hB0 : B = 0 := Nat.eq_zero_of_not_pos h
    subst B
    exact Fin.elim0 b0
  unfold batchCEObjective batchLoss
  unfold Hagi.Probability.FiniteFamilyConfidence.empiricalMean
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr hB)
  exact Finset.sum_lt_sum
    (fun b _hb =>
      (batchSampleCE_batchMinimumNormTrainStep_lt
        X y S opCost opRisk write hcost hω b).le)
    ⟨b0, Finset.mem_univ b0,
      batchSampleCE_batchMinimumNormTrainStep_lt
        X y S opCost opRisk write hcost hω b0⟩

/-- An admitted guarded minimum-norm step adds exactly the abstract supplied
operation cost to the canonical declared-flops ledger. -/
theorem batchMinimumNormTrainStep_flops_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    (batchMinimumNormTrainStep X y S opCost opRisk write).res.flops =
      S.res.flops + opCost := by
  rw [batchMinimumNormTrainStep_of_active X y S opCost opRisk write hcost,
    trainStep_flops]
  rfl


end Hagi.Contracts.BudgetedBatchCE
