import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Unified.GuardedRobustTrajectory
import Hagi.Contracts.BatchCETrajectoryFixtures

/-!
# BatchCETrajectoryGuardedInput

Guarded input-path abstraction `guardedBatchInputPath*`: per-sample and objective antitonicity, convergence, and budget accounting.
-/

set_option relaxedAutoImplicit false


namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- All direct current-state guarded inputs share the same actual recursive
path. Selection of an input remains separate from the existing guard. -/
noncomputable def guardedBatchInputPath (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) : ℕ → TrainState n a r c k
  | 0 => S
  | t + 1 => guardedBatchTrainStep X y inputFor
      (guardedBatchInputPath X y inputFor S t)

@[simp] theorem guardedBatchInputPath_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) : guardedBatchInputPath X y inputFor S 0 = S := rfl

@[simp] theorem guardedBatchInputPath_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (t : ℕ) :
    guardedBatchInputPath X y inputFor S (t + 1) =
      guardedBatchTrainStep X y inputFor (guardedBatchInputPath X y inputFor S t) := rfl

theorem guardedBatchInputPath_sampleCE_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    Antitone (fun t => batchSampleCE X y b (guardedBatchInputPath X y inputFor S t)) := by
  apply antitone_nat_of_succ_le
  intro t
  exact batchSampleCE_guardedBatchTrainStep_le X y inputFor
    (guardedBatchInputPath X y inputFor S t) b

theorem guardedBatchInputPath_objective_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    Antitone (fun t => batchCEObjective X y (guardedBatchInputPath X y inputFor S t)) := by
  apply antitone_nat_of_succ_le
  intro t
  exact batchCEObjective_guardedBatchTrainStep_le X y inputFor
    (guardedBatchInputPath X y inputFor S t)

theorem guardedBatchInputPath_sampleCE_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    Tendsto (fun t => batchSampleCE X y b (guardedBatchInputPath X y inputFor S t))
      atTop (𝓝 (⨅ t, batchSampleCE X y b
        (guardedBatchInputPath X y inputFor S t))) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (guardedBatchInputPath_sampleCE_antitone X y inputFor S b)
      (fun t => batchSampleCE_nonneg X y b (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_objective_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    Tendsto (fun t => batchCEObjective X y (guardedBatchInputPath X y inputFor S t))
      atTop (𝓝 (⨅ t, batchCEObjective X y (guardedBatchInputPath X y inputFor S t))) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (guardedBatchInputPath_objective_antitone X y inputFor S)
      (fun t => batchCEObjective_nonneg X y (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_sampleCE_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    0 ≤ ⨅ t, batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) :=
  ObjectiveTrajectory.ciInf_nonneg _
    (fun t => batchSampleCE_nonneg X y b (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_objective_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    0 ≤ ⨅ t, batchCEObjective X y (guardedBatchInputPath X y inputFor S t) :=
  ObjectiveTrajectory.ciInf_nonneg _
    (fun t => batchCEObjective_nonneg X y (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (hbudget : 0 ≤ S.res.budget) :
    ∀ t, 0 ≤ (guardedBatchInputPath X y inputFor S t).res.budget := by
  intro t
  induction t with
  | zero => exact hbudget
  | succ t ih => exact guardedBatchTrainStep_budget_nonneg X y inputFor _ ih

/-- A single local actual-margin law produces all finite/infinite sample CE
margin budgets for every direct guarded-input policy. -/
theorem guardedBatchInputPath_margin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k)
    (margin : Fin B → TrainState n a r c k → ℝ)
    (hmargin : ∀ b (T : TrainState n a r c k), 0 ≤ margin b T)
    (hbound : ∀ (T : TrainState n a r c k),
      0 ≤ (inputFor T).opCost ∧ (inputFor T).opCost ≤ T.res.budget →
        ∀ b, batchSampleCE X y b (guardedBatchTrainStep X y inputFor T) ≤
          batchSampleCE X y b T - margin b T)
    (hcost : ∀ t, 0 ≤ (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ∧
      (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ≤
        (guardedBatchInputPath X y inputFor S t).res.budget)
    (b : Fin B) :
    (∀ T, ∑ t ∈ Finset.range T,
        margin b (guardedBatchInputPath X y inputFor S t) ≤ batchSampleCE X y b S) ∧
      Summable (fun t => margin b (guardedBatchInputPath X y inputFor S t)) ∧
      Tendsto (fun t => margin b (guardedBatchInputPath X y inputFor S t)) atTop (𝓝 0) ∧
      ∑' t, margin b (guardedBatchInputPath X y inputFor S t) ≤ batchSampleCE X y b S := by
  have hle (t : ℕ) : margin b (guardedBatchInputPath X y inputFor S t) ≤
      batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) -
        batchSampleCE X y b (guardedBatchInputPath X y inputFor S (t + 1)) := by
    have h := hbound (guardedBatchInputPath X y inputFor S t) (hcost t) b
    rw [guardedBatchInputPath_succ]
    linarith
  have hfinite (T : ℕ) : ∑ t ∈ Finset.range T,
      margin b (guardedBatchInputPath X y inputFor S t) ≤ batchSampleCE X y b S := by
    calc
      ∑ t ∈ Finset.range T, margin b (guardedBatchInputPath X y inputFor S t) ≤
        batchSampleCE X y b (guardedBatchInputPath X y inputFor S 0) -
          batchSampleCE X y b (guardedBatchInputPath X y inputFor S T) :=
        ObjectiveTrajectory.sum_drop_le_initial_sub _ _ T (fun t => hle t)
      _ ≤ batchSampleCE X y b (guardedBatchInputPath X y inputFor S 0) :=
        sub_le_self _ (batchSampleCE_nonneg X y b (guardedBatchInputPath X y inputFor S T))
      _ = batchSampleCE X y b S := rfl
  have hsummable : Summable
      (fun t => margin b (guardedBatchInputPath X y inputFor S t)) :=
    summable_of_sum_range_le (fun t => hmargin b _) hfinite
  exact ⟨hfinite, hsummable, hsummable.tendsto_atTop_zero,
    hsummable.tsum_le_of_sum_range_le hfinite⟩

/-- The averaged counterpart of a generic local sample-margin law.  The
only batch denominator is on the averaged current margin. -/
theorem guardedBatchInputPath_meanMargin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k)
    (margin : Fin B → TrainState n a r c k → ℝ)
    (hmargin : ∀ b (T : TrainState n a r c k), 0 ≤ margin b T)
    (hbound : ∀ (T : TrainState n a r c k),
      0 ≤ (inputFor T).opCost ∧ (inputFor T).opCost ≤ T.res.budget →
        ∀ b, batchSampleCE X y b (guardedBatchTrainStep X y inputFor T) ≤
          batchSampleCE X y b T - margin b T)
    (hcost : ∀ t, 0 ≤ (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ∧
      (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ≤
        (guardedBatchInputPath X y inputFor S t).res.budget) :
    (∀ T, ∑ t ∈ Finset.range T,
        ((∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ≤
          batchCEObjective X y S) ∧
      Summable (fun t => (∑ b,
        margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ∧
      Tendsto (fun t => (∑ b,
        margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ))
        atTop (𝓝 0) ∧
      ∑' t, (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) ≤
        batchCEObjective X y S := by
  have hsucc (t : ℕ) : batchCEObjective X y
        (guardedBatchInputPath X y inputFor S (t + 1)) ≤
      batchCEObjective X y (guardedBatchInputPath X y inputFor S t) -
        (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) := by
    have hsum : (∑ b, batchSampleCE X y b
          (guardedBatchInputPath X y inputFor S (t + 1))) ≤
        ∑ b, (batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) -
          margin b (guardedBatchInputPath X y inputFor S t)) := by
      exact Finset.sum_le_sum (fun b _hb => by
        simpa only [guardedBatchInputPath_succ] using
          hbound (guardedBatchInputPath X y inputFor S t) (hcost t) b)
    have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
    unfold batchCEObjective batchLoss
    unfold Hagi.Probability.FiniteFamilyConfidence.empiricalMean
    calc
      (∑ b, batchSampleCE X y b (guardedBatchInputPath X y inputFor S (t + 1))) /
          (B : ℝ) ≤
        (∑ b, (batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) -
          margin b (guardedBatchInputPath X y inputFor S t))) / (B : ℝ) := hdiv
      _ = (∑ b, batchSampleCE X y b (guardedBatchInputPath X y inputFor S t)) /
          (B : ℝ) -
        (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) := by
        rw [Finset.sum_sub_distrib, sub_div]
  have hle (t : ℕ) : (∑ b,
        margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) ≤
      batchCEObjective X y (guardedBatchInputPath X y inputFor S t) -
        batchCEObjective X y (guardedBatchInputPath X y inputFor S (t + 1)) := by
    have h := hsucc t
    linarith [hsucc t]
  have hfinite (T : ℕ) : ∑ t ∈ Finset.range T,
      ((∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ≤
        batchCEObjective X y S := by
    calc
      ∑ t ∈ Finset.range T, ((∑ b,
          margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ≤
        batchCEObjective X y (guardedBatchInputPath X y inputFor S 0) -
          batchCEObjective X y (guardedBatchInputPath X y inputFor S T) :=
        ObjectiveTrajectory.sum_drop_le_initial_sub _ _ T (fun t => hle t)
      _ ≤ batchCEObjective X y (guardedBatchInputPath X y inputFor S 0) :=
        sub_le_self _ (batchCEObjective_nonneg X y (guardedBatchInputPath X y inputFor S T))
      _ = batchCEObjective X y S := rfl
  have hsummable : Summable (fun t => (∑ b,
      margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) :=
    summable_of_sum_range_le (fun t => div_nonneg
      (Finset.sum_nonneg (fun b _hb => hmargin b _)) (Nat.cast_nonneg B)) hfinite
  exact ⟨hfinite, hsummable, hsummable.tendsto_atTop_zero,
    hsummable.tsum_le_of_sum_range_le hfinite⟩

noncomputable def directionBatchState (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : ℕ → TrainState n a r c k :=
  guardedBatchInputPath X y
    (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S

@[simp] theorem directionBatchState_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    directionBatchState X y D S opCost opRisk write 0 = S := rfl

@[simp] theorem directionBatchState_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    directionBatchState X y D S opCost opRisk write (t + 1) =
      batchDirectionTrainStep X y D
        (directionBatchState X y D S opCost opRisk write t) opCost opRisk write := rfl

/-- Actual sample CE and its current local guaranteed margin along the path. -/
noncomputable def directionBatchSampleCE (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) : ℝ :=
  batchSampleCE X y b (directionBatchState X y D S opCost opRisk write t)

noncomputable def directionBatchMargin (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) : ℝ :=
  batchDirectionMargin X
    (coreParameters (directionBatchState X y D S opCost opRisk write t)) y
      (D (directionBatchState X y D S opCost opRisk write t)) b

noncomputable def directionBatchObjective (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  batchCEObjective X y (directionBatchState X y D S opCost opRisk write t)

noncomputable def directionBatchMeanMargin (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  (∑ b, directionBatchMargin X y D S opCost opRisk write b t) / (B : ℝ)

end Hagi.Contracts.BatchCETrajectory
