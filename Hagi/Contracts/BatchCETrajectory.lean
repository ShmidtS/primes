import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Model.CEHeldout

/-!
# Repeated common-direction batch CE transitions

A fixed finite batch is re-evaluated after every actual `State.trainStep`.
The common residual and safe step therefore always use the successor's own
weights, rather than reusing stale first-step quantities.  Nonempty vocabulary
is enough for nonnegative CE and for the per-step majorizer.

The actual loss differences telescope and dominate the sum of certified
majorizer residuals.  Nonnegative CE and antitonicity imply convergence of the
loss values to their real infimum.  That infimum is not asserted to be zero,
to be a global optimum, or to make parameters or residuals converge.

The batch and ledger inputs are supplied and deterministic.  This is not an
IID, fresh-data, external-quality or hardware-compute theorem.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Nonnegative majorizer residual for the selected common batch step.  The
zero-range branch is literal zero; no positive certificate is fabricated. -/
noncomputable def batchCertifiedDrop (X : Fin B → Matrix V (Fin n) ℝ)
    (θ : EuclideanSpace ℝ (Fin n)) (y : Fin B → V) : ℝ :=
  if batchRangeSquare X θ y = 0 then 0
  else 2 * batchAlignment X θ y ^ 2 / batchRangeSquare X θ y

/-- Both branches of the certified residual are nonnegative. -/
theorem batchCertifiedDrop_nonneg (X : Fin B → Matrix V (Fin n) ℝ)
    (θ : EuclideanSpace ℝ (Fin n)) (y : Fin B → V) :
    0 ≤ batchCertifiedDrop X θ y := by
  rw [batchCertifiedDrop]
  split_ifs with hR
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (batchRangeSquare_nonneg X θ y)

/-- Actual CE on one fixed finite batch has the existing termwise nonnegative
bound.  Empty batches retain Lean's conventional raw mean zero. -/
theorem batchLoss_nonneg [Nonempty V] (X : Fin B → Matrix V (Fin n) ℝ)
    (θ : EuclideanSpace ℝ (Fin n)) (y : Fin B → V) :
    0 ≤ batchLoss X θ y := by
  unfold batchLoss Hagi.Probability.FiniteFamilyConfidence.empiricalMean
  exact div_nonneg (Finset.sum_nonneg fun _ _ => CEHeldout.ceOneHot_nonneg _ _)
    (Nat.cast_nonneg B)

/-- The unmodified transition's exact loss decrease is at least the computed
nonnegative majorizer residual at the same old weights. -/
theorem batchCertifiedDrop_le_actualDrop [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    batchCertifiedDrop X (coreParameters S) y ≤
      batchCEObjective X y S -
        batchCEObjective X y (batchTrainStep X y S opCost opRisk write) := by
  rw [batchCertifiedDrop]
  split_ifs with hR
  · rw [batchCEObjective_batchTrainStep_eq_of_rangeSquare_eq_zero
      X y S opCost opRisk write hR]
    exact sub_nonneg.mpr le_rfl
  · have hRpos : 0 < batchRangeSquare X (coreParameters S) y :=
      lt_of_le_of_ne (batchRangeSquare_nonneg X (coreParameters S) y)
        (Ne.symm hR)
    have hbound := batchLoss_safeStep_le_residual X (coreParameters S) y hRpos
    rw [batchCEObjective, batchCEObjective, coreParameters_batchTrainStep]
    linarith

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
  rw [← fixedBatchObjective_actual_telescope X y S opCost opRisk write T]
  exact Finset.sum_le_sum fun t _ht =>
    batchCertifiedDrop_le_actualDrop X y
      (fixedBatchState X y S opCost opRisk write t) opCost opRisk write

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
  apply tendsto_atTop_ciInf (fixedBatchObjective_antitone X y S opCost opRisk write)
  refine ⟨0, ?_⟩
  rintro z ⟨t, rfl⟩
  exact fixedBatchObjective_nonneg X y S opCost opRisk write t

/-- The actual loss infimum is nonnegative, without being declared optimal. -/
theorem fixedBatchObjective_ciInf_nonneg [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    0 ≤ ⨅ t, fixedBatchObjective X y S opCost opRisk write t :=
  le_ciInf (fixedBatchObjective_nonneg X y S opCost opRisk write)

/-- The empty fixed batch has zero raw mean at every time. -/
theorem fixedBatchObjective_empty [Nonempty V]
    (X : Fin 0 → Matrix V (Fin n) ℝ) (y : Fin 0 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    fixedBatchObjective X y S opCost opRisk write t = 0 := by
  simp [fixedBatchObjective, batchCEObjective, batchLoss,
    Hagi.Probability.FiniteFamilyConfidence.empiricalMean]

end Hagi.Contracts.BatchCETrajectory
