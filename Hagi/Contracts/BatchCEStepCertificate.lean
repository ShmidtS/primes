import Hagi.Contracts.CEStepCertificate
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEHeldout
import Hagi.Unified.ParetoExecution

/-!
# Executed arithmetic-batch CE descent through the canonical trainStep

This module computes a common batch direction and safe step from actual current
backbone weights and supplied feature/label maps, then executes the existing
`State.trainStep`.  It proves that this executed update is the same
`batchNextParameters` from `Model.BatchCEDescent`.

Certificates concern the actual arithmetic-mean categorical cross-entropy on
the supplied batch, not independent per-example descent, fresh held-out data,
global convergence, or external quality telemetry.  Cost, risk and optional
memory writes remain supplied logical inputs, not physical measurements.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BatchCEStep

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Unified.HonestTransition Hagi.Unified.CertifiedLoop

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- The actual arithmetic-mean batch CE of the state's backbone weights. -/
noncomputable def batchCEObjective (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) : ℝ :=
  batchLoss X (coreParameters S) y

/-- A canonical training input computed from the common batch residual
transpose and the safe batch step; resource/write inputs stay external. -/
noncomputable def batchTrainInput (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainingInput n c where
  grad := meanResidualTranspose X (coreParameters S) y
  eta := batchSafeStep X (coreParameters S) y
  opCost := opCost
  opRisk := opRisk
  write := write

/-- Actual execution of the unmodified canonical training transition. -/
noncomputable def batchTrainStep (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  trainStep S (batchTrainInput X y S opCost opRisk write)

/-- The executed common mean-gradient subtraction is precisely the common
batch negative-residual update, at the same old parameters and batch. -/
theorem coreParameters_batchTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    coreParameters (batchTrainStep X y S opCost opRisk write) =
      batchNextParameters X (coreParameters S) y := by
  apply PiLp.ext
  intro i
  change S.model.weights i -
      batchSafeStep X (coreParameters S) y *
        meanResidualTranspose X (coreParameters S) y i =
    S.model.weights i + batchSafeStep X (coreParameters S) y *
      (batchMeanDirection X (coreParameters S) y).ofLp i
  rw [batchMeanDirection_eq_neg_meanResidualTranspose]
  change S.model.weights i - batchSafeStep X (coreParameters S) y *
      meanResidualTranspose X (coreParameters S) y i =
    S.model.weights i + batchSafeStep X (coreParameters S) y *
      -meanResidualTranspose X (coreParameters S) y i
  ring

/-- Adapters are unchanged by the existing backbone-weight transition. -/
theorem adapters_batchTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (batchTrainStep X y S opCost opRisk write).model.adapters =
      S.model.adapters := rfl

/-- Stored external telemetry is unchanged, not claimed to improve. -/
theorem qual_batchTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (batchTrainStep X y S opCost opRisk write).qual = S.qual := rfl

/-- A positive common squared range produces a strictly positive safe step. -/
theorem batchTrainInput_eta_pos
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hR : 0 < batchRangeSquare X (coreParameters S) y) :
    0 < (batchTrainInput X y S opCost opRisk write).eta :=
  batchSafeStep_pos_of_rangeSquare_pos X (coreParameters S) y hR

/-- Strict descent of actual supplied-batch mean CE at the executed state. -/
theorem batchCEObjective_batchTrainStep_lt [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hR : 0 < batchRangeSquare X (coreParameters S) y) :
    batchCEObjective X y (batchTrainStep X y S opCost opRisk write) <
      batchCEObjective X y S := by
  rw [batchCEObjective, batchCEObjective, coreParameters_batchTrainStep]
  exact batchLoss_safeStep_lt X (coreParameters S) y hR

/-- The minimal certificate uses the exact old mean CE minus new mean CE. -/
noncomputable def batchTrainStepMinimalCert [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hR : 0 < batchRangeSquare X (coreParameters S) y) :
    CertStep (batchCEObjective X y) S
      (batchTrainStep X y S opCost opRisk write) where
  drop := batchCEObjective X y S -
    batchCEObjective X y (batchTrainStep X y S opCost opRisk write)
  drop_pos := sub_pos.mpr
    (batchCEObjective_batchTrainStep_lt X y S opCost opRisk write hR)
  actual := by
    have hlt := batchCEObjective_batchTrainStep_lt X y S opCost opRisk write hR
    linarith

/-- Complete canonical certificate for real executed mean-CE descent.  The
stored external quality floor is preserved unchanged; this does not equate
CE with quality.  Optimizer/resource and optional memory effects can change. -/
noncomputable def batchTrainStepCert [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (floor : QualityVector) (riskLim : ℝ)
    (hR : 0 < batchRangeSquare X (coreParameters S) y)
    (hrisk : 0 ≤ opRisk) (hcost : 0 ≤ opCost)
    (hriskLim : opRisk ≤ riskLim) (hfloor : FloorHeld S floor)
    (hbudget : opCost ≤ S.res.budget) :
    StepCert (batchCEObjective X y) trainMeasured floor riskLim S
      (batchTrainStep X y S opCost opRisk write) S.res.budget
      (batchTrainStep X y S opCost opRisk write).res.budget where
  riskSpend := opRisk
  budgetSpend := opCost
  trans :=
    { objectiveDrop :=
        (batchTrainStepMinimalCert X y S opCost opRisk write hR).drop
      objectiveDrop_pos :=
        (batchTrainStepMinimalCert X y S opCost opRisk write hR).drop_pos
      actualDescent :=
        (batchTrainStepMinimalCert X y S opCost opRisk write hR).actual
      riskBound := hriskLim
      budgetBound := by
        rw [batchTrainStep, trainStep_budget, batchTrainInput]
        exact sub_nonneg.mpr hbudget }
  hriskSpend_nn := hrisk
  hbudgetSpend_nn := hcost
  hdec := le_of_eq (trainStep_budget S (batchTrainInput X y S opCost opRisk write))
  quality := by
    intro i
    change floor i ≤ (batchTrainStep X y S opCost opRisk write).qual i
    rw [qual_batchTrainStep]
    exact hfloor i

/-- The zero-range selected update preserves the actual backbone parameters. -/
theorem coreParameters_batchTrainStep_eq_of_rangeSquare_eq_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hR : batchRangeSquare X (coreParameters S) y = 0) :
    coreParameters (batchTrainStep X y S opCost opRisk write) =
      coreParameters S := by
  rw [coreParameters_batchTrainStep]
  exact batchNextParameters_eq_of_rangeSquare_eq_zero X (coreParameters S) y hR

/-- The zero-range selected update preserves the supplied batch mean CE only;
it is not an optimizer hold or a positive certificate. -/
theorem batchCEObjective_batchTrainStep_eq_of_rangeSquare_eq_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hR : batchRangeSquare X (coreParameters S) y = 0) :
    batchCEObjective X y (batchTrainStep X y S opCost opRisk write) =
      batchCEObjective X y S := by
  rw [batchCEObjective, batchCEObjective, coreParameters_batchTrainStep]
  exact batchLoss_batchNext_eq_of_rangeSquare_eq_zero X (coreParameters S) y hR

end Hagi.Contracts.BatchCEStep

namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- The raw finite arithmetic-mean loss is nonnegative when the target
vocabulary is inhabited; the separate empty-batch convention is checked below. -/
theorem batchLoss_nonneg [Nonempty V] (X : Fin B → Matrix V (Fin n) ℝ)
    (θ : EuclideanSpace ℝ (Fin n)) (y : Fin B → V) :
    0 ≤ batchLoss X θ y := by
  unfold batchLoss Hagi.Probability.FiniteFamilyConfidence.empiricalMean
  exact div_nonneg (Finset.sum_nonneg fun _ _ => CEHeldout.ceOneHot_nonneg _ _)
    (Nat.cast_nonneg B)

/-- The existing nonnegative majorizer residual for the canonical batch step. -/
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

/-- The canonical transition's exact loss decrease dominates the nonnegative
majorizer residual at the same old weights. -/
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

end Hagi.Contracts.BatchCETrajectory

namespace Hagi.Contracts.BatchCEStep

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Unified.HonestTransition Hagi.Unified.CertifiedLoop

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Distinct finite feature matrices I and 2I with genuinely mixed labels. -/
abbrev heterogeneousFeatures : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun b v j => if v = j then (if b = 0 then 1 else 2) else 0

/-- Exact first coordinate of the common mixed-feature direction. -/
theorem heterogeneous_meanDirection_zero :
    (batchMeanDirection heterogeneousFeatures
      (coreParameters identityInitialState) mixedLabels).ofLp 0 = -1 / 4 := by
  change (batchMeanDirection heterogeneousFeatures 0 mixedLabels).ofLp 0 = -1 / 4
  norm_num [batchMeanDirection, heterogeneousFeatures, mixedLabels, ceDirection,
    residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

/-- Exact second coordinate of the common mixed-feature direction. -/
theorem heterogeneous_meanDirection_one :
    (batchMeanDirection heterogeneousFeatures
      (coreParameters identityInitialState) mixedLabels).ofLp 1 = 1 / 4 := by
  change (batchMeanDirection heterogeneousFeatures 0 mixedLabels).ofLp 1 = 1 / 4
  norm_num [batchMeanDirection, heterogeneousFeatures, mixedLabels, ceDirection,
    residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

/-- Common mean-gradient alignment, not a mean of own alignments. -/
theorem heterogeneous_alignment :
    batchAlignment heterogeneousFeatures
      (coreParameters identityInitialState) mixedLabels = 1 / 8 := by
  change batchAlignment heterogeneousFeatures 0 mixedLabels = 1 / 8
  norm_num [batchAlignment, meanResidualTranspose, heterogeneousFeatures,
    mixedLabels, residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

/-- Mean squared range is evaluated along the common direction. -/
theorem heterogeneous_rangeSquare :
    batchRangeSquare heterogeneousFeatures
      (coreParameters identityInitialState) mixedLabels = 5 / 2 := by
  change batchRangeSquare heterogeneousFeatures 0 mixedLabels = 5 / 2
  norm_num [batchRangeSquare, batchMeanDirection, dirRange,
    heterogeneousFeatures, mixedLabels, ceDirection, residualTranspose,
    ceResidual, ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul]

/-- The mixed-feature common range is strictly positive. -/
theorem heterogeneous_rangeSquare_pos :
    0 < batchRangeSquare heterogeneousFeatures
      (coreParameters identityInitialState) mixedLabels := by
  rw [heterogeneous_rangeSquare]
  norm_num

/-- Computed safe batch step for the mixed-feature fixture. -/
theorem heterogeneous_safeStep :
    batchSafeStep heterogeneousFeatures
      (coreParameters identityInitialState) mixedLabels = 1 / 5 := by
  rw [batchSafeStep, heterogeneous_rangeSquare, heterogeneous_alignment]
  norm_num

/-- The model-level common update has the expected actual nonzero parameters. -/
theorem heterogeneous_nextParameters :
    batchNextParameters heterogeneousFeatures
      (coreParameters identityInitialState) mixedLabels =
      WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then (-1 : ℝ) / 20 else 1 / 20) := by
  rw [batchNextParameters, alongNext, heterogeneous_safeStep]
  apply PiLp.ext
  intro i
  fin_cases i
  · change (0 : ℝ) + (1 / 5 : ℝ) *
      (batchMeanDirection heterogeneousFeatures
        (coreParameters identityInitialState) mixedLabels).ofLp 0 = -1 / 20
    rw [heterogeneous_meanDirection_zero]
    norm_num
  · change (0 : ℝ) + (1 / 5 : ℝ) *
      (batchMeanDirection heterogeneousFeatures
        (coreParameters identityInitialState) mixedLabels).ofLp 1 = 1 / 20
    rw [heterogeneous_meanDirection_one]
    norm_num

/-- Executed heterogeneous batch transition with logical ledger inputs only. -/
noncomputable def heterogeneousStep : TrainState 2 0 0 0 0 :=
  batchTrainStep heterogeneousFeatures mixedLabels identityInitialState
    (1 / 2) (1 / 4) none

/-- Actual weights after executing the common batch safe step. -/
theorem coreParameters_heterogeneousStep :
    coreParameters heterogeneousStep =
      WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then (-1 : ℝ) / 20 else 1 / 20) := by
  rw [heterogeneousStep, coreParameters_batchTrainStep]
  exact heterogeneous_nextParameters

/-- Actual supplied mixed-batch mean CE strictly descends under execution. -/
theorem batchCEObjective_heterogeneousStep_lt :
    batchCEObjective heterogeneousFeatures mixedLabels heterogeneousStep <
      batchCEObjective heterogeneousFeatures mixedLabels identityInitialState :=
  batchCEObjective_batchTrainStep_lt heterogeneousFeatures mixedLabels
    identityInitialState (1 / 2) (1 / 4) none heterogeneous_rangeSquare_pos

/-- At the selected step the computed majorizer equals old mean CE minus 1/80.
This residual lower bound is not the certificate's exact old-minus-new drop. -/
theorem heterogeneous_majorizer_at_safeStep :
    batchMajorizer heterogeneousFeatures (coreParameters identityInitialState)
      mixedLabels (batchSafeStep heterogeneousFeatures
        (coreParameters identityInitialState) mixedLabels) =
      batchCEObjective heterogeneousFeatures mixedLabels identityInitialState -
        1 / 80 := by
  change batchMajorizer heterogeneousFeatures (coreParameters identityInitialState)
    mixedLabels (batchSafeStep heterogeneousFeatures
      (coreParameters identityInitialState) mixedLabels) =
    batchLoss heterogeneousFeatures (coreParameters identityInitialState)
      mixedLabels - 1 / 80
  rw [batchMajorizer_safeStep_eq _ _ _ heterogeneous_rangeSquare_pos,
    heterogeneous_alignment, heterogeneous_rangeSquare]
  norm_num

/-- Full concrete canonical batch certificate.  These are hypothetical ledger
values, not hardware or benchmark measurements. -/
noncomputable def heterogeneousStepCert :
    StepCert (batchCEObjective heterogeneousFeatures mixedLabels)
      trainMeasured (fun _ => 0) (1 / 2) identityInitialState heterogeneousStep
      identityInitialState.res.budget heterogeneousStep.res.budget :=
  batchTrainStepCert heterogeneousFeatures mixedLabels identityInitialState
    (1 / 2) (1 / 4) none (fun _ => 0) (1 / 2) heterogeneous_rangeSquare_pos
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; change (0 : ℝ) ≤ 0; exact le_rfl)
    (by change (1 / 2 : ℝ) ≤ 2; norm_num)

end Hagi.Contracts.BatchCEStep

namespace Hagi.Contracts.BudgetedBatchCE

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep

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

/-- Accept the canonical batch transition only if nonnegative supplied cost
fits declared budget and every finite-batch component does not increase. -/
noncomputable def budgetedParetoBatchTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  if (0 ≤ opCost ∧ opCost ≤ S.res.budget) ∧ ∀ b,
      batchSampleCE X y b (batchTrainStep X y S opCost opRisk write) ≤
        batchSampleCE X y b S then
    batchTrainStep X y S opCost opRisk write
  else
    S

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

/-- Two control successors: identity and the budget/pointwise-guarded batch
transition with the same supplied optimizer, resource and optional write inputs. -/
noncomputable def batchParetoStepFun
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (action : Fin 2) (S : TrainState n a r c k) : TrainState n a r c k :=
  if action = 1 then
    budgetedParetoBatchTrainStep X y S opCost opRisk write
  else
    S

/-- The finite-batch Pareto controller. Its model operation index is `B` per
update action, not a count of physical FLOPs or estimator evaluations. -/
noncomputable def batchParetoProblem
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Hagi.Unified.ParetoExecution.ControllerProblem (Fin 2) (TrainState n a r c k) where
  value := fun S => -batchCEObjective X y S
  step := batchParetoStepFun X y opCost opRisk write
  memory := fun action => action.val
  operations := fun action => B * action.val
  safe := fun action => ∀ S : TrainState n a r c k,
    batchCEObjective X y (batchParetoStepFun X y opCost opRisk write action S) ≤
      batchCEObjective X y S

/-- Both finite actions are decided by the proved batch CE guards, not by an
unsubstantiated executable safety certificate. -/
noncomputable instance batchParetoProblemSafeDecidable
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    DecidablePred (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write).safe :=
  fun action =>
    if h : action = 0 then
      isTrue (by
        subst action
        intro S
        simp [batchParetoStepFun])
    else
      isTrue (by
        have ha_one : action = 1 := by
          have hval : action.val = 0 ∨ action.val = 1 := by omega
          rcases hval with hzero | hone
          · exact False.elim (h (Fin.ext hzero))
          · exact Fin.ext hone
        subst action
        intro S
        simpa [batchParetoStepFun] using
          (batchCEObjective_budgetedParetoBatchTrainStep_le
            X y S opCost opRisk write))

@[simp] theorem batchParetoProblem_step_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (batchParetoProblem X y opCost opRisk write).step 0 S = S := by
  simp [batchParetoProblem, batchParetoStepFun]

@[simp] theorem batchParetoProblem_step_one
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (batchParetoProblem X y opCost opRisk write).step 1 S =
      budgetedParetoBatchTrainStep X y S opCost opRisk write := by
  simp [batchParetoProblem, batchParetoStepFun]

open Hagi.Unified.ParetoExecution

/-- The stay action is feasible under every logical resource cap pair. -/
theorem batchPareto_stay_feasible
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y opCost opRisk write) M C := by
  apply mem_feasible.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro S
    rw [show batchParetoStepFun X y opCost opRisk write 0 S = S by
      simp [batchParetoStepFun]]
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
    · intro S
      rw [show batchParetoStepFun X y opCost opRisk write 1 S =
        budgetedParetoBatchTrainStep X y S opCost opRisk write by
          simp [batchParetoStepFun]]
      exact batchCEObjective_budgetedParetoBatchTrainStep_le
        X y S opCost opRisk write
    · simpa [batchParetoProblem] using hM
    · simpa [batchParetoProblem] using hC

end Hagi.Contracts.BudgetedBatchCE
