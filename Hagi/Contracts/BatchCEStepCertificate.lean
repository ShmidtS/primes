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

/-- A canonical training input from the minimum-norm point of the raw
single-sample residual-gradient convex hull at the current state. -/
noncomputable def batchMinimumNormTrainInput (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainingInput n c where
  grad j := (batchGradientMinimizer X (coreParameters S) y).ofLp j
  eta := batchCommonSafeEta X (coreParameters S) y
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

/-- The canonical weight subtraction with the current minimum-norm gradient
is exactly addition along its negative at the common safe step. -/
theorem coreParameters_trainStep_batchMinimumNormTrainInput
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    coreParameters (trainStep S
      (batchMinimumNormTrainInput X y S opCost opRisk write)) =
      batchCommonNextParameters X (coreParameters S) y := by
  apply PiLp.ext
  intro j
  change S.model.weights j - batchCommonSafeEta X (coreParameters S) y *
      (batchGradientMinimizer X (coreParameters S) y).ofLp j =
    S.model.weights j + batchCommonSafeEta X (coreParameters S) y *
      -(batchGradientMinimizer X (coreParameters S) y).ofLp j
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
