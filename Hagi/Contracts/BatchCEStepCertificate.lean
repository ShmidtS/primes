import Hagi.Contracts.CEStepCertificate
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEExpansion
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

/-- A current-state training input for an arbitrary supplied descent
direction.  The canonical transition subtracts the supplied raw gradient,
so the gradient field is exactly `-D`; cost, risk and writes stay external. -/
noncomputable def batchDirectionTrainInput
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainingInput n c where
  grad j := (-D S).ofLp j
  eta := batchDirectionSafeEta X (coreParameters S) y (D S)
  opCost := opCost
  opRisk := opRisk
  write := write

/-- The explicit two-sample current-state input.  Its gradient is the exact
minimum-norm point of the segment between the two current raw residual
gradients; all other fields retain the existing minimum-norm policy. -/
noncomputable def batchPairMinimumNormTrainInput
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainingInput n c where
  grad j := (Hagi.Step.segmentMinNorm
    (batchResidualGradient (X 0) (coreParameters S) (y 0))
    (batchResidualGradient (X 1) (coreParameters S) (y 1))).ofLp j
  eta := batchCommonSafeEta X (coreParameters S) y
  opCost := opCost
  opRisk := opRisk
  write := write

/-- On a two-sample batch, the explicit segment input is definitionally the
same policy as the classically selected minimum-norm input, up to the proved
pointwise gradient equality. -/
theorem batchPairMinimumNormTrainInput_eq_batchMinimumNormTrainInput
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    batchPairMinimumNormTrainInput X y S opCost opRisk write =
      batchMinimumNormTrainInput X y S opCost opRisk write := by
  unfold batchPairMinimumNormTrainInput batchMinimumNormTrainInput
  congr 1
  funext j
  rw [← batchGradientMinimizer_pair X (coreParameters S) y]

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

/-- Subtracting `-D` through the canonical transition is exactly addition
along `D` at the arbitrary-direction certified step from BatchCEDescent. -/
theorem coreParameters_trainStep_batchDirectionTrainInput
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    coreParameters (trainStep S
      (batchDirectionTrainInput X y D S opCost opRisk write)) =
      batchDirectionNextParameters X (coreParameters S) y (D S) := by
  apply PiLp.ext
  intro j
  change S.model.weights j -
      batchDirectionSafeEta X (coreParameters S) y (D S) * (-D S).ofLp j =
    S.model.weights j + batchDirectionSafeEta X (coreParameters S) y (D S) *
      (D S).ofLp j
  change S.model.weights j -
      batchDirectionSafeEta X (coreParameters S) y (D S) * -(D S).ofLp j =
    S.model.weights j + batchDirectionSafeEta X (coreParameters S) y (D S) *
      (D S).ofLp j
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

/-- The reusable two-sample specialization of the generic finite-batch
Pareto problem, using the explicit current-state segment input. -/
noncomputable def pairMinimumNormBatchParetoProblem
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Hagi.Unified.ParetoExecution.ControllerProblem (Fin 2) (TrainState n a r c k) :=
  guardedBatchParetoProblem X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write)

/-- Both pair-controller actions inherit generic safety; no new safety
decider, resource model or trajectory is constructed. -/
noncomputable instance pairMinimumNormBatchParetoProblemSafeDecidable
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    DecidablePred (pairMinimumNormBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write).safe :=
  guardedBatchParetoProblemSafeDecidable X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write)

/-- The explicit pair controller is exactly the prior minimum-norm
controller, by function extensionality of its current-state input. -/
theorem pairMinimumNormBatchParetoProblem_eq_minimumNormBatchParetoProblem
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    pairMinimumNormBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
        X y opCost opRisk write =
      minimumNormBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
        X y opCost opRisk write := by
  unfold pairMinimumNormBatchParetoProblem minimumNormBatchParetoProblem
  apply congrArg (guardedBatchParetoProblem X y)
  funext S
  exact batchPairMinimumNormTrainInput_eq_batchMinimumNormTrainInput
    X y S opCost opRisk write

/-- The pair-controller value is negative actual supplied-batch mean CE. -/
@[simp] theorem pairMinimumNormBatchParetoProblem_value
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (pairMinimumNormBatchParetoProblem X y opCost opRisk write).value S =
      -batchCEObjective X y S :=
  guardedBatchParetoProblem_value X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) S

/-- The pair-controller stay action is inherited unchanged. -/
@[simp] theorem pairMinimumNormBatchParetoProblem_step_zero
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (pairMinimumNormBatchParetoProblem X y opCost opRisk write).step 0 S = S :=
  guardedBatchParetoProblem_step_zero X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) S

/-- The pair-controller update action is the guarded explicit pair step. -/
@[simp] theorem pairMinimumNormBatchParetoProblem_step_one
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (pairMinimumNormBatchParetoProblem X y opCost opRisk write).step 1 S =
      batchPairMinimumNormTrainStep X y S opCost opRisk write :=
  guardedBatchParetoProblem_step_one X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) S

/-- The pair controller's stay action is feasible under every cap pair. -/
theorem pairMinimumNormBatchPareto_stay_feasible
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (pairMinimumNormBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y opCost opRisk write) M C :=
  guardedBatchPareto_stay_feasible X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) M C

/-- Pair update feasibility retains the generic logical resource condition:
one memory unit and at most two operation-index units. -/
theorem pairMinimumNormBatchPareto_one_feasible_iff
    (X : Fin 2 → Matrix V (Fin n) ℝ) (y : Fin 2 → V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (1 : Fin 2) ∈ feasible (pairMinimumNormBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y opCost opRisk write) M C ↔
        1 ≤ M ∧ 2 ≤ C :=
  guardedBatchPareto_one_feasible_iff X y
    (fun S => batchPairMinimumNormTrainInput X y S opCost opRisk write) M C

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

/-! ## A two-sample asymmetric CE guard comparison -/

open InnerProductSpace

/-- Two samples whose target-zero feature rows are respectively `(1,1)` and
`(1,3)`; both target-one rows are zero. -/
abbrev asymmetricFeatures : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun b v j => if v = 0 then
    (if j = 0 then 1 else if b = 0 then 1 else 3) else 0

/-- The two supplied labels are zero and one respectively. -/
def asymmetricLabels : Fin 2 → Fin 2 := fun b => if b = 0 then 0 else 1

/-- First coordinate of the first raw residual gradient at zero weights. -/
theorem asymmetric_residualGradient_zero_zero :
    (batchResidualGradient (asymmetricFeatures 0)
      (coreParameters identityInitialState) (asymmetricLabels 0)).ofLp 0 = -1 / 2 := by
  change residualTranspose (asymmetricFeatures 0)
    (0 : EuclideanSpace ℝ (Fin 2)) (asymmetricLabels 0) 0 = -1 / 2
  norm_num [asymmetricFeatures, asymmetricLabels, residualTranspose, ceResidual,
    ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, smul_eq_mul]

/-- Second coordinate of the first raw residual gradient at zero weights. -/
theorem asymmetric_residualGradient_zero_one :
    (batchResidualGradient (asymmetricFeatures 0)
      (coreParameters identityInitialState) (asymmetricLabels 0)).ofLp 1 = -1 / 2 := by
  change residualTranspose (asymmetricFeatures 0)
    (0 : EuclideanSpace ℝ (Fin 2)) (asymmetricLabels 0) 1 = -1 / 2
  norm_num [asymmetricFeatures, asymmetricLabels, residualTranspose, ceResidual,
    ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, smul_eq_mul]

/-- First coordinate of the second raw residual gradient at zero weights. -/
theorem asymmetric_residualGradient_one_zero :
    (batchResidualGradient (asymmetricFeatures 1)
      (coreParameters identityInitialState) (asymmetricLabels 1)).ofLp 0 = 1 / 2 := by
  change residualTranspose (asymmetricFeatures 1)
    (0 : EuclideanSpace ℝ (Fin 2)) (asymmetricLabels 1) 0 = 1 / 2
  norm_num [asymmetricFeatures, asymmetricLabels, residualTranspose, ceResidual,
    ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, smul_eq_mul]

/-- Second coordinate of the second raw residual gradient at zero weights. -/
theorem asymmetric_residualGradient_one_one :
    (batchResidualGradient (asymmetricFeatures 1)
      (coreParameters identityInitialState) (asymmetricLabels 1)).ofLp 1 = 3 / 2 := by
  change residualTranspose (asymmetricFeatures 1)
    (0 : EuclideanSpace ℝ (Fin 2)) (asymmetricLabels 1) 1 = 3 / 2
  norm_num [asymmetricFeatures, asymmetricLabels, residualTranspose, ceResidual,
    ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, smul_eq_mul]

/-- The common mean descent direction has zero first coordinate. -/
theorem asymmetric_meanDirection_zero :
    (batchMeanDirection asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels).ofLp 0 = 0 := by
  change (batchMeanDirection asymmetricFeatures 0 asymmetricLabels).ofLp 0 = 0
  norm_num [batchMeanDirection, asymmetricFeatures, asymmetricLabels, ceDirection,
    residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    smul_eq_mul]

/-- The common mean descent direction has second coordinate `-1/2`. -/
theorem asymmetric_meanDirection_one :
    (batchMeanDirection asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels).ofLp 1 = -1 / 2 := by
  change (batchMeanDirection asymmetricFeatures 0 asymmetricLabels).ofLp 1 = -1 / 2
  norm_num [batchMeanDirection, asymmetricFeatures, asymmetricLabels, ceDirection,
    residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    smul_eq_mul]

/-- The exact mean-residual alignment of the asymmetric fixture. -/
theorem asymmetric_alignment : batchAlignment asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels = 1 / 4 := by
  change batchAlignment asymmetricFeatures 0 asymmetricLabels = 1 / 4
  norm_num [batchAlignment, meanResidualTranspose, asymmetricFeatures,
    asymmetricLabels, residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    smul_eq_mul]

/-- The mean squared range along the actual common direction is five. -/
theorem asymmetric_rangeSquare : batchRangeSquare asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels = 5 := by
  change batchRangeSquare asymmetricFeatures 0 asymmetricLabels = 5
  norm_num [batchRangeSquare, batchMeanDirection, dirRange,
    asymmetricFeatures, asymmetricLabels, ceDirection, residualTranspose,
    ceResidual, ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, smul_eq_mul]

/-- The mean raw residual has zero first coordinate. -/
theorem asymmetric_meanResidualTranspose_zero :
    meanResidualTranspose asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels 0 = 0 := by
  change meanResidualTranspose asymmetricFeatures 0 asymmetricLabels 0 = 0
  norm_num [meanResidualTranspose, asymmetricFeatures, asymmetricLabels,
    residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    smul_eq_mul]

/-- The mean raw residual has second coordinate `1/2`. -/
theorem asymmetric_meanResidualTranspose_one :
    meanResidualTranspose asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels 1 = 1 / 2 := by
  change meanResidualTranspose asymmetricFeatures 0 asymmetricLabels 1 = 1 / 2
  norm_num [meanResidualTranspose, asymmetricFeatures, asymmetricLabels,
    residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    smul_eq_mul]

/-- The exact safe mean step computed from alignment and range is `1/5`. -/
theorem asymmetric_safeStep : batchSafeStep asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels = 1 / 5 := by
  rw [batchSafeStep, asymmetric_rangeSquare, asymmetric_alignment]
  norm_num

/-- The model-level mean successor has parameters `(0,-1/10)`. -/
theorem asymmetric_nextParameters :
    batchNextParameters asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels =
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -1 / 10) := by
  rw [batchNextParameters, alongNext, asymmetric_safeStep]
  apply PiLp.ext
  intro i
  fin_cases i
  · change (0 : ℝ) + (1 / 5 : ℝ) *
      (batchMeanDirection asymmetricFeatures
        (coreParameters identityInitialState) asymmetricLabels).ofLp 0 = 0
    rw [asymmetric_meanDirection_zero]
    norm_num
  · change (0 : ℝ) + (1 / 5 : ℝ) *
      (batchMeanDirection asymmetricFeatures
        (coreParameters identityInitialState) asymmetricLabels).ofLp 1 = -1 / 10
    rw [asymmetric_meanDirection_one]
    norm_num

/-- The actual canonical mean-gradient candidate for the asymmetric batch. -/
noncomputable def asymmetricMeanBatchStep : TrainState 2 0 0 0 0 :=
  batchTrainStep asymmetricFeatures asymmetricLabels identityInitialState
    (1 / 2) (1 / 4) none

/-- The canonical guard candidate, rather than a replacement fabricated state,
has parameters `(0,-1/10)`. -/
theorem coreParameters_asymmetricMeanBatchStep :
    coreParameters asymmetricMeanBatchStep =
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -1 / 10) := by
  rw [asymmetricMeanBatchStep, coreParameters_batchTrainStep]
  exact asymmetric_nextParameters

/-- Initially the first sample has the exact two-class loss `log 2`. -/
theorem batchSampleCE_asymmetric_initial_zero :
    batchSampleCE asymmetricFeatures asymmetricLabels 0 identityInitialState =
      Real.log 2 := by
  norm_num [batchSampleCE, asymmetricFeatures, asymmetricLabels,
    identityInitialState, coreParameters, ceLogits, Hagi.ceOneHot, Hagi.Core.lse,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- After the actual mean step, the first sample's real natural-log CE is
`log (1 + exp (1/10))`. -/
theorem batchSampleCE_asymmetricMeanBatchStep_zero :
    batchSampleCE asymmetricFeatures asymmetricLabels 0 asymmetricMeanBatchStep =
      Real.log (1 + Real.exp (1 / 10 : ℝ)) := by
  rw [batchSampleCE, coreParameters_asymmetricMeanBatchStep]
  norm_num [asymmetricFeatures, asymmetricLabels, ceLogits, Hagi.ceOneHot,
    Hagi.Core.lse, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hexp : (1 : ℝ) + Real.exp (1 / 10 : ℝ) =
      Real.exp (1 / 10 : ℝ) * (Real.exp (-1 / 10 : ℝ) + 1) := by
    rw [show (-1 / 10 : ℝ) = -(1 / 10 : ℝ) by ring, Real.exp_neg]
    field_simp
  rw [hexp, Real.log_mul (ne_of_gt (Real.exp_pos _)) (by positivity), Real.log_exp]
  ring_nf

/-- The actual mean-gradient candidate strictly increases the first sample CE. -/
theorem batchSampleCE_asymmetricMeanBatchStep_zero_gt :
    batchSampleCE asymmetricFeatures asymmetricLabels 0 identityInitialState <
      batchSampleCE asymmetricFeatures asymmetricLabels 0 asymmetricMeanBatchStep := by
  rw [batchSampleCE_asymmetric_initial_zero,
    batchSampleCE_asymmetricMeanBatchStep_zero]
  apply Real.log_lt_log (by norm_num : (0 : ℝ) < 2)
  have hpos : (1 / 10 : ℝ) + 1 < Real.exp (1 / 10 : ℝ) :=
    Real.add_one_lt_exp (by norm_num)
  linarith

/-- The second sample CE after the mean step has its exact logarithmic form. -/
theorem batchSampleCE_asymmetricMeanBatchStep_one :
    batchSampleCE asymmetricFeatures asymmetricLabels 1 asymmetricMeanBatchStep =
      Real.log (1 + Real.exp (-3 / 10 : ℝ)) := by
  rw [batchSampleCE, coreParameters_asymmetricMeanBatchStep]
  norm_num [asymmetricFeatures, asymmetricLabels, ceLogits, Hagi.ceOneHot,
    Hagi.Core.lse, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [add_comm]

/-- The same mean candidate strictly decreases the second sample CE; this does
not cancel the first sample's strict increase in the pointwise guard. -/
theorem batchSampleCE_asymmetricMeanBatchStep_one_lt :
    batchSampleCE asymmetricFeatures asymmetricLabels 1 asymmetricMeanBatchStep <
      batchSampleCE asymmetricFeatures asymmetricLabels 1 identityInitialState := by
  have hinitial :
      batchSampleCE asymmetricFeatures asymmetricLabels 1 identityInitialState =
        Real.log 2 := by
    norm_num [batchSampleCE, asymmetricFeatures, asymmetricLabels,
      identityInitialState, coreParameters, ceLogits, Hagi.ceOneHot, Hagi.Core.lse,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [batchSampleCE_asymmetricMeanBatchStep_one, hinitial]
  apply Real.log_lt_log (by positivity : (0 : ℝ) < 1 + Real.exp (-3 / 10 : ℝ))
  have hexp : Real.exp (-3 / 10 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-- The exact common range is positive. -/
theorem asymmetricRangeSquare_pos :
    0 < batchRangeSquare asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels := by
  rw [asymmetric_rangeSquare]
  norm_num

/-- Although the guard rejects the mean candidate, its actual batch-mean CE
strictly decreases.  Mean descent does not imply componentwise descent. -/
theorem batchCEObjective_asymmetricMeanBatchStep_lt :
    batchCEObjective asymmetricFeatures asymmetricLabels asymmetricMeanBatchStep <
      batchCEObjective asymmetricFeatures asymmetricLabels identityInitialState :=
  batchCEObjective_batchTrainStep_lt asymmetricFeatures asymmetricLabels
    identityInitialState (1 / 2) (1 / 4) none asymmetricRangeSquare_pos

/-- The common supplied cost is nonnegative and fits the initial budget two. -/
theorem asymmetric_cost_feasible :
    0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ identityInitialState.res.budget := by
  change 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 2
  norm_num

/-- The existing combined budget/pointwise guard vetoes the mean candidate and
returns the complete old state, solely because sample zero's CE increases. -/
theorem budgetedParetoBatchTrainStep_asymmetric_eq_fallback :
    budgetedParetoBatchTrainStep asymmetricFeatures asymmetricLabels
      identityInitialState (1 / 2) (1 / 4) none = identityInitialState := by
  apply budgetedParetoBatchTrainStep_of_inactive
  intro h
  have hle := h.2 0
  have hgt := batchSampleCE_asymmetricMeanBatchStep_zero_gt
  exact (not_le_of_gt hgt) hle

/-- The first raw residual gradient as an exact Euclidean vector. -/
theorem asymmetric_rawGradient_zero :
    batchResidualGradient (asymmetricFeatures 0)
      (coreParameters identityInitialState) (asymmetricLabels 0) =
      !₂[(-1 / 2 : ℝ), -1 / 2] := by
  apply PiLp.ext
  intro j
  fin_cases j
  · exact asymmetric_residualGradient_zero_zero
  · exact asymmetric_residualGradient_zero_one

/-- The second raw residual gradient as an exact Euclidean vector. -/
theorem asymmetric_rawGradient_one :
    batchResidualGradient (asymmetricFeatures 1)
      (coreParameters identityInitialState) (asymmetricLabels 1) =
      !₂[(1 / 2 : ℝ), 3 / 2] := by
  apply PiLp.ext
  intro j
  fin_cases j
  · exact asymmetric_residualGradient_one_zero
  · exact asymmetric_residualGradient_one_one

/-- Exact evaluation of the segment minimizer coefficient from the two real
raw gradients: the difference is nonzero, its squared norm is five, and the
required real inner product is `-3/2`. -/
theorem asymmetric_segmentMinNormCoefficient :
    Hagi.Step.segmentMinNormCoefficient
      (batchResidualGradient (asymmetricFeatures 0)
        (coreParameters identityInitialState) (asymmetricLabels 0))
      (batchResidualGradient (asymmetricFeatures 1)
        (coreParameters identityInitialState) (asymmetricLabels 1)) = 3 / 10 := by
  let g0 := batchResidualGradient (asymmetricFeatures 0)
    (coreParameters identityInitialState) (asymmetricLabels 0)
  let g1 := batchResidualGradient (asymmetricFeatures 1)
    (coreParameters identityInitialState) (asymmetricLabels 1)
  have h00 : residualTranspose (asymmetricFeatures 0)
      (coreParameters identityInitialState) (asymmetricLabels 0) 0 = -1 / 2 :=
    asymmetric_residualGradient_zero_zero
  have h01 : residualTranspose (asymmetricFeatures 0)
      (coreParameters identityInitialState) (asymmetricLabels 0) 1 = -1 / 2 :=
    asymmetric_residualGradient_zero_one
  have h10 : residualTranspose (asymmetricFeatures 1)
      (coreParameters identityInitialState) (asymmetricLabels 1) 0 = 1 / 2 :=
    asymmetric_residualGradient_one_zero
  have h11 : residualTranspose (asymmetricFeatures 1)
      (coreParameters identityInitialState) (asymmetricLabels 1) 1 = 3 / 2 :=
    asymmetric_residualGradient_one_one
  have hd : g1 - g0 ≠ 0 := by
    intro h
    have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z.ofLp 0) h
    dsimp [g0, g1] at hcoord
    norm_num [h00, h10] at hcoord
  have hnorm : ‖g1 - g0‖ ^ 2 = 5 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    dsimp [g0, g1]
    norm_num [h00, h01, h10, h11, Fin.sum_univ_two, RCLike.inner_apply]
  have hinner : ⟪g0, g1 - g0⟫_ℝ = -3 / 2 := by
    rw [PiLp.inner_apply]
    dsimp [g0, g1]
    norm_num [h00, h01, h10, h11, Fin.sum_univ_two, RCLike.inner_apply]
  rw [Hagi.Step.segmentMinNormCoefficient, ite_eq_right hd, hnorm, hinner]
  norm_num

/-- The explicit segment minimum is the actual vector `(-1/5,1/10)`. -/
theorem asymmetric_segmentMinNorm :
    Hagi.Step.segmentMinNorm
      (batchResidualGradient (asymmetricFeatures 0)
        (coreParameters identityInitialState) (asymmetricLabels 0))
      (batchResidualGradient (asymmetricFeatures 1)
        (coreParameters identityInitialState) (asymmetricLabels 1)) =
      !₂[(-1 / 5 : ℝ), 1 / 10] := by
  rw [Hagi.Step.segmentMinNorm, asymmetric_segmentMinNormCoefficient]
  rw [asymmetric_rawGradient_zero, asymmetric_rawGradient_one]
  apply PiLp.ext
  intro j
  fin_cases j <;> norm_num

/-- The selected two-sample convex-hull minimizer agrees with that explicit
segment point by the existing pair theorem. -/
theorem batchGradientMinimizer_asymmetric :
    batchGradientMinimizer asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels =
      !₂[(-1 / 5 : ℝ), 1 / 10] := by
  rw [batchGradientMinimizer_pair]
  exact asymmetric_segmentMinNorm

/-- The actual segment minimizer is nonzero by its first coordinate. -/
theorem batchGradientMinimizer_asymmetric_ne_zero :
    batchGradientMinimizer asymmetricFeatures
      (coreParameters identityInitialState) asymmetricLabels ≠ 0 := by
  rw [batchGradientMinimizer_asymmetric]
  intro h
  have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z.ofLp 0) h
  norm_num at hcoord

/-- The explicit pair-minimum candidate passed through the existing complete
guard, with the same nonnegative affordable cost as the mean candidate. -/
noncomputable def asymmetricPairMinimumNormBatchStep : TrainState 2 0 0 0 0 :=
  batchPairMinimumNormTrainStep asymmetricFeatures asymmetricLabels
    identityInitialState (1 / 2) (1 / 4) none

/-- The existing pair guard genuinely accepts and executes `trainStep`. -/
theorem asymmetricPairMinimumNormBatchStep_eq_trainStep :
    asymmetricPairMinimumNormBatchStep =
      trainStep identityInitialState (batchPairMinimumNormTrainInput
        asymmetricFeatures asymmetricLabels identityInitialState
          (1 / 2) (1 / 4) none) :=
  batchPairMinimumNormTrainStep_of_active asymmetricFeatures asymmetricLabels
    identityInitialState (1 / 2) (1 / 4) none asymmetric_cost_feasible

/-- Every supplied sample has strict real CE descent after the accepted pair
step, inherited from the proved nonzero-minimizer safety theorem. -/
theorem batchSampleCE_asymmetricPairMinimumNormBatchStep_lt (b : Fin 2) :
    batchSampleCE asymmetricFeatures asymmetricLabels b
      asymmetricPairMinimumNormBatchStep <
    batchSampleCE asymmetricFeatures asymmetricLabels b identityInitialState :=
  batchSampleCE_batchPairMinimumNormTrainStep_lt asymmetricFeatures
    asymmetricLabels identityInitialState (1 / 2) (1 / 4) none
    asymmetric_cost_feasible batchGradientMinimizer_asymmetric_ne_zero b

/-- The accepted pair step also strictly decreases actual batch-mean CE. -/
theorem batchCEObjective_asymmetricPairMinimumNormBatchStep_lt :
    batchCEObjective asymmetricFeatures asymmetricLabels
      asymmetricPairMinimumNormBatchStep <
    batchCEObjective asymmetricFeatures asymmetricLabels identityInitialState :=
  batchCEObjective_batchPairMinimumNormTrainStep_lt asymmetricFeatures
    asymmetricLabels identityInitialState (1 / 2) (1 / 4) none
    asymmetric_cost_feasible batchGradientMinimizer_asymmetric_ne_zero

/-- Accepted pair execution records exactly its abstract supplied `opCost`;
this is not a hardware or optimizer-work measurement. -/
theorem asymmetricPairMinimumNormBatchStep_flops :
    asymmetricPairMinimumNormBatchStep.res.flops =
      identityInitialState.res.flops + (1 / 2 : ℝ) :=
  batchPairMinimumNormTrainStep_flops_of_active asymmetricFeatures
    asymmetricLabels identityInitialState (1 / 2) (1 / 4) none
    asymmetric_cost_feasible

/-- One new backbone coordinate and two new optimizer moments are the
incremental persistent state coefficients, not a byte or RAM measurement. -/
def expandedStateCoefficients : ℕ := 3

/-- Construct the genuinely one-coordinate-wider state.  All dependent-width
fields are freshly constructed; independent state and old prefixes are kept. -/
noncomputable def expandedTrainState {n a r c k : ℕ}
    (S : TrainState n a r c k) : TrainState (n + 1) a r c k where
  model := {
    weights := (expandedParameters (coreParameters S) 0).ofLp
    adapters := S.model.adapters
    version := S.model.version + 1 }
  opt := {
    m := Fin.snoc S.opt.m 0
    v := Fin.snoc S.opt.v 0
    schedStep := S.opt.schedStep }
  mem := S.mem
  res := S.res
  saf := S.saf
  qual := S.qual

/-- The actual expanded state has zero in the new readout coordinate. -/
theorem coreParameters_expandedTrainState {n a r c k : ℕ}
    (S : TrainState n a r c k) :
    coreParameters (expandedTrainState S) =
      expandedParameters (coreParameters S) 0 := rfl

/-- Entry into the widened state preserves each supplied sample's actual CE,
even when the appended latent feature is nonzero. -/
theorem batchSampleCE_expandedTrainState
    (X : Fin B → Matrix V (Fin n) ℝ) (Z : Fin B → V → ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) (b : Fin B) :
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
      (expandedTrainState S) = batchSampleCE X y b S := by
  change Hagi.ceOneHot (y b) (ceLogits (expandedFeatures (X b) (Z b))
    (coreParameters (expandedTrainState S))) =
    Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S))
  rw [coreParameters_expandedTrainState]
  exact ceOneHot_expandedParameters_zero (X b) (coreParameters S) (Z b) (y b)

/-- Construct one wider zero-initialized state, then run the existing guarded
half-window training step at a supplied direction in the enlarged space. -/
noncomputable def expandedHalfTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState (n + 1) a r c k :=
  batchDirectionHalfTrainStep (fun b => expandedFeatures (X b) (Z b)) y
    (fun _ => D) (expandedTrainState S)
    (expandedFeatureEvaluationCount B V + trainingCost) opRisk write

/-- Growth into the zero-initialized wider state composes with ordinary guarded
training to give actual samplewise nonregression against the original model. -/
theorem batchSampleCE_expandedHalfTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) ≤
      batchSampleCE X y b S := by
  have h := batchSampleCE_batchDirectionHalfTrainStep_le
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write b
  calc
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) ≤
      batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedTrainState S) := by
        simpa only [expandedHalfTrainStep] using h
    _ = batchSampleCE X y b S :=
      batchSampleCE_expandedTrainState X Z y S b

/-- The legal enlarged half-step dominates the certified minimum quadratic
residual and transports its bound to the original model's CE. -/
theorem batchSampleCE_expandedHalfTrainStep_le_minQuadraticMargin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) (y b) D < 0) (b : Fin B) :
  let _ : Nonempty (Fin B) := hcert.1
  batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) ≤
      batchSampleCE X y b S -
        batchDirectionMinQuadraticMargin
          (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D
          (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
            (coreParameters (expandedTrainState S)) y D) := by
  let _ : Nonempty (Fin B) := hcert.1
  have hcombined : 0 ≤ (expandedFeatureEvaluationCount B V : ℝ) + trainingCost :=
    add_nonneg (by positivity) hcost.1
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤
      (expandedTrainState S).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have hper := batchSampleCE_batchDirectionHalfTrainStep_le_quadraticMargin
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write ⟨hcombined, hbudget⟩ b
  have hmin :
      batchDirectionMinQuadraticMargin
        (fun b => expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) y D
        (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D) ≤
      batchDirectionQuadraticMargin
        (fun b => expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) y D
        (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D) b :=
    ciInf_le (Finite.bddBelow_range _) b
  calc
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) ≤
      batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedTrainState S) - _ := by
        simpa only [expandedHalfTrainStep] using hper
    _ ≤ batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedTrainState S) -
        batchDirectionMinQuadraticMargin
          (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D
          (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
            (coreParameters (expandedTrainState S)) y D) := by
      linarith [hmin]
    _ = batchSampleCE X y b S -
        batchDirectionMinQuadraticMargin
          (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D
          (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
            (coreParameters (expandedTrainState S)) y D) := by
      rw [batchSampleCE_expandedTrainState X Z y S b]

/-- An affordable, fully certified enlarged step strictly improves every
sample's actual CE relative to the original narrow model. -/
theorem batchSampleCE_expandedHalfTrainStep_lt
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) (y b) D < 0) (b : Fin B) :
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) <
      batchSampleCE X y b S := by
  let _ : Nonempty (Fin B) := hcert.1
  have hcombined : 0 ≤ (expandedFeatureEvaluationCount B V : ℝ) + trainingCost :=
    add_nonneg (by positivity) hcost.1
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤
      (expandedTrainState S).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have hactive := batchDirectionHalfTrainStep_of_active
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write ⟨hcombined, hbudget⟩ hcert
  calc
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) =
      Hagi.ceOneHot (y b) (ceLogits (expandedFeatures (X b) (Z b))
        (batchDirectionHalfNextParameters
          (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D)) := by
      unfold batchSampleCE expandedHalfTrainStep
      rw [hactive, coreParameters_trainStep_batchDirectionHalfTrainInput]
    _ < batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedTrainState S) :=
      ceOneHot_batchDirectionHalfNextParameters_lt
        (fun b => expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) y D (hcert.2) b
    _ = batchSampleCE X y b S :=
      batchSampleCE_expandedTrainState X Z y S b

/-- The accepted step can actually learn the appended readout coordinate; its
last coefficient is the old zero plus the half-window times its direction. -/
theorem coreParameters_expandedHalfTrainStep_last
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) (y b) D < 0) :
    (coreParameters (expandedHalfTrainStep X y Z D S trainingCost opRisk write)).ofLp
        (Fin.last n) =
      batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) y D * D.ofLp (Fin.last n) := by
  have hcombined : 0 ≤ (expandedFeatureEvaluationCount B V : ℝ) + trainingCost :=
    add_nonneg (by positivity) hcost.1
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤
      (expandedTrainState S).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have hactive := batchDirectionHalfTrainStep_of_active
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write ⟨hcombined, hbudget⟩ hcert
  unfold expandedHalfTrainStep
  rw [hactive, coreParameters_trainStep_batchDirectionHalfTrainInput]
  simp [batchDirectionHalfNextParameters, alongNext]
  change (Fin.snoc (α := fun _ : Fin (n + 1) => ℝ)
    (coreParameters S).ofLp 0) (Fin.last n) = 0
  simp

/-- An affordable combined operation-cell cost leaves nonnegative budget
after expansion and the guarded training step, including fallback branches. -/
theorem expandedHalfTrainStep_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget) :
    0 ≤ (expandedHalfTrainStep X y Z D S trainingCost opRisk write).res.budget := by
  have hbudget : 0 ≤ S.res.budget :=
    le_trans (add_nonneg (by positivity) hcost.1) hcost.2
  have h := batchDirectionHalfTrainStep_budget_nonneg
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write (by simpa only [expandedTrainState] using hbudget)
  simpa only [expandedHalfTrainStep] using h

/-- Under the complete certificate, accepted enlarged training has exact
declared cost accounting from the original state's accumulated flops. -/
theorem expandedHalfTrainStep_flops_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) (y b) D < 0) :
    (expandedHalfTrainStep X y Z D S trainingCost opRisk write).res.flops =
      S.res.flops + ((expandedFeatureEvaluationCount B V : ℝ) + trainingCost) := by
  have hcombined : 0 ≤ (expandedFeatureEvaluationCount B V : ℝ) + trainingCost :=
    add_nonneg (by positivity) hcost.1
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤
      (expandedTrainState S).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have h := batchDirectionHalfTrainStep_flops_of_active
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write ⟨hcombined, hbudget⟩ hcert
  simpa only [expandedHalfTrainStep, expandedTrainState] using h

/-! ## Computed five-task batch evaluation through the actual MGDA step

`batchCEMeasured` is a mathematical, parameter-computed evaluation of named
supervised tasks.  It does not read stored `TrainState.qual`, make those five
sample indices into external task categories, or assert fresh-data confidence.
The negative-CE orientation matches `FloorKept`: higher evaluation is better.
-/
open Hagi.Unified.HonestTransition Hagi.Unified.CertifiedLoop
  Hagi.Unified.LinkedQVec

/-- Actual per-task CE, negated for the higher-is-better quality-floor API. -/
noncomputable def batchCEMeasured (X : Fin 5 → Matrix V (Fin n) ℝ)
    (y : Fin 5 → V) : MeasuredState (TrainState n a r c k) where
  evaluate := fun S i => -batchSampleCE X y i S

/-- Any supplied-batch computed quality floor survives the existing guarded
minimum-norm transition, including a rejected update that returns `S`. -/
theorem floor_kept_batchMinimumNormTrainStep
    (X : Fin 5 → Matrix V (Fin n) ℝ) (y : Fin 5 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (floor : QualityVector)
    (hfloor : FloorKept (batchCEMeasured X y) S floor) :
    FloorKept (batchCEMeasured X y)
      (batchMinimumNormTrainStep X y S opCost opRisk write) floor := by
  intro i
  have hle := batchSampleCE_batchMinimumNormTrainStep_le
    X y S opCost opRisk write i
  exact (hfloor i).trans (neg_le_neg hle)

/-- Strict mean-CE descent on the admitted nonzero-minimizer MGDA successor,
using the exact old-minus-new objective gap rather than an assigned effect. -/
noncomputable def batchMinimumNormMinimalCert
    (X : Fin 5 → Matrix V (Fin n) ℝ) (y : Fin 5 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hω : batchGradientMinimizer X (coreParameters S) y ≠ 0) :
    CertStep (batchCEObjective X y) S
      (batchMinimumNormTrainStep X y S opCost opRisk write) where
  drop := batchCEObjective X y S -
    batchCEObjective X y (batchMinimumNormTrainStep X y S opCost opRisk write)
  drop_pos := sub_pos.mpr (batchCEObjective_batchMinimumNormTrainStep_lt
    X y S opCost opRisk write hcost hω)
  actual := by
    have hlt := batchCEObjective_batchMinimumNormTrainStep_lt
      X y S opCost opRisk write hcost hω
    linarith

/-- A full certificate for the actually executed nonzero-minimizer update:
strict supplied-batch mean-CE descent and preservation of all five computed
per-task evaluation floors.  Costs and risk are logical inputs, not runtime
measurements; this says nothing about external quality or generalization. -/
noncomputable def evaluatedBatchMinimumNormCert
    (X : Fin 5 → Matrix V (Fin n) ℝ) (y : Fin 5 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (floor : QualityVector) (riskLim : ℝ)
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hω : batchGradientMinimizer X (coreParameters S) y ≠ 0)
    (hrisk : 0 ≤ opRisk) (hriskLim : opRisk ≤ riskLim)
    (hfloor : FloorKept (batchCEMeasured X y) S floor) :
    StepCert (batchCEObjective X y) (batchCEMeasured X y) floor riskLim S
      (batchMinimumNormTrainStep X y S opCost opRisk write) S.res.budget
      (batchMinimumNormTrainStep X y S opCost opRisk write).res.budget where
  riskSpend := opRisk
  budgetSpend := opCost
  trans :=
    { objectiveDrop :=
        (batchMinimumNormMinimalCert X y S opCost opRisk write hcost hω).drop
      objectiveDrop_pos :=
        (batchMinimumNormMinimalCert X y S opCost opRisk write hcost hω).drop_pos
      actualDescent :=
        (batchMinimumNormMinimalCert X y S opCost opRisk write hcost hω).actual
      riskBound := hriskLim
      budgetBound := batchMinimumNormTrainStep_budget_nonneg
        X y S opCost opRisk write (le_trans hcost.1 hcost.2) }
  hriskSpend_nn := hrisk
  hbudgetSpend_nn := hcost.1
  hdec := by
    rw [batchMinimumNormTrainStep_of_active X y S opCost opRisk write hcost]
    exact le_of_eq (trainStep_budget S
      (batchMinimumNormTrainInput X y S opCost opRisk write))
  quality := floor_kept_batchMinimumNormTrainStep
    X y S opCost opRisk write floor hfloor

end Hagi.Contracts.BudgetedBatchCE
