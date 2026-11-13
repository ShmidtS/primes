import Hagi.Contracts.CEStepCertificate
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEExpansion
import Hagi.Model.CEHeldout
import Hagi.Unified.ParetoExecution

/-!
# BatchCEStepCore

Canonical batch CE step inputs, executed `trainStep` descent certificates, certified drop, and the heterogeneous mixed-feature witness. Split from `BatchCEStepCertificate` (C255).
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

/-! ## Sharp-range certified drop (C233 R2 wiring) -/

/-- Sharp-range certified residual: the exact C223 expression
`2 * batchAlignment^2 / batchLogitRangeSquare` under the same zero-branch
convention as `batchCertifiedDrop`, with the sharp mean logit range
`batchLogitRangeSquare` in place of `batchRangeSquare`. -/
noncomputable def batchLogitCertifiedDrop [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n))
    (y : Fin B → V) : ℝ :=
  if batchLogitRangeSquare X θ y = 0 then 0
  else 2 * batchAlignment X θ y ^ 2 / batchLogitRangeSquare X θ y

/-- Both branches of the sharp-range residual are nonnegative. -/
theorem batchLogitCertifiedDrop_nonneg [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n))
    (y : Fin B → V) :
    0 ≤ batchLogitCertifiedDrop X θ y := by
  rw [batchLogitCertifiedDrop]
  split_ifs with hR
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (batchLogitRangeSquare_nonneg X θ y)

/-- Under a positive sharp mean range-square the engine's certified
residual never exceeds the sharp-range one: `batchRangeSquare` dominates
`batchLogitRangeSquare`, so the sharp divisor gives the larger drop.  The
positivity premise is load-bearing: a zero sharp range with positive
vocabulary-sum range (constant directional logits, nonzero alignment)
makes the engine residual positive and the sharp one zero. -/
theorem batchCertifiedDrop_le_batchLogitCertifiedDrop [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n))
    (y : Fin B → V) (hR : 0 < batchLogitRangeSquare X θ y) :
    batchCertifiedDrop X θ y ≤ batchLogitCertifiedDrop X θ y := by
  have hle := batchLogitRangeSquare_le_batchRangeSquare X θ y
  have hRold : 0 < batchRangeSquare X θ y := lt_of_lt_of_le hR hle
  have hA : 0 ≤ batchAlignment X θ y := batchAlignment_nonneg X θ y
  rw [batchCertifiedDrop, ite_eq_right (ne_of_gt hRold),
    batchLogitCertifiedDrop, ite_eq_right (ne_of_gt hR),
    div_le_div_iff₀ hRold hR]
  exact mul_le_mul_of_nonneg_left hle
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg _))

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
