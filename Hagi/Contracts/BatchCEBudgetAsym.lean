import Hagi.Contracts.CEStepCertificate
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEExpansion
import Hagi.Model.CEHeldout
import Hagi.Unified.ParetoExecution
import Hagi.Contracts.BatchCEBudgetIdentity

/-!
# BatchCEBudgetAsym

Two-sample asymmetric CE guard comparison fixtures. Split from `BatchCEStepCertificate` (C255).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BudgetedBatchCE

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Model.CEExpansion

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

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
alias asymmetric_cost_feasible := identityMinimumNormBatchStep_cost_feasible

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


end Hagi.Contracts.BudgetedBatchCE
