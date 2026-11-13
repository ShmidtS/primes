import Hagi.Model.CEDescent
import Hagi.Model.CEGroupedScale
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Step.ProjectionDescent
import Hagi.Step.SafeQPStep
import Hagi.Optimization.MirrorHedge
import Hagi.Model.BatchCEDescentSafeStep

/-!
# BatchCEDescentFixtures

Concrete `mixedFeatures`/`sameZeroLabels` algebraic probes: cancellation, zero alignment, preserved batch loss, and positive sameZero descent.
-/

set_option relaxedAutoImplicit false

open scoped Matrix
open InnerProductSpace

namespace Hagi.Model.BatchCEDescent

/-- Two copies of identity features, used only as a finite algebraic probe. -/
abbrev mixedFeatures : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ := fun _ => 1

/-- The genuinely mixed-label sample `[0, 1]`, not a same-label witness. -/
def mixedLabels : Fin 2 → Fin 2 := fun i => if i = 0 then 0 else 1

/-- Empty batches have raw loss and all coefficients zero by Lean's division
convention; they are not included in the positive-range descent statement. -/
theorem empty_batch_convention {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 0 → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin 0 → V) :
    batchLoss X θ y = 0 ∧ batchMeanDirection X θ y = 0 ∧
      batchAlignment X θ y = 0 ∧ batchRangeSquare X θ y = 0 ∧
      batchSafeStep X θ y = 0 ∧ batchNextParameters X θ y = θ := by
  have hR : batchRangeSquare X θ y = 0 := by
    simp [batchRangeSquare]
  refine ⟨?_, ?_, ?_, hR, ?_, ?_⟩
  · simp [batchLoss, Hagi.Probability.FiniteFamilyConfidence.empiricalMean]
  · apply PiLp.ext
    intro j
    simp [batchMeanDirection_ofLp]
  · simp [batchAlignment, meanResidualTranspose]
  · exact batchSafeStep_of_rangeSquare_eq_zero X θ y hR
  · exact batchNextParameters_eq_of_rangeSquare_eq_zero X θ y hR

/-- At zero parameters the two own directions cancel exactly. -/
theorem mixed_own_directions_cancel :
    ceDirection (mixedFeatures 0) 0 (mixedLabels 0) +
      ceDirection (mixedFeatures 1) 0 (mixedLabels 1) = 0 := by
  apply PiLp.ext
  intro j
  fin_cases j <;>
    norm_num [mixedFeatures, mixedLabels, ceDirection, residualTranspose,
      ceResidual, ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The common mean direction, rather than the own directions, is zero. -/
theorem mixed_meanDirection_eq_zero :
    batchMeanDirection mixedFeatures 0 mixedLabels = 0 := by
  apply PiLp.ext
  intro j
  fin_cases j <;>
    norm_num [batchMeanDirection, mixedFeatures, mixedLabels, ceDirection,
      residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
      Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mixed_alignment_eq_zero :
    batchAlignment mixedFeatures 0 mixedLabels = 0 := by
  norm_num [batchAlignment, meanResidualTranspose, mixedFeatures, mixedLabels,
    residualTranspose, ceResidual, ceLogits, Hagi.Energy.smax,
    Hagi.Prelude.softDef, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The arithmetic mean of squared ranges is zero because the common direction
is zero, not because each own residual gradient was zero. -/
theorem mixed_rangeSquare_eq_zero :
    batchRangeSquare mixedFeatures 0 mixedLabels = 0 := by
  simp [batchRangeSquare, dirRange, ceLogits, mixed_meanDirection_eq_zero,
    Matrix.mulVec, dotProduct]

theorem mixed_safeStep_eq_zero :
    batchSafeStep mixedFeatures 0 mixedLabels = 0 :=
  batchSafeStep_of_rangeSquare_eq_zero _ _ _ mixed_rangeSquare_eq_zero

theorem mixed_nextParameters_eq_zero :
    batchNextParameters mixedFeatures 0 mixedLabels = 0 :=
  batchNextParameters_eq_of_rangeSquare_eq_zero _ _ _ mixed_rangeSquare_eq_zero

/-- Every initial two-class CE is exactly `log 2`. -/
theorem identity_CE_zero_parameters (t : Fin 2) :
    Hagi.ceOneHot t (ceLogits (1 : Matrix (Fin 2) (Fin 2) ℝ) 0) =
      Real.log 2 := by
  fin_cases t <;>
    norm_num [ceLogits, Hagi.ceOneHot, Hagi.Core.lse, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- The mixed-label mean stays exactly `log 2` after the common safe update. -/
theorem mixed_batchLoss_before_eq_log_two :
    batchLoss mixedFeatures 0 mixedLabels = Real.log 2 := by
  norm_num [batchLoss, Hagi.Probability.FiniteFamilyConfidence.empiricalMean,
    Fin.sum_univ_two, mixedFeatures, mixedLabels,
    identity_CE_zero_parameters]

theorem mixed_batchLoss_after_eq_log_two :
    batchLoss mixedFeatures (batchNextParameters mixedFeatures 0 mixedLabels)
      mixedLabels = Real.log 2 := by
  rw [batchNextParameters_eq_of_rangeSquare_eq_zero _ _ _
    mixed_rangeSquare_eq_zero]
  exact mixed_batchLoss_before_eq_log_two

theorem mixed_batchLoss_preserved :
    batchLoss mixedFeatures (batchNextParameters mixedFeatures 0 mixedLabels)
      mixedLabels = batchLoss mixedFeatures 0 mixedLabels :=
  batchLoss_batchNext_eq_of_rangeSquare_eq_zero _ _ _ mixed_rangeSquare_eq_zero

/-- The previous target-zero safe step is still a nonzero parameter update. -/
theorem old_target_zero_next :
    ceNextParameters (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
        (safeStepSize (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0) =
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (1 : ℝ) / 4 else -1 / 4) := by
  rw [identityTwoClass_safeStepSize_test]
  apply PiLp.ext
  intro i
  fin_cases i <;>
    norm_num [ceNextParameters, ceDirection, residualTranspose, ceResidual,
      ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- The old one-target update raises the mixed-label raw arithmetic mean,
exactly the failure avoided by zeroing the common-direction step. -/
theorem old_singleTarget_mixed_increases :
    batchLoss mixedFeatures 0 mixedLabels <
      batchLoss mixedFeatures
        (ceNextParameters (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
          (safeStepSize (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0)) mixedLabels := by
  rw [old_target_zero_next, mixed_batchLoss_before_eq_log_two]
  norm_num [batchLoss, Hagi.Probability.FiniteFamilyConfidence.empiricalMean,
    Fin.sum_univ_two, mixedFeatures, mixedLabels, ceLogits,
    Hagi.ceOneHot, Hagi.Core.lse, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hpos : (1 / 4 : ℝ) + 1 < Real.exp (1 / 4 : ℝ) :=
    Real.add_one_lt_exp (show (1 / 4 : ℝ) ≠ 0 by norm_num)
  have hnonneg : (-1 / 4 : ℝ) + 1 ≤ Real.exp (-1 / 4 : ℝ) :=
    Real.add_one_le_exp (-1 / 4)
  have hsum : (2 : ℝ) < Real.exp (1 / 4 : ℝ) + Real.exp (-1 / 4 : ℝ) := by
    nlinarith
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) hsum
  linarith

/-- A second same-label two-sample probe makes the strict-batch theorem
explicitly nonvacuous; it is additional to, not a replacement for, the mixed
zero-direction counterexample above. -/
def sameZeroLabels : Fin 2 → Fin 2 := fun _ => 0

theorem sameZero_alignment :
    batchAlignment mixedFeatures 0 sameZeroLabels = 1 / 2 := by
  norm_num [batchAlignment, meanResidualTranspose, mixedFeatures,
    sameZeroLabels, residualTranspose, ceResidual, ceLogits,
    Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

theorem sameZero_rangeSquare :
    batchRangeSquare mixedFeatures 0 sameZeroLabels = 4 := by
  norm_num [batchRangeSquare, batchMeanDirection, dirRange, mixedFeatures,
    sameZeroLabels, ceDirection, residualTranspose, ceResidual, ceLogits,
    Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

theorem sameZero_rangeSquare_pos :
    0 < batchRangeSquare mixedFeatures 0 sameZeroLabels := by
  rw [sameZero_rangeSquare]
  norm_num

theorem sameZero_safeStep :
    batchSafeStep mixedFeatures 0 sameZeroLabels = 1 / 2 := by
  rw [batchSafeStep, sameZero_rangeSquare, sameZero_alignment]
  norm_num

theorem sameZero_batchLoss_before :
    batchLoss mixedFeatures 0 sameZeroLabels = Real.log 2 := by
  norm_num [batchLoss, Hagi.Probability.FiniteFamilyConfidence.empiricalMean,
    Fin.sum_univ_two, mixedFeatures, sameZeroLabels,
    identity_CE_zero_parameters]

theorem sameZero_batchLoss_descent :
    batchLoss mixedFeatures
      (batchNextParameters mixedFeatures 0 sameZeroLabels) sameZeroLabels <
      batchLoss mixedFeatures 0 sameZeroLabels :=
  batchLoss_safeStep_lt _ _ _ sameZero_rangeSquare_pos

theorem sameZero_batchLoss_after_lt_log_two :
    batchLoss mixedFeatures
      (batchNextParameters mixedFeatures 0 sameZeroLabels) sameZeroLabels <
      Real.log 2 := by
  rw [← sameZero_batchLoss_before]
  exact sameZero_batchLoss_descent

/-! The common half-margin window is computed before any optional cap. -/


end Hagi.Model.BatchCEDescent
