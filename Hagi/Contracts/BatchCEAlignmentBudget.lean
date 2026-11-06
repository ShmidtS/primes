import Hagi.Contracts.BatchCETrajectory

/-!
# Feature curvature controls the sum of squared mean residuals

For a fixed finite feature batch, finite triangle inequalities and square-root
norm bounds control the actual common logit range by feature absolute mass and
the common mean-residual norm.  This
turns the trajectory's summed majorizer residuals into an explicit bound on
summed squared mean residuals.  A nonempty vocabulary is used for CE
nonnegativity; no IID, held-out, external-quality or hardware-cost premise is
introduced.

The Cesaro mean of the squared residuals tends to zero.  This does not assert
that every residual, the parameters, or the actual loss gap tends to zero.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BatchCEAlignmentBudget

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BatchCETrajectory
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Explicit full-feature mass curvature coefficient for a finite batch. -/
noncomputable def rangeCurvature (X : Fin B → Matrix V (Fin n) ℝ) : ℝ :=
  4 * (∑ b, (CEGroupedScale.featureAbsSum (X b)) ^ 2) / (B : ℝ)

/-- The feature curvature is nonnegative, including its empty-batch zero. -/
theorem rangeCurvature_nonneg (X : Fin B → Matrix V (Fin n) ℝ) :
    0 ≤ rangeCurvature X := by
  unfold rangeCurvature
  positivity

/-- One coordinate is bounded by the supplied finite squared norm. -/
theorem abs_coordinate_le_sqrt_sum_sq (D : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : |D.ofLp j| ≤ Real.sqrt (∑ i, D.ofLp i ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun i _hi => sq_nonneg (D.ofLp i))
    (Finset.mem_univ j)

/-- A directional logit is bounded by its own feature-row absolute mass and
the Euclidean norm of the direction. -/
theorem abs_ceLogits_le_rowMass_mul_sqrt (X : Matrix V (Fin n) ℝ)
    (D : EuclideanSpace ℝ (Fin n)) (v : V) :
    |ceLogits X D v| ≤ (∑ j, |X v j|) *
      Real.sqrt (∑ j, D.ofLp j ^ 2) := by
  change |∑ j, X v j * D.ofLp j| ≤ _
  calc
    |∑ j, X v j * D.ofLp j| ≤ ∑ j, |X v j * D.ofLp j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |X v j| * |D.ofLp j| := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [abs_mul]
    _ ≤ ∑ j, |X v j| * Real.sqrt (∑ i, D.ofLp i ^ 2) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (abs_coordinate_le_sqrt_sum_sq D j)
        (abs_nonneg (X v j))
    _ = (∑ j, |X v j|) * Real.sqrt (∑ j, D.ofLp j ^ 2) := by
      rw [Finset.sum_mul]

/-- Common-direction range at alignment `A` is bounded by feature mass and its
literal norm square, with no averaging of own-example alignments. -/
theorem dirRange_le_featureMass_mul_sqrt (X : Fin B → Matrix V (Fin n) ℝ)
    (θ : EuclideanSpace ℝ (Fin n)) (y : Fin B → V) (b : Fin B) :
    dirRange (X b) (batchMeanDirection X θ y) ≤
      2 * CEGroupedScale.featureAbsSum (X b) *
        Real.sqrt (batchAlignment X θ y) := by
  let D := batchMeanDirection X θ y
  have hDnorm : (∑ j, D.ofLp j ^ 2) = batchAlignment X θ y := by
    have hj : ∀ j, D.ofLp j = -meanResidualTranspose X θ y j := by
      intro j
      change (∑ b, (ceDirection (X b) θ (y b)).ofLp j) / (B : ℝ) =
        -meanResidualTranspose X θ y j
      simp only [ceDirection_ofLp, meanResidualTranspose, Finset.sum_neg_distrib]
      ring
    unfold batchAlignment
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hj j]
    ring
  calc
    dirRange (X b) D = 2 * ∑ v, |ceLogits (X b) D v| := rfl
    _ ≤ 2 * ∑ v, ((∑ j, |(X b) v j|) *
        Real.sqrt (∑ j, D.ofLp j ^ 2)) := by
      gcongr with v
      exact abs_ceLogits_le_rowMass_mul_sqrt (X b) D v
    _ = 2 * CEGroupedScale.featureAbsSum (X b) *
        Real.sqrt (batchAlignment X θ y) := by
      rw [← Finset.sum_mul, hDnorm, CEGroupedScale.featureAbsSum]
      ring

/-- Feature curvature controls the actual mean squared common-direction range,
including empty batches under Lean's natural `0 / 0 = 0` convention. -/
theorem batchRangeSquare_le_rangeCurvature_mul_alignment
    (X : Fin B → Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n))
    (y : Fin B → V) :
    batchRangeSquare X θ y ≤ rangeCurvature X * batchAlignment X θ y := by
  have hA : 0 ≤ batchAlignment X θ y := batchAlignment_nonneg X θ y
  have hpoint (b : Fin B) :
      (dirRange (X b) (batchMeanDirection X θ y)) ^ 2 ≤
        (2 * CEGroupedScale.featureAbsSum (X b) *
          Real.sqrt (batchAlignment X θ y)) ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self (dirRange_nonneg (X b) (batchMeanDirection X θ y))
        (dirRange_le_featureMass_mul_sqrt X θ y b)
  calc
    batchRangeSquare X θ y =
        (∑ b, (dirRange (X b) (batchMeanDirection X θ y)) ^ 2) / (B : ℝ) := rfl
    _ ≤ (∑ b, (2 * CEGroupedScale.featureAbsSum (X b) *
        Real.sqrt (batchAlignment X θ y)) ^ 2) / (B : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun b _hb => hpoint b)
        (Nat.cast_nonneg B)
    _ = rangeCurvature X * batchAlignment X θ y := by
      have hs := Real.sq_sqrt hA
      have heq : (∑ b, (2 * CEGroupedScale.featureAbsSum (X b) *
          Real.sqrt (batchAlignment X θ y)) ^ 2) =
          4 * (∑ b, (CEGroupedScale.featureAbsSum (X b)) ^ 2) *
            batchAlignment X θ y := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _hb
        calc
          (2 * CEGroupedScale.featureAbsSum (X b) *
              Real.sqrt (batchAlignment X θ y)) ^ 2 =
              4 * CEGroupedScale.featureAbsSum (X b) ^ 2 *
                Real.sqrt (batchAlignment X θ y) ^ 2 := by ring
          _ = 4 * CEGroupedScale.featureAbsSum (X b) ^ 2 *
              batchAlignment X θ y := by rw [hs]
      rw [heq, rangeCurvature]
      ring

/-- Zero mean common range forces zero common gradient alignment.  Zero
directional logits make every samplewise action zero; averaging gives minus
alignment, hence alignment itself is zero.  This is not inferred merely from
an arbitrary vector being in a feature nullspace. -/
theorem batchAlignment_eq_zero_of_rangeSquare_eq_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n))
    (y : Fin B → V) (hR : batchRangeSquare X θ y = 0) :
    batchAlignment X θ y = 0 := by
  have hzero (b : Fin B) : dirRange (X b) (batchMeanDirection X θ y) = 0 := by
    have hB : B ≠ 0 := by
      intro hB
      subst B
      exact Fin.elim0 b
    have hsum : (∑ c, (dirRange (X c) (batchMeanDirection X θ y)) ^ 2) = 0 := by
      unfold batchRangeSquare at hR
      exact (div_eq_zero_iff.mp hR).resolve_right (Nat.cast_ne_zero.mpr hB)
    have hsq : (dirRange (X b) (batchMeanDirection X θ y)) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun c _hc => sq_nonneg _)).mp hsum b (Finset.mem_univ b)
    exact sq_eq_zero_iff.mp hsq
  have hlogits (b : Fin B) (v : V) :
      ceLogits (X b) (batchMeanDirection X θ y) v = 0 :=
    (dirRange_eq_zero_iff (X b) (batchMeanDirection X θ y)).mp (hzero b) v
  have haction : batchMeanAction X θ y (batchMeanDirection X θ y) = 0 := by
    simp [batchMeanAction, dirAction, hlogits]
  have hcommon := batchMeanAction_common X θ y
  linarith

/-- The explicitly positive feature-curvature divisor converts a certified
safe-step residual into a lower bound on the common squared mean residual. -/
theorem alignment_le_scaled_certifiedDrop
    (X : Fin B → Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n))
    (y : Fin B → V) :
    2 * batchAlignment X θ y / (rangeCurvature X + 1) ≤
      batchCertifiedDrop X θ y := by
  by_cases hR : batchRangeSquare X θ y = 0
  · rw [batchAlignment_eq_zero_of_rangeSquare_eq_zero X θ y hR,
      batchCertifiedDrop, hR]
    norm_num
  · have hRpos : 0 < batchRangeSquare X θ y :=
      lt_of_le_of_ne (batchRangeSquare_nonneg X θ y) (Ne.symm hR)
    have hA : 0 ≤ batchAlignment X θ y := batchAlignment_nonneg X θ y
    have hK : 0 < rangeCurvature X + 1 := by
      have := rangeCurvature_nonneg X
      linarith
    have hcurve : batchRangeSquare X θ y ≤
        (rangeCurvature X + 1) * batchAlignment X θ y := by
      calc
        batchRangeSquare X θ y ≤ rangeCurvature X * batchAlignment X θ y :=
          batchRangeSquare_le_rangeCurvature_mul_alignment X θ y
        _ ≤ (rangeCurvature X + 1) * batchAlignment X θ y := by
          nlinarith
    have hmul := mul_le_mul_of_nonneg_left hcurve
      (mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) hA)
    rw [batchCertifiedDrop, ite_eq_right hR]
    apply (div_le_div_iff₀ hK hRpos).2
    calc
      2 * batchAlignment X θ y * batchRangeSquare X θ y ≤
          (2 * batchAlignment X θ y) *
            ((rangeCurvature X + 1) * batchAlignment X θ y) := hmul
      _ = 2 * batchAlignment X θ y ^ 2 * (rangeCurvature X + 1) := by ring

/-- Finite batch residual budget: mean CE loss dominates the explicitly
curvature-weighted sum of common squared mean residuals. -/
theorem fixedBatch_weighted_sum_alignment_le_initial [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    (2 / (rangeCurvature X + 1)) *
        ∑ t ∈ Finset.range T, batchAlignment X
          (coreParameters (fixedBatchState X y S opCost opRisk write t)) y ≤
      batchCEObjective X y S := by
  have hterms := Finset.sum_le_sum (fun t (_ht : t ∈ Finset.range T) =>
    alignment_le_scaled_certifiedDrop X
      (coreParameters (fixedBatchState X y S opCost opRisk write t)) y)
  have hmaj := fixedBatchObjective_sum_certifiedDrop_le_telescope
    X y S opCost opRisk write T
  have hloss := fixedBatchObjective_nonneg X y S opCost opRisk write T
  calc
    (2 / (rangeCurvature X + 1)) *
        ∑ t ∈ Finset.range T, batchAlignment X
          (coreParameters (fixedBatchState X y S opCost opRisk write t)) y =
        ∑ t ∈ Finset.range T,
          2 * batchAlignment X
            (coreParameters (fixedBatchState X y S opCost opRisk write t)) y /
            (rangeCurvature X + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _ht
          ring
    _ ≤ ∑ t ∈ Finset.range T, batchCertifiedDrop X
        (coreParameters (fixedBatchState X y S opCost opRisk write t)) y := hterms
    _ ≤ batchCEObjective X y S -
        fixedBatchObjective X y S opCost opRisk write T := hmaj
    _ ≤ batchCEObjective X y S := by linarith

/-- The unweighted finite sum has the explicit trajectory-independent upper
bound `(curvature + 1) / 2` times initial mean CE. -/
theorem fixedBatch_sum_alignment_le_initial [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ t ∈ Finset.range T, batchAlignment X
        (coreParameters (fixedBatchState X y S opCost opRisk write t)) y ≤
      ((rangeCurvature X + 1) / 2) * batchCEObjective X y S := by
  have hK : 0 < rangeCurvature X + 1 := by
    have := rangeCurvature_nonneg X
    linarith
  have hw := fixedBatch_weighted_sum_alignment_le_initial
    X y S opCost opRisk write T
  have hmul := mul_le_mul_of_nonneg_left hw
    (div_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 2))
  calc
    ∑ t ∈ Finset.range T, batchAlignment X
        (coreParameters (fixedBatchState X y S opCost opRisk write t)) y =
        ((rangeCurvature X + 1) / 2) * ((2 / (rangeCurvature X + 1)) *
          ∑ t ∈ Finset.range T, batchAlignment X
            (coreParameters (fixedBatchState X y S opCost opRisk write t)) y) := by
      field_simp [ne_of_gt hK]
    _ ≤ ((rangeCurvature X + 1) / 2) * batchCEObjective X y S := hmul

/-- Arithmetic mean of actual common squared residuals through time `T`. -/
noncomputable def fixedAlignmentCesaro
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, batchAlignment X
    (coreParameters (fixedBatchState X y S opCost opRisk write t)) y) / (T : ℝ)

/-- Every finite Cesaro average is nonnegative. -/
theorem fixedAlignmentCesaro_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    0 ≤ fixedAlignmentCesaro X y S opCost opRisk write T := by
  unfold fixedAlignmentCesaro
  exact div_nonneg (Finset.sum_nonneg fun t _ht => batchAlignment_nonneg _ _ _)
    (Nat.cast_nonneg T)

/-- The average is at most a fixed numerator divided by the time index,
including the empty prefix under the raw division convention. -/
theorem fixedAlignmentCesaro_le [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    fixedAlignmentCesaro X y S opCost opRisk write T ≤
      (((rangeCurvature X + 1) / 2) * batchCEObjective X y S) / (T : ℝ) := by
  unfold fixedAlignmentCesaro
  exact div_le_div_of_nonneg_right
    (fixedBatch_sum_alignment_le_initial X y S opCost opRisk write T)
    (Nat.cast_nonneg T)

/-- The common squared mean residual is zero on average in the Cesaro limit.
This is weaker than asserting residuals or parameters converge pointwise. -/
theorem fixedAlignmentCesaro_tendsto_zero [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fixedAlignmentCesaro X y S opCost opRisk write) atTop (𝓝 0) := by
  apply squeeze_zero (fixedAlignmentCesaro_nonneg X y S opCost opRisk write)
    (fixedAlignmentCesaro_le X y S opCost opRisk write)
  exact tendsto_const_div_atTop_nhds_zero_nat _

end Hagi.Contracts.BatchCEAlignmentBudget
