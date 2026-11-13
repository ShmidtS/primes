import Hagi.Model.CEDescent
import Hagi.Model.CEGroupedScale
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Step.ProjectionDescent
import Hagi.Step.SafeQPStep
import Hagi.Optimization.MirrorHedge
import Hagi.Model.BatchCEDescentDirection

/-!
# BatchCEDescentSafeStep

Batch safe step: `batchMeanAction`, `batchSafeStep`, `batchMajorizer`, `batchNextParameters`, and their descent certificates.
-/

set_option relaxedAutoImplicit false

open scoped Matrix
open InnerProductSpace

namespace Hagi.Model.BatchCEDescent

/-- Averaging the exact actions on the common direction gives minus its
alignment.  At `B = 0` both sides are the algebra convention zero. -/
theorem batchMeanAction_common {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) :
    batchMeanAction X θ y (batchMeanDirection X θ y) =
      -batchAlignment X θ y := by
  classical
  by_cases hB : B = 0
  · subst B
    simp [batchMeanAction, batchAlignment, meanResidualTranspose]
  have hBreal : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB
  have hdir_at (b : Fin B) :
      dirAction (X b) θ (y b) (batchMeanDirection X θ y) =
        -∑ j, residualTranspose (X b) θ (y b) j *
          meanResidualTranspose X θ y j := by
    rw [dirAction_eq_dot, batchMeanDirection_eq_neg_meanResidualTranspose]
    simp only [meanResidualTranspose]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hsum : (∑ b, dirAction (X b) θ (y b) (batchMeanDirection X θ y)) =
      -∑ j, (∑ b, residualTranspose (X b) θ (y b) j) *
        meanResidualTranspose X θ y j := by
    rw [Finset.sum_congr rfl (fun b _hb => hdir_at b), Finset.sum_neg_distrib,
      Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Finset.sum_mul]
  have hcoord (j : Fin d) :
      (∑ b, residualTranspose (X b) θ (y b) j) =
        (B : ℝ) * meanResidualTranspose X θ y j := by
    simp only [meanResidualTranspose]
    field_simp
  have havg :
      (∑ j, (∑ b, residualTranspose (X b) θ (y b) j) *
        meanResidualTranspose X θ y j) / (B : ℝ) =
      ∑ j, (meanResidualTranspose X θ y j) ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hcoord j]
    field_simp
  unfold batchMeanAction batchAlignment
  rw [hsum, neg_div, havg]

/-- Both scalar batch coefficients are nonnegative. -/
theorem batchAlignment_nonneg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : 0 ≤ batchAlignment X θ y := by
  unfold batchAlignment
  positivity

theorem batchRangeSquare_nonneg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : 0 ≤ batchRangeSquare X θ y := by
  unfold batchRangeSquare
  positivity

/-- Positive range-square belongs to the genuinely nonempty-batch class. -/
theorem batch_pos_of_rangeSquare_pos
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchRangeSquare X θ y) : 0 < B := by
  apply Nat.pos_of_ne_zero
  intro hB
  subst B
  simp [batchRangeSquare] at hR

/-- Zero mean alignment collapses the common direction itself to zero. -/
theorem batchMeanDirection_eq_zero_of_alignment_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hA : batchAlignment X θ y = 0) :
    batchMeanDirection X θ y = 0 := by
  have hm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      meanResidualTranspose X θ y j = 0 := by
    apply (Finset.sum_sq_eq_zero_iff Finset.univ
      (meanResidualTranspose X θ y)).mp
    simpa [batchAlignment] using hA
  rw [batchMeanDirection_eq_neg_meanResidualTranspose]
  apply PiLp.ext
  intro j
  simp [hm j (Finset.mem_univ j)]

/-- Positive mean common-direction range-square forces positive alignment by
forcing the common direction to be nonzero; positivity is not an assumption. -/
theorem batchAlignment_pos_of_rangeSquare_pos
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchRangeSquare X θ y) :
    0 < batchAlignment X θ y := by
  apply lt_of_le_of_ne (batchAlignment_nonneg X θ y)
  intro hne
  have hA : batchAlignment X θ y = 0 := hne.symm
  have hD := batchMeanDirection_eq_zero_of_alignment_eq_zero X θ y hA
  have hR0 : batchRangeSquare X θ y = 0 := by
    simp [batchRangeSquare, dirRange, ceLogits, hD, Matrix.mulVec, dotProduct]
  exact (ne_of_gt hR) hR0

/-- Safe minimizer of the common-direction averaged quadratic majorizer. -/
noncomputable def batchSafeStep {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : ℝ :=
  if batchRangeSquare X θ y = 0 then 0
  else 4 * batchAlignment X θ y / batchRangeSquare X θ y

/-- Averaged majorizer for one common step. -/
noncomputable def batchMajorizer {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (eta : ℝ) : ℝ :=
  batchLoss X θ y - eta * batchAlignment X θ y
    + eta ^ 2 * batchRangeSquare X θ y / 8

/-- The actual parameter update shared by every sample. -/
noncomputable def batchNextParameters {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : EuclideanSpace ℝ (Fin d) :=
  alongNext θ (batchMeanDirection X θ y) (batchSafeStep X θ y)

/-- Average the general individual bounds, all evaluated along the same common
direction.  No universal per-example descent is asserted. -/
theorem batchLoss_alongNext_le_batchMajorizer
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) {eta : ℝ} (heta : 0 ≤ eta) :
    batchLoss X (alongNext θ (batchMeanDirection X θ y) eta) y ≤
      batchMajorizer X θ y eta := by
  let D := batchMeanDirection X θ y
  have hsum : (∑ b, Hagi.ceOneHot (y b)
        (ceLogits (X b) (alongNext θ D eta))) ≤
      ∑ b, (Hagi.ceOneHot (y b) (ceLogits (X b) θ)
        + eta * dirAction (X b) θ (y b) D
        + (eta * dirRange (X b) D) ^ 2 / 8) := by
    exact Finset.sum_le_sum (fun b _hb =>
      ceOneHot_alongNext_le (X b) θ D (y b) heta)
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
  have hsumAction :
      (∑ b, eta * dirAction (X b) θ (y b) D) =
        eta * ∑ b, dirAction (X b) θ (y b) D := by
    rw [Finset.mul_sum]
  have hsumRange :
      (∑ b, (eta * dirRange (X b) D) ^ 2 / 8) =
        eta ^ 2 * (∑ b, (dirRange (X b) D) ^ 2) / 8 := by
    calc
      (∑ b, (eta * dirRange (X b) D) ^ 2 / 8) =
          ∑ b, eta ^ 2 * ((dirRange (X b) D) ^ 2 / 8) := by
        apply Finset.sum_congr rfl
        intro b _hb
        ring
      _ = eta ^ 2 * ∑ b, (dirRange (X b) D) ^ 2 / 8 := by
        rw [Finset.mul_sum]
      _ = eta ^ 2 * ((∑ b, (dirRange (X b) D) ^ 2) / 8) := by
        rw [Finset.sum_div]
      _ = eta ^ 2 * (∑ b, (dirRange (X b) D) ^ 2) / 8 := by ring
  simp only [Finset.sum_add_distrib, hsumAction, hsumRange] at hdiv
  have hmean := batchMeanAction_common X θ y
  unfold batchMeanAction at hmean
  dsimp [D] at hdiv hmean
  unfold batchMajorizer batchLoss batchRangeSquare
  unfold Hagi.Probability.FiniteFamilyConfidence.empiricalMean
  calc
    (∑ b, Hagi.ceOneHot (y b)
        (ceLogits (X b) (alongNext θ (batchMeanDirection X θ y) eta))) /
        (B : ℝ) ≤
      (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)
        + eta * (∑ b, dirAction (X b) θ (y b) (batchMeanDirection X θ y))
        + eta ^ 2 * (∑ b, (dirRange (X b) (batchMeanDirection X θ y)) ^ 2) / 8) /
        (B : ℝ) := hdiv
    _ = (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)) / (B : ℝ)
        - eta * batchAlignment X θ y
        + eta ^ 2 *
          ((∑ b, (dirRange (X b) (batchMeanDirection X θ y)) ^ 2) / (B : ℝ)) / 8 := by
      linear_combination eta * hmean


/-- Positive range-square makes the selected common step positive. -/
theorem batchSafeStep_pos_of_rangeSquare_pos
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchRangeSquare X θ y) :
    0 < batchSafeStep X θ y := by
  have hA := batchAlignment_pos_of_rangeSquare_pos X θ y hR
  rw [batchSafeStep, ite_eq_right (ne_of_gt hR)]
  exact div_pos (by positivity) hR

/-- The zero-range branch and all positive-range branches are nonnegative. -/
theorem batchSafeStep_nonneg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : 0 ≤ batchSafeStep X θ y := by
  by_cases hR : batchRangeSquare X θ y = 0
  · simp [batchSafeStep, hR]
  · have hRpos : 0 < batchRangeSquare X θ y :=
      lt_of_le_of_ne (batchRangeSquare_nonneg X θ y) (Ne.symm hR)
    exact (batchSafeStep_pos_of_rangeSquare_pos X θ y hRpos).le

/-- Exact minimizer residual for the averaged majorizer. -/
theorem batchMajorizer_safeStep_eq {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (hR : 0 < batchRangeSquare X θ y) :
    batchMajorizer X θ y (batchSafeStep X θ y) =
      batchLoss X θ y
        - 2 * (batchAlignment X θ y) ^ 2 / batchRangeSquare X θ y := by
  simp only [batchMajorizer, batchSafeStep, ite_eq_right (ne_of_gt hR)]
  field_simp
  ring

/-- The common safe step minimizes the averaged majorizer over every real eta. -/
theorem batchMajorizer_safeStep_le {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (hR : 0 < batchRangeSquare X θ y) (eta : ℝ) :
    batchMajorizer X θ y (batchSafeStep X θ y) ≤
      batchMajorizer X θ y eta := by
  have hne : batchRangeSquare X θ y ≠ 0 := ne_of_gt hR
  have hdiff : batchMajorizer X θ y eta
      - batchMajorizer X θ y (batchSafeStep X θ y) =
      batchRangeSquare X θ y / 8 *
        (eta - 4 * batchAlignment X θ y / batchRangeSquare X θ y) ^ 2 := by
    simp only [batchMajorizer, batchSafeStep, ite_eq_right hne]
    field_simp
    ring
  have hsquare : 0 ≤ batchRangeSquare X θ y / 8 *
      (eta - 4 * batchAlignment X θ y / batchRangeSquare X θ y) ^ 2 := by
    positivity
  linarith

/-- Averaged actual CE, not only its majorizer, obeys the exact residual bound. -/
theorem batchLoss_safeStep_le_residual {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (hR : 0 < batchRangeSquare X θ y) :
    batchLoss X (batchNextParameters X θ y) y ≤
      batchLoss X θ y
        - 2 * (batchAlignment X θ y) ^ 2 / batchRangeSquare X θ y := by
  rw [← batchMajorizer_safeStep_eq X θ y hR]
  exact batchLoss_alongNext_le_batchMajorizer X θ y (batchSafeStep_nonneg X θ y)

/-- Positive mean range-square gives strict descent of the arithmetic mean CE
for the supplied batch, including mixed labels, at the common safe update. -/
theorem batchLoss_safeStep_lt {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (hR : 0 < batchRangeSquare X θ y) :
    batchLoss X (batchNextParameters X θ y) y < batchLoss X θ y := by
  have hA := batchAlignment_pos_of_rangeSquare_pos X θ y hR
  have hbound := batchLoss_safeStep_le_residual X θ y hR
  have hpos : 0 < 2 * (batchAlignment X θ y) ^ 2 /
      batchRangeSquare X θ y := by positivity
  linarith

@[simp] theorem batchSafeStep_of_rangeSquare_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : batchRangeSquare X θ y = 0) :
    batchSafeStep X θ y = 0 := by
  simp [batchSafeStep, hR]

/-- At zero mean range-square the *selected* update is exactly zero.  Thus it
preserves every logit and every loss, with no fabricated positive certificate. -/
theorem batchNextParameters_eq_of_rangeSquare_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : batchRangeSquare X θ y = 0) :
    batchNextParameters X θ y = θ := by
  rw [batchNextParameters, batchSafeStep_of_rangeSquare_eq_zero X θ y hR,
    alongNext_zero]

theorem ceLogits_batchNext_eq_of_rangeSquare_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : batchRangeSquare X θ y = 0) (b : Fin B) :
    ceLogits (X b) (batchNextParameters X θ y) = ceLogits (X b) θ := by
  rw [batchNextParameters_eq_of_rangeSquare_eq_zero X θ y hR]

theorem batchLoss_batchNext_eq_of_rangeSquare_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : batchRangeSquare X θ y = 0) :
    batchLoss X (batchNextParameters X θ y) y = batchLoss X θ y := by
  rw [batchNextParameters_eq_of_rangeSquare_eq_zero X θ y hR]


end Hagi.Model.BatchCEDescent
