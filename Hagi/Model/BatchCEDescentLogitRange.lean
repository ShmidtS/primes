import Hagi.Model.CEDescent
import Hagi.Model.CEGroupedScale
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Step.ProjectionDescent
import Hagi.Step.SafeQPStep
import Hagi.Optimization.MirrorHedge
import Hagi.Model.BatchCEDescentResidualNorm

/-!
# BatchCEDescentLogitRange

Logit-range family incl. the C223 MAIN theorems: `dirLogitRange`, `batchLogitRangeSquare`, `batchLogitSafeStep`/`Majorizer`/`NextParameters`, and comparison with the existing engine. Split from `BatchCEDescent` (C257).
-/

set_option relaxedAutoImplicit false

open scoped Matrix
open InnerProductSpace

namespace Hagi.Model.BatchCEDescent

open scoped Classical BigOperators Matrix
open Hagi.Probability




/-! ## Per-example logit range of an arbitrary direction -/

/-- The logit RANGE of a one-unit directional displacement:
`sup d − inf d`, written as `sup' d + sup' (-d)` (C216 pattern). -/
noncomputable def dirLogitRange {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (D : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty
      (fun v => ceLogits X D v)
  + Finset.sup' Finset.univ Finset.univ_nonempty
      (fun v => -ceLogits X D v)

theorem dirLogitRange_nonneg {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (D : EuclideanSpace ℝ (Fin d)) :
    0 ≤ dirLogitRange X D := by
  obtain ⟨v₀, _⟩ : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have h1 : ceLogits X D v₀ ≤
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun v => ceLogits X D v) :=
    Finset.le_sup' _ (Finset.mem_univ v₀)
  have h2 : -ceLogits X D v₀ ≤
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun w => -ceLogits X D w) :=
    Finset.le_sup' (fun w => -ceLogits X D w) (Finset.mem_univ v₀)
  unfold dirLogitRange
  linarith

/-- The range bounds every pairwise difference of directional logits. -/
theorem dirLogit_sub_le {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (D : EuclideanSpace ℝ (Fin d)) (u v : V) :
    ceLogits X D u - ceLogits X D v ≤ dirLogitRange X D := by
  have h1 : ceLogits X D u ≤
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun w => ceLogits X D w) :=
    Finset.le_sup' _ (Finset.mem_univ u)
  have h2 : -ceLogits X D v ≤
      Finset.sup' Finset.univ Finset.univ_nonempty
        (fun w => -ceLogits X D w) :=
    Finset.le_sup' (fun w => -ceLogits X D w) (Finset.mem_univ v)
  unfold dirLogitRange
  linarith

/-- The actual eta-scaled displacement has pairwise difference at most
`eta * dirLogitRange`, feeding `lse_shift_upper` (batch mirror of
C216 `ce_logitDisplacement_range`). -/
theorem dir_logitDisplacement_logitRange {V : Type} [Fintype V] [Nonempty V]
    {d : ℕ} (X : Matrix V (Fin d) ℝ) (θ D : EuclideanSpace ℝ (Fin d))
    {eta : ℝ} (heta : 0 ≤ eta) (u v : V) :
    (ceLogits X (alongNext θ D eta) u - ceLogits X θ u)
      - (ceLogits X (alongNext θ D eta) v - ceLogits X θ v)
      ≤ eta * dirLogitRange X D := by
  rw [ceLogits_alongNext_apply, ceLogits_alongNext_apply]
  have h := mul_le_mul_of_nonneg_left
    (dirLogit_sub_le X D u v) heta
  ring_nf
  linarith

/-- The sharp range never exceeds the engine's vocabulary-abs-sum range. -/
theorem dirLogitRange_le_dirRange {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (D : EuclideanSpace ℝ (Fin d)) :
    dirLogitRange X D ≤ dirRange X D := by
  have h1 : Finset.sup' Finset.univ Finset.univ_nonempty
        (fun v => ceLogits X D v)
      ≤ ∑ v, |ceLogits X D v| := by
    refine (Finset.sup'_le_iff Finset.univ_nonempty _).mpr fun v _hv => ?_
    exact le_trans (le_abs_self _) (Finset.single_le_sum
      (f := fun z => |ceLogits X D z|)
      (fun z _hz => abs_nonneg _) (Finset.mem_univ v))
  have h2 : Finset.sup' Finset.univ Finset.univ_nonempty
        (fun v => -ceLogits X D v)
      ≤ ∑ v, |ceLogits X D v| := by
    refine (Finset.sup'_le_iff Finset.univ_nonempty _).mpr fun v _hv => ?_
    exact le_trans (neg_le_abs _) (Finset.single_le_sum
      (f := fun z => |ceLogits X D z|)
      (fun z _hz => abs_nonneg _) (Finset.mem_univ v))
  unfold dirLogitRange dirRange
  linarith

/-- Vanishing directional logits force vanishing range. -/
theorem dirLogitRange_eq_zero_of_forall_eq_zero
    {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (D : EuclideanSpace ℝ (Fin d))
    (h : ∀ v, ceLogits X D v = 0) :
    dirLogitRange X D = 0 := by
  have hneg : ∀ v, -ceLogits X D v = 0 := fun v => by rw [h v]; ring
  unfold dirLogitRange
  rw [Finset.sup'_congr Finset.univ_nonempty rfl (fun v _hv => h v),
    Finset.sup'_congr Finset.univ_nonempty rfl (fun v _hv => hneg v)]
  simp

/-- Range-based per-example Böhning bound: same assembly as
`ceOneHot_alongNext_le`, with the sharp range. -/
theorem ceOneHot_alongNext_le_logitRange
    {V : Type} [Fintype V] [Nonempty V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ D : EuclideanSpace ℝ (Fin d))
    (t : V) {eta : ℝ} (heta : 0 ≤ eta) :
    Hagi.ceOneHot t (ceLogits X (alongNext θ D eta)) ≤
      Hagi.ceOneHot t (ceLogits X θ) + eta * dirAction X θ t D
        + (eta * dirLogitRange X D) ^ 2 / 8 := by
  have hlse := Hagi.Energy.lse_shift_upper (ceLogits X θ)
    (ceLogits X (alongNext θ D eta)) (eta * dirLogitRange X D)
    (dir_logitDisplacement_logitRange X θ D heta)
  have hlin := dir_first_order_eq X θ D t eta
  have ht := ceLogits_alongNext_apply X θ D eta t
  classical
  have honehot : ∑ v, (if v = t then (1 : ℝ) else 0) *
      (ceLogits X (alongNext θ D eta) v - ceLogits X θ v) =
      ceLogits X (alongNext θ D eta) t - ceLogits X θ t := by
    simp
  simp only [ceResidual, sub_mul, Finset.sum_sub_distrib] at hlin
  rw [honehot, ht] at hlin
  have hsoft : ∑ v, Hagi.Energy.smax (ceLogits X θ) v *
      (ceLogits X (alongNext θ D eta) v - ceLogits X θ v) =
      eta * dirAction X θ t D + eta * ceLogits X D t := by
    linarith
  rw [hsoft] at hlse
  unfold Hagi.ceOneHot Hagi.Core.lse
  rw [ht]
  linarith

/-! ## Batch-level range-square quantities -/

/-- Arithmetic mean of the squared sharp ranges of the common direction. -/
noncomputable def batchLogitRangeSquare {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) : ℝ :=
  (∑ b, (dirLogitRange (X b) (batchMeanDirection X θ y)) ^ 2) / (B : ℝ)

theorem batchLogitRangeSquare_nonneg {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) :
    0 ≤ batchLogitRangeSquare X θ y := by
  unfold batchLogitRangeSquare
  positivity

/-- Positive logit-range-square belongs to the genuinely nonempty batch. -/
theorem batch_pos_of_logitRangeSquare_pos
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchLogitRangeSquare X θ y) : 0 < B := by
  apply Nat.pos_of_ne_zero
  intro hB
  subst B
  simp [batchLogitRangeSquare] at hR

/-- Positive mean sharp range-square forces positive alignment (mirror of
`batchAlignment_pos_of_rangeSquare_pos`). -/
theorem batchAlignment_pos_of_logitRangeSquare_pos
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchLogitRangeSquare X θ y) :
    0 < batchAlignment X θ y := by
  apply lt_of_le_of_ne (batchAlignment_nonneg X θ y)
  intro hne
  have hA : batchAlignment X θ y = 0 := hne.symm
  have hD := batchMeanDirection_eq_zero_of_alignment_eq_zero X θ y hA
  have hR0 : batchLogitRangeSquare X θ y = 0 := by
    unfold batchLogitRangeSquare
    apply div_eq_zero_iff.mpr
    left
    apply Finset.sum_eq_zero
    intro b _hb
    rw [dirLogitRange_eq_zero_of_forall_eq_zero (X b)
      (batchMeanDirection X θ y)
      (fun v => by simp [ceLogits, hD, Matrix.mulVec, dotProduct])]
    ring
  exact (ne_of_gt hR) hR0

/-- Safe minimizer of the sharp-range averaged quadratic majorizer. -/
noncomputable def batchLogitSafeStep {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) : ℝ :=
  if batchLogitRangeSquare X θ y = 0 then 0
  else 4 * batchAlignment X θ y / batchLogitRangeSquare X θ y

/-- Sharp-range averaged quadratic majorizer. -/
noncomputable def batchLogitMajorizer {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) (eta : ℝ) : ℝ :=
  batchLoss X θ y - eta * batchAlignment X θ y
    + eta ^ 2 * batchLogitRangeSquare X θ y / 8

/-- The range-based common update. -/
noncomputable def batchLogitNextParameters {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) :
    EuclideanSpace ℝ (Fin d) :=
  alongNext θ (batchMeanDirection X θ y) (batchLogitSafeStep X θ y)

/-- Averaging the sharp per-example bounds (mirror of
`batchLoss_alongNext_le_batchMajorizer`). -/
theorem batchLoss_alongNext_le_batchLogitMajorizer
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) {eta : ℝ} (heta : 0 ≤ eta) :
    batchLoss X (alongNext θ (batchMeanDirection X θ y) eta) y ≤
      batchLogitMajorizer X θ y eta := by
  let D := batchMeanDirection X θ y
  have hsum : (∑ b, Hagi.ceOneHot (y b)
        (ceLogits (X b) (alongNext θ D eta))) ≤
      ∑ b, (Hagi.ceOneHot (y b) (ceLogits (X b) θ)
        + eta * dirAction (X b) θ (y b) D
        + (eta * dirLogitRange (X b) D) ^ 2 / 8) := by
    exact Finset.sum_le_sum (fun b _hb =>
      ceOneHot_alongNext_le_logitRange (X b) θ D (y b) heta)
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
  have hsumAction :
      (∑ b, eta * dirAction (X b) θ (y b) D) =
        eta * ∑ b, dirAction (X b) θ (y b) D := by
    rw [Finset.mul_sum]
  have hsumRange :
      (∑ b, (eta * dirLogitRange (X b) D) ^ 2 / 8) =
        eta ^ 2 * (∑ b, (dirLogitRange (X b) D) ^ 2) / 8 := by
    calc
      (∑ b, (eta * dirLogitRange (X b) D) ^ 2 / 8) =
          ∑ b, eta ^ 2 * ((dirLogitRange (X b) D) ^ 2 / 8) := by
        apply Finset.sum_congr rfl
        intro b _hb
        ring
      _ = eta ^ 2 * ∑ b, (dirLogitRange (X b) D) ^ 2 / 8 := by
        rw [Finset.mul_sum]
      _ = eta ^ 2 * ((∑ b, (dirLogitRange (X b) D) ^ 2) / 8) := by
        rw [Finset.sum_div]
      _ = eta ^ 2 * (∑ b, (dirLogitRange (X b) D) ^ 2) / 8 := by ring
  simp only [Finset.sum_add_distrib, hsumAction, hsumRange] at hdiv
  have hmean := batchMeanAction_common X θ y
  unfold batchMeanAction at hmean
  dsimp [D] at hdiv hmean
  unfold batchLogitMajorizer batchLoss batchLogitRangeSquare
  unfold Hagi.Probability.FiniteFamilyConfidence.empiricalMean
  calc
    (∑ b, Hagi.ceOneHot (y b)
        (ceLogits (X b) (alongNext θ (batchMeanDirection X θ y) eta))) /
        (B : ℝ) ≤
      (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)
        + eta * (∑ b, dirAction (X b) θ (y b) (batchMeanDirection X θ y))
        + eta ^ 2 * (∑ b, (dirLogitRange (X b)
            (batchMeanDirection X θ y)) ^ 2) / 8) /
        (B : ℝ) := hdiv
    _ = (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)) / (B : ℝ)
        - eta * batchAlignment X θ y
        + eta ^ 2 *
          ((∑ b, (dirLogitRange (X b)
              (batchMeanDirection X θ y)) ^ 2) / (B : ℝ)) / 8 := by
      linear_combination eta * hmean

theorem batchLogitSafeStep_nonneg {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) :
    0 ≤ batchLogitSafeStep X θ y := by
  by_cases hR : batchLogitRangeSquare X θ y = 0
  · simp [batchLogitSafeStep, hR]
  · have hRpos : 0 < batchLogitRangeSquare X θ y :=
      lt_of_le_of_ne (batchLogitRangeSquare_nonneg X θ y) (Ne.symm hR)
    have hA := batchAlignment_pos_of_logitRangeSquare_pos X θ y hRpos
    rw [batchLogitSafeStep, ite_eq_right (ne_of_gt hRpos)]
    exact (div_pos (by positivity) hRpos).le

theorem batchLogitSafeStep_pos_of_logitRangeSquare_pos
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchLogitRangeSquare X θ y) :
    0 < batchLogitSafeStep X θ y := by
  have hA := batchAlignment_pos_of_logitRangeSquare_pos X θ y hR
  rw [batchLogitSafeStep, ite_eq_right (ne_of_gt hR)]
  exact div_pos (by positivity) hR

/-- Exact minimizer residual for the sharp-range averaged majorizer. -/
theorem batchLogitMajorizer_logitSafeStep_eq
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchLogitRangeSquare X θ y) :
    batchLogitMajorizer X θ y (batchLogitSafeStep X θ y) =
      batchLoss X θ y
        - 2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y := by
  simp only [batchLogitMajorizer, batchLogitSafeStep,
    ite_eq_right (ne_of_gt hR)]
  field_simp
  ring

/-- MAIN (C223, batch mirror of C216): the sharp-range batch safe step
loses at least `2·A²/R'` on the arithmetic-mean batch loss, with
`R' = mean of (sup d − inf d)²` never exceeding `batchRangeSquare`. -/
theorem batchLoss_logitSafeStep_le_residual
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchLogitRangeSquare X θ y) :
    batchLoss X (batchLogitNextParameters X θ y) y ≤
      batchLoss X θ y
        - 2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y := by
  rw [batchLogitNextParameters,
    ← batchLogitMajorizer_logitSafeStep_eq X θ y hR]
  exact batchLoss_alongNext_le_batchLogitMajorizer X θ y
    (batchLogitSafeStep_nonneg X θ y)

theorem batchLoss_logitSafeStep_lt
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchLogitRangeSquare X θ y) :
    batchLoss X (batchLogitNextParameters X θ y) y < batchLoss X θ y := by
  have hA := batchAlignment_pos_of_logitRangeSquare_pos X θ y hR
  have hbound := batchLoss_logitSafeStep_le_residual X θ y hR
  have hpos : 0 < 2 * (batchAlignment X θ y) ^ 2 /
      batchLogitRangeSquare X θ y := by positivity
  linarith

/-! ## Comparison with the existing engine -/

/-- The sharp mean range-square never exceeds the engine's
vocabulary-abs-sum mean range-square. -/
theorem batchLogitRangeSquare_le_batchRangeSquare
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) :
    batchLogitRangeSquare X θ y ≤ batchRangeSquare X θ y := by
  unfold batchLogitRangeSquare batchRangeSquare
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun b _hb =>
      sq_le_sq.mpr (by
        rw [abs_of_nonneg (dirLogitRange_nonneg (X b)
            (batchMeanDirection X θ y)),
          abs_of_nonneg (dirRange_nonneg (X b)
            (batchMeanDirection X θ y))]
        exact dirLogitRange_le_dirRange (X b) (batchMeanDirection X θ y)))
    (Nat.cast_nonneg B)

/-- The sharp-range step is never smaller than the engine's step whenever
the sharp mean range-square is positive. -/
theorem batchLogitSafeStep_ge_batchSafeStep
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hR : 0 < batchLogitRangeSquare X θ y) :
    batchSafeStep X θ y ≤ batchLogitSafeStep X θ y := by
  have hRold : 0 < batchRangeSquare X θ y :=
    lt_of_lt_of_le hR (batchLogitRangeSquare_le_batchRangeSquare X θ y)
  have hA := batchAlignment_pos_of_logitRangeSquare_pos X θ y hR
  rw [batchSafeStep, ite_eq_right (ne_of_gt hRold),
    batchLogitSafeStep, ite_eq_right (ne_of_gt hR)]
  rw [div_le_div_iff₀ hRold hR]
  exact mul_le_mul_of_nonneg_left
    (batchLogitRangeSquare_le_batchRangeSquare X θ y)
    (le_of_lt (mul_pos four_pos hA))

end Hagi.Model.BatchCEDescent
