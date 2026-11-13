import Hagi.Model.CEDescent
import Hagi.Model.CEGroupedScale
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Step.ProjectionDescent
import Hagi.Step.SafeQPStep
import Hagi.Optimization.MirrorHedge
import Hagi.Model.BatchCEDescentArithmetic

/-!
# BatchCEDescentDirection

Arbitrary-direction safe-step family: `batchDirectionSafeWindow`/`SafeEta`/`NextParameters`, margins, and comparison with the common minimizer window.
-/

set_option relaxedAutoImplicit false

open scoped Matrix
open InnerProductSpace

namespace Hagi.Model.BatchCEDescent

/-- A negative directional action forces a positive exact CE logit range. -/
theorem dirRange_pos_of_dirAction_neg {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (D : EuclideanSpace ℝ (Fin d)) (hA : dirAction X θ t D < 0) :
    0 < dirRange X D := by
  by_contra hpos
  have hR : dirRange X D = 0 :=
    le_antisymm (le_of_not_gt hpos) (dirRange_nonneg _ _)
  have hzero := (dirRange_eq_zero_iff X D).mp hR
  have hA0 : dirAction X θ t D = 0 := by
    simp [dirAction, hzero]
  linarith

/-- A certified negative action at every sample also rules out the zero
parameter direction, without any convex-hull or minimizer hypothesis. -/
theorem batchDirection_ne_zero_of_forall_dirAction_neg
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) : D ≠ 0 := by
  let b0 : Fin B := Classical.choice (inferInstance : Nonempty (Fin B))
  intro hD
  have hA := hneg b0
  rw [dirAction_eq_inner, hD, inner_zero_right] at hA
  exact (lt_irrefl 0) hA

/-- The conflict-free window for an arbitrary direction, using each exact
negative CE directional action as its margin.  The curvature denominator is
`‖D‖²`, so the generic SafeQP normalization has the exact CE threshold. -/
noncomputable def batchDirectionSafeWindow {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)] : ℝ :=
  Hagi.Step.safeqpEtaMaxConflictFree
    (fun b => -dirAction (X b) θ (y b) D)
    (fun b => (dirRange (X b) D) ^ 2 / (4 * ‖D‖ ^ 2))
    D

/-- The arbitrary-direction window is positive under the pointwise negative
CE derivative certificate. -/
theorem batchDirectionSafeWindow_pos {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) :
    0 < batchDirectionSafeWindow X θ y D := by
  have hD := batchDirection_ne_zero_of_forall_dirAction_neg X θ y D hneg
  unfold batchDirectionSafeWindow
  apply Hagi.Step.safeqpEtaMaxConflictFree_pos
  · intro b
    exact div_pos (sq_pos_of_pos (dirRange_pos_of_dirAction_neg
      (X b) θ (y b) D (hneg b)))
      (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hD)))
  · intro b
    exact neg_pos.mpr (hneg b)
  · exact hD

/-- Each raw SafeQP threshold is exactly the arbitrary-direction CE
majorizer threshold; the two norm-square factors cancel. -/
theorem batchDirectionSafeWindow_le_threshold {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) (b : Fin B) :
    batchDirectionSafeWindow X θ y D ≤
      8 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2 := by
  have hraw := ((Hagi.Step.le_safeqpEtaMaxConflictFree_iff
    (fun b => -dirAction (X b) θ (y b) D)
    (fun b => (dirRange (X b) D) ^ 2 / (4 * ‖D‖ ^ 2)) D).mp
      (le_refl (batchDirectionSafeWindow X θ y D))).2 b
  have hD := batchDirection_ne_zero_of_forall_dirAction_neg X θ y D hneg
  have hN : ‖D‖ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hD))
  have hR : (dirRange (X b) D) ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos
      (dirRange_pos_of_dirAction_neg (X b) θ (y b) D (hneg b)))
  unfold batchDirectionSafeWindow
  calc
    Hagi.Step.safeqpEtaMaxConflictFree
        (fun b => -dirAction (X b) θ (y b) D)
        (fun b => (dirRange (X b) D) ^ 2 / (4 * ‖D‖ ^ 2)) D ≤
      2 * (-dirAction (X b) θ (y b) D) /
        ((dirRange (X b) D) ^ 2 / (4 * ‖D‖ ^ 2) * ‖D‖ ^ 2) := hraw
    _ = 8 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2 := by
      field_simp [hN, hR]
      ring

/-- Half the certified arbitrary-direction window.  The totalized value is
zero unless the batch is nonempty and every CE directional derivative is
strictly negative. -/
noncomputable def batchDirectionSafeEta {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) : ℝ := by
  classical
  exact if hcert : Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0 then
    letI := hcert.1
    batchDirectionSafeWindow X θ y D / 2
  else 0

/-- On the certified branch, the selected step is exactly half the window. -/
theorem batchDirectionSafeEta_of_neg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) :
    batchDirectionSafeEta X θ y D = batchDirectionSafeWindow X θ y D / 2 := by
  classical
  have hcert : Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0 := ⟨inferInstance, hneg⟩
  rw [batchDirectionSafeEta, dite_eq_left hcert]

/-- Positivity of the totalized step is exactly the full certificate.  In
particular, an empty batch cannot make the universal condition vacuously
produce a positive step. -/
theorem batchDirectionSafeEta_pos_iff {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    0 < batchDirectionSafeEta X θ y D ↔
      Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0 := by
  classical
  constructor
  · intro heta
    by_contra hcert
    have hzero : batchDirectionSafeEta X θ y D = 0 := by
      simp [batchDirectionSafeEta, hcert]
    linarith
  · intro hcert
    let _ : Nonempty (Fin B) := hcert.1
    rw [batchDirectionSafeEta_of_neg X θ y D hcert.2]
    exact half_pos (batchDirectionSafeWindow_pos X θ y D hcert.2)

/-- Failure of either conjunct selects the exact zero step. -/
theorem batchDirectionSafeEta_eq_zero {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d))
    (hcert : ¬ (Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0)) :
    batchDirectionSafeEta X θ y D = 0 := by
  classical
  simp [batchDirectionSafeEta, hcert]

theorem batchDirectionSafeEta_nonneg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    0 ≤ batchDirectionSafeEta X θ y D := by
  by_cases hcert : Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0
  · exact ((batchDirectionSafeEta_pos_iff X θ y D).2 hcert).le
  · rw [batchDirectionSafeEta_eq_zero X θ y D hcert]

@[simp] theorem batchDirectionSafeEta_empty {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 0 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 0 → V) (D : EuclideanSpace ℝ (Fin d)) :
    batchDirectionSafeEta X θ y D = 0 := by
  simp [batchDirectionSafeEta]

/-- Half the finite window is strictly below every sample's exact CE
quadratic-descent threshold. -/
theorem batchDirectionSafeEta_lt_threshold {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) (b : Fin B) :
    batchDirectionSafeEta X θ y D <
      8 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2 := by
  rw [batchDirectionSafeEta_of_neg X θ y D hneg]
  have hwindow := batchDirectionSafeWindow_pos X θ y D hneg
  have hle := batchDirectionSafeWindow_le_threshold X θ y D hneg b
  have hR : 0 < (dirRange (X b) D) ^ 2 :=
    sq_pos_of_pos (dirRange_pos_of_dirAction_neg (X b) θ (y b) D (hneg b))
  have hthreshold : 0 < 8 * (-dirAction (X b) θ (y b) D) /
      (dirRange (X b) D) ^ 2 :=
    div_pos (mul_pos (by norm_num) (neg_pos.mpr (hneg b))) hR
  linarith

/-- Parameter update along an arbitrary direction at its totalized certified
step. -/
noncomputable def batchDirectionNextParameters {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  alongNext θ D (batchDirectionSafeEta X θ y D)

/-- Without the complete certificate the direction update preserves the
actual model parameters; this says nothing about other training-state fields. -/
theorem batchDirectionNextParameters_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d))
    (hcert : ¬ (Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0)) :
    batchDirectionNextParameters X θ y D = θ := by
  rw [batchDirectionNextParameters,
    batchDirectionSafeEta_eq_zero X θ y D hcert, alongNext_zero]

@[simp] theorem batchDirectionNextParameters_empty
    {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 0 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 0 → V) (D : EuclideanSpace ℝ (Fin d)) :
    batchDirectionNextParameters X θ y D = θ := by
  rw [batchDirectionNextParameters, batchDirectionSafeEta_empty, alongNext_zero]

/-- Exact full quadratic residual in an arbitrary supplied eta.  It is a
majorizer residual, not the exact actual CE difference. -/
noncomputable def batchDirectionQuadraticMargin {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (eta : ℝ) (b : Fin B) : ℝ :=
  eta * (-dirAction (X b) θ (y b) D) - (eta * dirRange (X b) D) ^ 2 / 8

/-- At any eta inside a sample's half threshold, its half-linear margin is
no larger than the full quadratic residual.  Positive range is supplied by
the real negative derivative certificate at the call site. -/
theorem halfAction_le_quadraticMargin_of_le_threshold
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (eta : ℝ) (b : Fin B)
    (heta : 0 ≤ eta) (hR : 0 < dirRange (X b) D)
    (hbound : eta ≤ 4 * (-dirAction (X b) θ (y b) D) /
      (dirRange (X b) D) ^ 2) :
    eta * (-dirAction (X b) θ (y b) D) / 2 ≤
      batchDirectionQuadraticMargin X θ y D eta b := by
  have hscaled : eta * (dirRange (X b) D) ^ 2 ≤
      4 * (-dirAction (X b) θ (y b) D) :=
    (le_div_iff₀ (sq_pos_of_pos hR)).mp hbound
  have hmul := mul_le_mul_of_nonneg_left hscaled heta
  unfold batchDirectionQuadraticMargin
  nlinarith

/-- The exact local per-sample CE margin supplied by the half-window step.
This is a mathematical lower bound on the guaranteed drop, not a physical
cost, an empirical rate, or a trajectory-wide discount. -/
noncomputable def batchDirectionMargin {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) : ℝ :=
  batchDirectionSafeEta X θ y D * (-dirAction (X b) θ (y b) D) / 2

/-- The local margin is nonnegative even without a complete certificate:
the totalized step is zero on that branch. -/
theorem batchDirectionMargin_nonneg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) :
    0 ≤ batchDirectionMargin X θ y D b := by
  by_cases hcert : Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0
  · exact div_nonneg
      (mul_nonneg (batchDirectionSafeEta_nonneg X θ y D)
        (neg_nonneg.mpr (hcert.2 b).le)) (by norm_num)
  · simp [batchDirectionMargin, batchDirectionSafeEta_eq_zero X θ y D hcert]

/-- The full negative-derivative certificate makes each local margin
strictly positive. -/
theorem batchDirectionMargin_pos_of_neg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) (b : Fin B) :
    0 < batchDirectionMargin X θ y D b := by
  have heta := (batchDirectionSafeEta_pos_iff X θ y D).2 ⟨inferInstance, hneg⟩
  exact div_pos (mul_pos heta (neg_pos.mpr (hneg b))) (by norm_num)

/-- Every arbitrary-direction update decreases each sample's actual CE by at
least its exact local margin.  Without the full certificate both the step and
the margin vanish, so no conditional premise is needed in the statement. -/
theorem ceOneHot_batchDirectionNextParameters_le_margin
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) :
    Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchDirectionNextParameters X θ y D)) ≤
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) -
        batchDirectionMargin X θ y D b := by
  by_cases hcert : Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0
  · let _ : Nonempty (Fin B) := hcert.1
    let _ : Nonempty V := ⟨y b⟩
    have heta := batchDirectionSafeEta_nonneg X θ y D
    have hR := dirRange_pos_of_dirAction_neg (X b) θ (y b) D (hcert.2 b)
    have hwindow := batchDirectionSafeWindow_le_threshold X θ y D hcert.2 b
    have heta_le : batchDirectionSafeEta X θ y D ≤
        4 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2 := by
      rw [batchDirectionSafeEta_of_neg X θ y D hcert.2]
      calc
        batchDirectionSafeWindow X θ y D / 2 ≤
            (8 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2) / 2 :=
          div_le_div_of_nonneg_right hwindow (by norm_num)
        _ = 4 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2 := by ring
    have hmargin := halfAction_le_quadraticMargin_of_le_threshold
      X θ y D (batchDirectionSafeEta X θ y D) b heta hR heta_le
    have hbase := ceOneHot_alongNext_le (X b) θ D (y b) heta
    rw [← batchDirectionNextParameters] at hbase
    unfold batchDirectionQuadraticMargin at hmargin
    unfold batchDirectionMargin
    linarith
  · rw [batchDirectionNextParameters_eq_zero X θ y D hcert]
    simp [batchDirectionMargin, batchDirectionSafeEta_eq_zero X θ y D hcert]

/-- The arithmetic-mean loss decreases by at least the arithmetic mean of the
same exact local margins.  Lean's zero-denominator convention handles the
empty batch without introducing a nonzero-batch premise. -/
theorem batchLoss_batchDirectionNextParameters_le_margin_sum
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    batchLoss X (batchDirectionNextParameters X θ y D) y ≤
      batchLoss X θ y - (∑ b, batchDirectionMargin X θ y D b) / (B : ℝ) := by
  have hsum : (∑ b, Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchDirectionNextParameters X θ y D))) ≤
      ∑ b, (Hagi.ceOneHot (y b) (ceLogits (X b) θ) -
        batchDirectionMargin X θ y D b) :=
    Finset.sum_le_sum (fun b _hb =>
      ceOneHot_batchDirectionNextParameters_le_margin X θ y D b)
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
  unfold batchLoss Hagi.Probability.FiniteFamilyConfidence.empiricalMean
  calc
    (∑ b, Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchDirectionNextParameters X θ y D))) / (B : ℝ) ≤
      (∑ b, (Hagi.ceOneHot (y b) (ceLogits (X b) θ) -
        batchDirectionMargin X θ y D b)) / (B : ℝ) := hdiv
    _ = (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)) / (B : ℝ) -
        (∑ b, batchDirectionMargin X θ y D b) / (B : ℝ) := by
      rw [Finset.sum_sub_distrib, sub_div]

/-- The exact half-window produces strict actual CE descent on every sample
under only the negative directional-derivative certificate. -/
theorem ceOneHot_batchDirectionNextParameters_lt
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) (b : Fin B) :
    Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchDirectionNextParameters X θ y D)) <
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) := by
  have hbound := ceOneHot_batchDirectionNextParameters_le_margin X θ y D b
  have hmargin := batchDirectionMargin_pos_of_neg X θ y D hneg b
  linarith

/-- Every sample is nonincreasing, including the exact zero-step branch when
any sample lacks a negative directional derivative. -/
theorem ceOneHot_batchDirectionNextParameters_le
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) :
    Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchDirectionNextParameters X θ y D)) ≤
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) := by
  by_cases hcert : Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0
  · let _ : Nonempty (Fin B) := hcert.1
    exact (ceOneHot_batchDirectionNextParameters_lt X θ y D hcert.2 b).le
  · rw [batchDirectionNextParameters_eq_zero X θ y D hcert]

@[simp] theorem ceOneHot_batchDirectionNextParameters_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d))
    (hcert : ¬ (Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0)) (b : Fin B) :
    Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchDirectionNextParameters X θ y D)) =
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) := by
  rw [batchDirectionNextParameters_eq_zero X θ y D hcert]

@[simp] theorem batchLoss_batchDirectionNextParameters_empty
    {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 0 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 0 → V) (D : EuclideanSpace ℝ (Fin d)) :
    batchLoss X (batchDirectionNextParameters X θ y D) y = batchLoss X θ y := by
  rw [batchDirectionNextParameters_empty]

/-- Strict component descent and the inhabited finite denominator give
strict arithmetic-mean CE descent on the supplied batch. -/
theorem batchLoss_batchDirectionNextParameters_lt
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) :
    batchLoss X (batchDirectionNextParameters X θ y D) y < batchLoss X θ y := by
  obtain ⟨b0⟩ := (inferInstance : Nonempty (Fin B))
  have hB : 0 < B := by
    by_contra h
    have hB0 : B = 0 := Nat.eq_zero_of_not_pos h
    subst B
    exact Fin.elim0 b0
  have hsum : 0 < ∑ b, batchDirectionMargin X θ y D b :=
    Finset.sum_pos (fun b _hb => batchDirectionMargin_pos_of_neg X θ y D hneg b)
      Finset.univ_nonempty
  have hmean : 0 < (∑ b, batchDirectionMargin X θ y D b) / (B : ℝ) :=
    div_pos hsum (Nat.cast_pos.mpr hB)
  have hbound := batchLoss_batchDirectionNextParameters_le_margin_sum X θ y D
  linarith

/-- At a nonzero exact minimum-norm raw gradient, KKT makes every actual
CE directional derivative along `-ω` strictly negative. -/
theorem dirAction_neg_batchGradientMinimizer_lt
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y ≠ 0) (b : Fin B) :
    dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y) < 0 := by
  have hA := dirAction_neg_batchGradientMinimizer_le X θ y b
  have hN : 0 < ‖batchGradientMinimizer X θ y‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hω)
  linarith

/-- The old exact minimizer supplies the complete arbitrary-direction
certificate, including genuine batch nonemptiness. -/
theorem neg_batchGradientMinimizer_descent_certificate
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y ≠ 0) :
    Nonempty (Fin B) ∧ ∀ b,
      dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y) < 0 :=
  ⟨nonempty_fin_batch_of_minimizer_ne_zero X θ y hω,
    dirAction_neg_batchGradientMinimizer_lt X θ y hω⟩

/-- The conservative old window is no larger than the certificate-aware
window along `-ω`; their curvature families coincide after `norm_neg`. -/
theorem batchCommonSafeWindow_le_batchDirectionSafeWindow_neg_minimizer
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [Nonempty (Fin B)]
    (hω : batchGradientMinimizer X θ y ≠ 0) :
    batchCommonSafeWindow X θ y ≤
      batchDirectionSafeWindow X θ y (-batchGradientMinimizer X θ y) := by
  have hNpos : 0 < ‖batchGradientMinimizer X θ y‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hω)
  have hN : ‖batchGradientMinimizer X θ y‖ ^ 2 ≠ 0 := ne_of_gt hNpos
  have hone : batchCommonSafeWindow X θ y ≤ 1 := by
    unfold batchCommonSafeWindow Hagi.Step.safeqpEtaMaxConflictFree
    exact min_le_left _ _
  unfold batchDirectionSafeWindow
  apply (Hagi.Step.le_safeqpEtaMaxConflictFree_iff _ _ _).2
  refine ⟨hone, ?_⟩
  intro b
  have hold := ((Hagi.Step.le_safeqpEtaMaxConflictFree_iff
    (fun _ : Fin B => ‖batchGradientMinimizer X θ y‖ ^ 2)
    (fun b => (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 /
      (4 * ‖batchGradientMinimizer X θ y‖ ^ 2))
    (batchGradientMinimizer X θ y)).mp
      (le_refl (batchCommonSafeWindow X θ y))).2 b
  have heps : ‖batchGradientMinimizer X θ y‖ ^ 2 ≤
      -dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y) := by
    have hA := dirAction_neg_batchGradientMinimizer_le X θ y b
    linarith
  have hR : (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos
      (dirRange_neg_batchGradientMinimizer_pos X θ y hω b))
  calc
    batchCommonSafeWindow X θ y ≤
      2 * ‖batchGradientMinimizer X θ y‖ ^ 2 /
        ((dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 /
          (4 * ‖batchGradientMinimizer X θ y‖ ^ 2) *
            ‖batchGradientMinimizer X θ y‖ ^ 2) := hold
    _ = 8 * ‖batchGradientMinimizer X θ y‖ ^ 2 /
        (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 := by
      field_simp [hN, hR]
      ring
    _ ≤ 8 * (-dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y)) /
        (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left heps (by norm_num)) (sq_nonneg _)
    _ = 2 * (-dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y)) /
        ((dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 /
          (4 * ‖-batchGradientMinimizer X θ y‖ ^ 2) *
            ‖-batchGradientMinimizer X θ y‖ ^ 2) := by
      rw [norm_neg]
      field_simp [hN, hR]
      ring

/-- The old selected step is conservatively no larger than the new step for
every old totalized minimizer.  This is an inequality, not eta equality or
a comparison of their actual CE values. -/
theorem batchCommonSafeEta_le_batchDirectionSafeEta_neg_minimizer
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) :
    batchCommonSafeEta X θ y ≤
      batchDirectionSafeEta X θ y (-batchGradientMinimizer X θ y) := by
  classical
  by_cases hω : batchGradientMinimizer X θ y = 0
  · rw [batchCommonSafeEta_of_minimizer_eq_zero X θ y hω]
    exact batchDirectionSafeEta_nonneg X θ y _
  · let _ : Nonempty (Fin B) := nonempty_fin_batch_of_minimizer_ne_zero X θ y hω
    have hneg := dirAction_neg_batchGradientMinimizer_lt X θ y hω
    rw [batchCommonSafeEta, dite_eq_left (inferInstance : Nonempty (Fin B)),
      dite_eq_right hω, batchDirectionSafeEta_of_neg X θ y _ hneg]
    exact div_le_div_of_nonneg_right
      (batchCommonSafeWindow_le_batchDirectionSafeWindow_neg_minimizer
        X θ y hω) (by norm_num)


end Hagi.Model.BatchCEDescent
