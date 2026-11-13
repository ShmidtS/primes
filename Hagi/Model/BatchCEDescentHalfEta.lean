import Hagi.Model.CEDescent
import Hagi.Model.CEGroupedScale
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Step.ProjectionDescent
import Hagi.Step.SafeQPStep
import Hagi.Optimization.MirrorHedge
import Hagi.Model.BatchCEDescentFixtures

/-!
# BatchCEDescentHalfEta

Half-margin window family: `batchDirectionHalfEta`, quadratic-margin maximization, and half-next-parameter margin certificates.
-/

set_option relaxedAutoImplicit false

open scoped Matrix
open InnerProductSpace

namespace Hagi.Model.BatchCEDescent

/-- The largest common half-margin window before any unit cap.  Unlike the
older conservative half-window-over-capped-window rule, this totalizes the
exact finite infimum `⨅ b, 4 * eps_b / range_b²`.  Without the full current
derivative certificate it is zero, including at an empty batch. -/
noncomputable def batchDirectionHalfEta {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) : ℝ := by
  classical
  exact if hcert : Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0 then
    ⨅ b, 4 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2
  else 0

/-- The common half-window is positive exactly under the full current
pointwise derivative certificate; finite infimum positivity is explicit. -/
theorem batchDirectionHalfEta_pos_iff {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    0 < batchDirectionHalfEta X θ y D ↔
      Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0 := by
  classical
  constructor
  · intro hpos
    by_contra hcert
    simp [batchDirectionHalfEta, hcert] at hpos
  · intro hcert
    let _ : Nonempty (Fin B) := hcert.1
    rw [batchDirectionHalfEta, dite_eq_left hcert,
      ← Finset.inf'_univ_eq_ciInf]
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).2
    intro b _hb
    exact div_pos (mul_pos (by norm_num)
      (neg_pos.mpr (hcert.2 b))) (sq_pos_of_pos
        (dirRange_pos_of_dirAction_neg (X b) θ (y b) D (hcert.2 b)))

theorem batchDirectionHalfEta_nonneg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    0 ≤ batchDirectionHalfEta X θ y D := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0
  · exact ((batchDirectionHalfEta_pos_iff X θ y D).2 hcert).le
  · simp [batchDirectionHalfEta, hcert]

theorem batchDirectionHalfEta_eq_zero {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d))
    (hcert : ¬ (Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0)) :
    batchDirectionHalfEta X θ y D = 0 := by
  simp [batchDirectionHalfEta, hcert]

/-- The finite common half-window is below each sample's half threshold. -/
theorem batchDirectionHalfEta_le_threshold {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d))
    (hcert : Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0)
    (b : Fin B) :
    batchDirectionHalfEta X θ y D ≤
      4 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2 := by
  let _ : Nonempty (Fin B) := hcert.1
  rw [batchDirectionHalfEta, dite_eq_left hcert]
  exact ciInf_le (Finite.bddBelow_range _) b

theorem exists_batchDirectionHalfEta_eq_threshold
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d))
    (hcert : Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0) :
    ∃ b : Fin B, batchDirectionHalfEta X θ y D =
      4 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2 := by
  classical
  let _ : Nonempty (Fin B) := hcert.1
  rw [batchDirectionHalfEta, dite_eq_left hcert]
  obtain ⟨b, _, hb⟩ := Finset.exists_min_image Finset.univ
    (fun b : Fin B => 4 * (-dirAction (X b) θ (y b) D) /
      (dirRange (X b) D) ^ 2) Finset.univ_nonempty
  refine ⟨b, le_antisymm (ciInf_le (Finite.bddBelow_range _) b) ?_⟩
  exact le_ciInf fun i => hb i (Finset.mem_univ i)

/-- For a positive range, the full quadratic residual increases while both
endpoints stay below its individual threshold `4*a/r²`. -/
theorem quadraticMargin_mono_upto_threshold
    {a r x y : ℝ} (hr : 0 < r)
    (hxy : x ≤ y) (hy : y ≤ 4 * a / r ^ 2) :
    a * x - (x * r) ^ 2 / 8 ≤ a * y - (y * r) ^ 2 / 8 := by
  have hident (t : ℝ) :
      2 * a ^ 2 / r ^ 2 - (a * t - (t * r) ^ 2 / 8) =
        r ^ 2 / 8 * (4 * a / r ^ 2 - t) ^ 2 := by
    field_simp [ne_of_gt hr]
    ring
  have hsquare : (4 * a / r ^ 2 - y) ^ 2 ≤ (4 * a / r ^ 2 - x) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self
      (sub_nonneg.mpr hy) (sub_le_sub_left hxy (4 * a / r ^ 2))
  have hnonneg :
      0 ≤ r ^ 2 / 8 * ((4 * a / r ^ 2 - x) ^ 2 - (4 * a / r ^ 2 - y) ^ 2) :=
    mul_nonneg (div_nonneg (sq_nonneg r) (by norm_num))
      (sub_nonneg.mpr hsquare)
  linarith [hident x, hident y]

/-- Infimum of the per-sample full quadratic residual at a candidate eta. -/
noncomputable def batchDirectionMinQuadraticMargin
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (eta : ℝ)
    [Nonempty (Fin B)] : ℝ :=
  ⨅ b, batchDirectionQuadraticMargin X θ y D eta b

/-- The common certified half-window maximizes the worst-sample full
quadratic residual on the common half-threshold interval. -/
theorem batchDirectionHalfEta_maximizes_minQuadraticMargin
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d))
    (hcert : Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0) :
    IsMaxOn (fun eta =>
        let _ : Nonempty (Fin B) := hcert.1
        batchDirectionMinQuadraticMargin X θ y D eta)
      {eta | 0 ≤ eta ∧ ∀ b, eta ≤
        4 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D)^2}
      (batchDirectionHalfEta X θ y D) := by
  let _ : Nonempty (Fin B) := hcert.1
  rw [isMaxOn_iff]
  intro eta heta
  have heta_le : eta ≤ batchDirectionHalfEta X θ y D := by
    rw [batchDirectionHalfEta, dite_eq_left hcert]
    exact le_ciInf heta.2
  simp only [batchDirectionMinQuadraticMargin]
  apply le_ciInf
  intro b
  calc
    (⨅ b, batchDirectionQuadraticMargin X θ y D eta b) ≤
        batchDirectionQuadraticMargin X θ y D eta b :=
      ciInf_le (Finite.bddBelow_range _) b
    _ ≤ batchDirectionQuadraticMargin X θ y D
        (batchDirectionHalfEta X θ y D) b := by
      have hmono := quadraticMargin_mono_upto_threshold
        (a := -dirAction (X b) θ (y b) D) (r := dirRange (X b) D)
        (x := eta) (y := batchDirectionHalfEta X θ y D)
        (dirRange_pos_of_dirAction_neg (X b) θ (y b) D (hcert.2 b))
        heta_le (batchDirectionHalfEta_le_threshold X θ y D hcert b)
      simpa only [batchDirectionQuadraticMargin, mul_comm] using hmono

/-- Exact quadratic residual at one sample's half-window threshold. -/
theorem batchDirectionQuadraticMargin_at_threshold
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B)
    (hR : 0 < dirRange (X b) D) :
    batchDirectionQuadraticMargin X θ y D
        (4 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2) b =
      2 * (-dirAction (X b) θ (y b) D) ^ 2 / (dirRange (X b) D) ^ 2 := by
  unfold batchDirectionQuadraticMargin
  field_simp [ne_of_gt hR]
  ring

/-- The attained common half-window turns the full quadratic majorizer at its
binding sample into the exact squared-action-over-range-square expression. -/
theorem batchDirectionQuadraticMargin_halfEta_of_eq_threshold
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d))
    (hcert : Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0)
    (b : Fin B)
    (heta : batchDirectionHalfEta X θ y D =
      4 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2) :
    batchDirectionQuadraticMargin X θ y D (batchDirectionHalfEta X θ y D) b =
      2 * (-dirAction (X b) θ (y b) D) ^ 2 / (dirRange (X b) D) ^ 2 := by
  rw [heta]
  exact batchDirectionQuadraticMargin_at_threshold X θ y D b
    (dirRange_pos_of_dirAction_neg (X b) θ (y b) D (hcert.2 b))

/-- The old half-of-capped-window is no larger than the common half-window
computed before the cap.  No corresponding actual-CE ordering is inferred. -/
theorem batchDirectionSafeEta_le_halfEta {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    batchDirectionSafeEta X θ y D ≤ batchDirectionHalfEta X θ y D := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0
  · let _ : Nonempty (Fin B) := hcert.1
    rw [batchDirectionSafeEta_of_neg X θ y D hcert.2,
      batchDirectionHalfEta, dite_eq_left hcert,
      ← Finset.inf'_univ_eq_ciInf]
    apply (Finset.le_inf'_iff Finset.univ_nonempty _).2
    intro b _hb
    have hwindow := batchDirectionSafeWindow_le_threshold X θ y D hcert.2 b
    calc
      batchDirectionSafeWindow X θ y D / 2 ≤
          (8 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2) / 2 :=
        div_le_div_of_nonneg_right hwindow (by norm_num)
      _ = 4 * (-dirAction (X b) θ (y b) D) / (dirRange (X b) D) ^ 2 := by ring
  · rw [batchDirectionSafeEta_eq_zero X θ y D hcert]
    exact batchDirectionHalfEta_nonneg X θ y D

/-- A common arbitrary-direction step at the new explicit half-window. -/
noncomputable def batchDirectionHalfNextParameters {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  alongNext θ D (batchDirectionHalfEta X θ y D)

theorem batchDirectionHalfNextParameters_eq_zero {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d))
    (hcert : ¬ (Nonempty (Fin B) ∧
      ∀ b, dirAction (X b) θ (y b) D < 0)) :
    batchDirectionHalfNextParameters X θ y D = θ := by
  rw [batchDirectionHalfNextParameters,
    batchDirectionHalfEta_eq_zero X θ y D hcert, alongNext_zero]

/-- Common half-linear margin at the newly computed half-window. -/
noncomputable def batchDirectionHalfMargin {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) : ℝ :=
  batchDirectionHalfEta X θ y D * (-dirAction (X b) θ (y b) D) / 2

theorem batchDirectionHalfMargin_nonneg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) :
    0 ≤ batchDirectionHalfMargin X θ y D b := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0
  · exact div_nonneg (mul_nonneg (batchDirectionHalfEta_nonneg X θ y D)
      (neg_nonneg.mpr (hcert.2 b).le)) (by norm_num)
  · simp [batchDirectionHalfMargin, batchDirectionHalfEta_eq_zero X θ y D hcert]

/-- The new full quadratic residual is at least its nonnegative half-linear
margin, with no separate certificate premise in the theorem statement. -/
theorem batchDirectionHalfMargin_le_quadraticMargin
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) :
    batchDirectionHalfMargin X θ y D b ≤
      batchDirectionQuadraticMargin X θ y D (batchDirectionHalfEta X θ y D) b := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0
  · exact halfAction_le_quadraticMargin_of_le_threshold X θ y D
      (batchDirectionHalfEta X θ y D) b (batchDirectionHalfEta_nonneg X θ y D)
      (dirRange_pos_of_dirAction_neg (X b) θ (y b) D (hcert.2 b))
      (batchDirectionHalfEta_le_threshold X θ y D hcert b)
  · simp [batchDirectionHalfMargin, batchDirectionQuadraticMargin,
      batchDirectionHalfEta_eq_zero X θ y D hcert]

/-- The new half-window's linear margin strictly improves the supplied
sample under the same complete derivative certificate. -/
theorem batchDirectionHalfMargin_pos_of_neg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) (b : Fin B) :
    0 < batchDirectionHalfMargin X θ y D b := by
  exact div_pos (mul_pos ((batchDirectionHalfEta_pos_iff X θ y D).2
      ⟨inferInstance, hneg⟩) (neg_pos.mpr (hneg b))) (by norm_num)

/-- The prior conservative linear margin is at most the new margin. -/
theorem batchDirectionMargin_le_halfMargin {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) :
    batchDirectionMargin X θ y D b ≤ batchDirectionHalfMargin X θ y D b := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (batchDirectionSafeEta_le_halfEta X θ y D)
        (neg_nonneg.mpr (hcert.2 b).le)) (by norm_num)
  · simp [batchDirectionMargin, batchDirectionHalfMargin,
      batchDirectionSafeEta_eq_zero X θ y D hcert,
      batchDirectionHalfEta_eq_zero X θ y D hcert]

/-- Actual one-sample CE at the new half-window is bounded by the real
full quadratic residual, not merely by the old conservative half margin. -/
theorem ceOneHot_batchDirectionHalfNextParameters_le_quadraticMargin
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) :
    Hagi.ceOneHot (y b) (ceLogits (X b)
      (batchDirectionHalfNextParameters X θ y D)) ≤
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) -
        batchDirectionQuadraticMargin X θ y D (batchDirectionHalfEta X θ y D) b := by
  by_cases hcert : Nonempty (Fin B) ∧ ∀ b, dirAction (X b) θ (y b) D < 0
  · let _ : Nonempty (Fin B) := hcert.1
    let _ : Nonempty V := ⟨y b⟩
    have heta := batchDirectionHalfEta_nonneg X θ y D
    have hbase := ceOneHot_alongNext_le (X b) θ D (y b) heta
    rw [← batchDirectionHalfNextParameters] at hbase
    unfold batchDirectionQuadraticMargin
    linarith
  · rw [batchDirectionHalfNextParameters_eq_zero X θ y D hcert]
    simp [batchDirectionQuadraticMargin, batchDirectionHalfEta_eq_zero X θ y D hcert]

/-- The weaker half-linear bound at the new step holds in all branches. -/
theorem ceOneHot_batchDirectionHalfNextParameters_le_halfMargin
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) :
    Hagi.ceOneHot (y b) (ceLogits (X b)
      (batchDirectionHalfNextParameters X θ y D)) ≤
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) -
        batchDirectionHalfMargin X θ y D b := by
  have hfull := ceOneHot_batchDirectionHalfNextParameters_le_quadraticMargin
    X θ y D b
  have hmargin := batchDirectionHalfMargin_le_quadraticMargin X θ y D b
  linarith

/-- The actual new sample update retains at least the old conservative
margin guarantee.  This is not a comparison with the old actual next CE. -/
theorem ceOneHot_batchDirectionHalfNextParameters_le_margin
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) (b : Fin B) :
    Hagi.ceOneHot (y b) (ceLogits (X b)
      (batchDirectionHalfNextParameters X θ y D)) ≤
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) -
        batchDirectionMargin X θ y D b := by
  have hfull := ceOneHot_batchDirectionHalfNextParameters_le_halfMargin X θ y D b
  have hmargin := batchDirectionMargin_le_halfMargin X θ y D b
  linarith

/-- Complete negative derivative certification makes the actual update at
the new half-window strictly subunitary in every real sample. -/
theorem ceOneHot_batchDirectionHalfNextParameters_lt
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) [Nonempty (Fin B)]
    (hneg : ∀ b, dirAction (X b) θ (y b) D < 0) (b : Fin B) :
    Hagi.ceOneHot (y b) (ceLogits (X b)
      (batchDirectionHalfNextParameters X θ y D)) <
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) := by
  have hbound := ceOneHot_batchDirectionHalfNextParameters_le_halfMargin X θ y D b
  have hmargin := batchDirectionHalfMargin_pos_of_neg X θ y D hneg b
  linarith

/-- The arithmetic-mean residual at the new step uses the actual full
quadratic margins and exactly one batch denominator, including B = 0. -/
theorem batchLoss_batchDirectionHalfNextParameters_le_quadraticMargin_sum
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    batchLoss X (batchDirectionHalfNextParameters X θ y D) y ≤
      batchLoss X θ y -
        (∑ b, batchDirectionQuadraticMargin X θ y D
          (batchDirectionHalfEta X θ y D) b) / (B : ℝ) := by
  have hsum : (∑ b, Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchDirectionHalfNextParameters X θ y D))) ≤
      ∑ b, (Hagi.ceOneHot (y b) (ceLogits (X b) θ) -
        batchDirectionQuadraticMargin X θ y D
          (batchDirectionHalfEta X θ y D) b) :=
    Finset.sum_le_sum (fun b _hb =>
      ceOneHot_batchDirectionHalfNextParameters_le_quadraticMargin X θ y D b)
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
  unfold batchLoss Hagi.Probability.FiniteFamilyConfidence.empiricalMean
  calc
    (∑ b, Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchDirectionHalfNextParameters X θ y D))) / (B : ℝ) ≤
      (∑ b, (Hagi.ceOneHot (y b) (ceLogits (X b) θ) -
        batchDirectionQuadraticMargin X θ y D
          (batchDirectionHalfEta X θ y D) b)) / (B : ℝ) := hdiv
    _ = (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)) / (B : ℝ) -
        (∑ b, batchDirectionQuadraticMargin X θ y D
          (batchDirectionHalfEta X θ y D) b) / (B : ℝ) := by
      rw [Finset.sum_sub_distrib, sub_div]

/-- The same updated mean loss remains below the old average linear margin. -/
theorem batchLoss_batchDirectionHalfNextParameters_le_margin_sum
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) :
    batchLoss X (batchDirectionHalfNextParameters X θ y D) y ≤
      batchLoss X θ y - (∑ b, batchDirectionMargin X θ y D b) / (B : ℝ) := by
  have hsum : (∑ b, batchDirectionMargin X θ y D b) ≤
      ∑ b, batchDirectionQuadraticMargin X θ y D
        (batchDirectionHalfEta X θ y D) b :=
    Finset.sum_le_sum (fun b _hb =>
      (batchDirectionHalfMargin_le_quadraticMargin X θ y D b).trans'
        (batchDirectionMargin_le_halfMargin X θ y D b))
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
  have hbound := batchLoss_batchDirectionHalfNextParameters_le_quadraticMargin_sum
    X θ y D
  linarith


end Hagi.Model.BatchCEDescent
