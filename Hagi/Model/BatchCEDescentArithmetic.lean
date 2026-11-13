import Hagi.Model.CEDescent
import Hagi.Model.CEGroupedScale
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Step.ProjectionDescent
import Hagi.Step.SafeQPStep
import Hagi.Optimization.MirrorHedge
import Hagi.Model.BatchCEDescentCommon

/-!
# BatchCEDescentArithmetic

Arithmetic-batch mean-direction family: `batchMeanDirection`, `batchAlignment`, `batchCommonSafeWindow`/`SafeEta`/`NextParameters`, and strict descent of the mean batch loss.
-/

set_option relaxedAutoImplicit false

open scoped Matrix
open InnerProductSpace

namespace Hagi.Model.BatchCEDescent

/-! ## Arithmetic batch: one common averaged direction -/

/-- Raw arithmetic mean CE on the supplied samples.  The empty-batch value is
Lean's `0 / 0 = 0` algebra convention, not a statistical estimate. -/
noncomputable def batchLoss {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : ℝ :=
  Hagi.Probability.FiniteFamilyConfidence.empiricalMean
    (fun b t => Hagi.ceOneHot t (ceLogits (X b) θ)) y

/-- Coordinatewise arithmetic mean of the exact residual transposes. -/
noncomputable def meanResidualTranspose {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : Fin d → ℝ :=
  fun j => (∑ b, residualTranspose (X b) θ (y b) j) / (B : ℝ)

/-- Arithmetic mean of the individual negative-residual directions.  This is
the one common direction used in every individual majorizer below. -/
noncomputable def batchMeanDirection {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j =>
    (∑ b, (ceDirection (X b) θ (y b)).ofLp j) / (B : ℝ))

/-- Alignment is based on the mean residual transpose, never on a mean of
individual alignments. -/
noncomputable def batchAlignment {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : ℝ :=
  ∑ j, (meanResidualTranspose X θ y j) ^ 2

/-- Arithmetic mean of the squared ranges of the *same* common direction. -/
noncomputable def batchRangeSquare {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : ℝ :=
  (∑ b, (dirRange (X b) (batchMeanDirection X θ y)) ^ 2) / (B : ℝ)

/-- Mean directional action, before specializing to the common direction. -/
noncomputable def batchMeanAction {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (D : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (∑ b, dirAction (X b) θ (y b) D) / (B : ℝ)

@[simp] theorem batchMeanDirection_ofLp {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (j : Fin d) :
    (batchMeanDirection X θ y).ofLp j =
      (∑ b, (ceDirection (X b) θ (y b)).ofLp j) / (B : ℝ) := rfl

/-- The mean of the own negative directions is minus the mean residual
transpose; this is a coordinate equality, not an alignment assertion. -/
theorem batchMeanDirection_eq_neg_meanResidualTranspose
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) :
    batchMeanDirection X θ y =
      WithLp.toLp 2 (fun j => -meanResidualTranspose X θ y j) := by
  apply PiLp.ext
  intro j
  rw [batchMeanDirection_ofLp]
  simp only [ceDirection_ofLp, meanResidualTranspose]
  rw [Finset.sum_neg_distrib]
  ring

/-! ## Raw-gradient minimum-norm common direction -/

/-- The raw residual-transpose gradient of one sample on the Euclidean
carrier.  Its negative is the existing `ceDirection`. -/
noncomputable def batchResidualGradient {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (residualTranspose X θ t)

@[simp] theorem batchResidualGradient_ofLp {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (j : Fin d) :
    (batchResidualGradient X θ t).ofLp j = residualTranspose X θ t j := rfl

/-- On a nonempty finite batch, compactness of the convex hull supplies a
minimum-norm raw-gradient convex combination. -/
theorem exists_batchGradientMinimizer {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [Nonempty (Fin B)] :
    ∃ ω ∈ convexHull ℝ (Set.range fun b => batchResidualGradient (X b) θ (y b)),
      ∀ c ∈ convexHull ℝ (Set.range fun b => batchResidualGradient (X b) θ (y b)),
        ‖ω‖ ≤ ‖c‖ := by
  let C := convexHull ℝ (Set.range fun b => batchResidualGradient (X b) θ (y b))
  have hCcompact : IsCompact C :=
    (Set.finite_range _).isCompact_convexHull ℝ
  have hCnonempty : C.Nonempty :=
    (Set.range_nonempty _).mono
      (subset_convexHull ℝ (Set.range fun b => batchResidualGradient (X b) θ (y b)))
  obtain ⟨ω, hω, hmin⟩ := hCcompact.exists_isMinOn hCnonempty
    continuous_norm.continuousOn
  exact ⟨ω, hω, fun c hc => hmin hc⟩

/-- Totalized classical minimum-norm point of the raw-gradient convex hull.
At an empty batch there is no simplex choice and the value is zero. -/
noncomputable def batchGradientMinimizer {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : EuclideanSpace ℝ (Fin d) := by
  classical
  exact if hB : Nonempty (Fin B) then
    letI := hB
    Classical.choose (exists_batchGradientMinimizer X θ y)
  else 0

theorem batchGradientMinimizer_spec {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [hB : Nonempty (Fin B)] :
    batchGradientMinimizer X θ y ∈
        convexHull ℝ (Set.range fun b => batchResidualGradient (X b) θ (y b)) ∧
      ∀ c ∈ convexHull ℝ (Set.range fun b => batchResidualGradient (X b) θ (y b)),
        ‖batchGradientMinimizer X θ y‖ ≤ ‖c‖ := by
  classical
  rw [batchGradientMinimizer, dite_eq_left hB]
  exact Classical.choose_spec (exists_batchGradientMinimizer X θ y)

theorem batchGradientMinimizer_mem {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [Nonempty (Fin B)] :
    batchGradientMinimizer X θ y ∈
      convexHull ℝ (Set.range fun b => batchResidualGradient (X b) θ (y b)) :=
  (batchGradientMinimizer_spec X θ y).1

theorem batchGradientMinimizer_norm_le {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [Nonempty (Fin B)]
    {c : EuclideanSpace ℝ (Fin d)}
    (hc : c ∈ convexHull ℝ
      (Set.range fun b => batchResidualGradient (X b) θ (y b))) :
    ‖batchGradientMinimizer X θ y‖ ≤ ‖c‖ :=
  (batchGradientMinimizer_spec X θ y).2 c hc

@[simp] theorem batchGradientMinimizer_empty {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 0 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 0 → V) : batchGradientMinimizer X θ y = 0 := by
  simp [batchGradientMinimizer]

/-- The actual arithmetic-mean raw gradient is a uniform convex combination
of the sample gradients. -/
theorem meanResidualTranspose_mem_convexHull {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [Nonempty (Fin B)] :
    WithLp.toLp 2 (meanResidualTranspose X θ y) ∈
      convexHull ℝ (Set.range fun b => batchResidualGradient (X b) θ (y b)) := by
  classical
  let b0 : Fin B := Classical.choice (inferInstance : Nonempty (Fin B))
  have hB : (B : ℝ) ≠ 0 := by
    intro h
    have hB0 : B = 0 := Nat.cast_eq_zero.mp h
    subst B
    exact Fin.elim0 b0
  have hmean :
      (∑ b, (B : ℝ)⁻¹ • batchResidualGradient (X b) θ (y b)) =
        WithLp.toLp 2 (meanResidualTranspose X θ y) := by
    apply PiLp.ext
    intro j
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul, batchResidualGradient_ofLp, meanResidualTranspose]
    rw [← Finset.mul_sum, div_eq_inv_mul]
  rw [← hmean]
  apply (convex_convexHull ℝ _).sum_mem
  · intro b _hb
    exact inv_nonneg.mpr (Nat.cast_nonneg B)
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hB
  · intro b _hb
    exact subset_convexHull ℝ _ ⟨b, rfl⟩

theorem batchGradientMinimizer_norm_le_mean {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [Nonempty (Fin B)] :
    ‖batchGradientMinimizer X θ y‖ ≤
      ‖WithLp.toLp 2 (meanResidualTranspose X θ y)‖ :=
  batchGradientMinimizer_norm_le X θ y (meanResidualTranspose_mem_convexHull X θ y)

/-- The feasible mean raw residual dominates the minimum-norm hull point's
squared Euclidean norm. Empty batches are handled by the same totalized mean. -/
theorem batchGradientMinimizer_norm_sq_le_batchAlignment
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) :
    ‖batchGradientMinimizer X θ y‖ ^ 2 ≤ batchAlignment X θ y := by
  by_cases hB : B = 0
  · subst B
    simp [batchAlignment, meanResidualTranspose]
  let _ : Nonempty (Fin B) := ⟨⟨0, Nat.pos_of_ne_zero hB⟩⟩
  have hnorm := batchGradientMinimizer_norm_le_mean X θ y
  have hsq : ‖batchGradientMinimizer X θ y‖ ^ 2 ≤
      ‖WithLp.toLp 2 (meanResidualTranspose X θ y)‖ ^ 2 := by
    simpa only [pow_two] using
      (mul_self_le_mul_self (norm_nonneg _) hnorm)
  calc
    ‖batchGradientMinimizer X θ y‖ ^ 2 ≤
        ‖WithLp.toLp 2 (meanResidualTranspose X θ y)‖ ^ 2 := hsq
    _ = batchAlignment X θ y := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl

/-- On a two-sample batch, the indexed raw residual gradients are exactly
the unordered pair of the two sample gradients. -/
theorem batchGradientRange_pair {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 2 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 2 → V) :
    Set.range (fun b : Fin 2 => batchResidualGradient (X b) θ (y b)) =
      {batchResidualGradient (X 0) θ (y 0),
        batchResidualGradient (X 1) θ (y 1)} := by
  apply Set.ext
  intro g
  constructor
  · rintro ⟨b, rfl⟩
    fin_cases b
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · intro hg
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- For two samples, the raw residual-gradient convex hull is the segment
between the two actual gradients at the current parameters. -/
theorem batchGradientHull_pair {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 2 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 2 → V) :
    convexHull ℝ (Set.range fun b : Fin 2 =>
        batchResidualGradient (X b) θ (y b)) =
      segment ℝ (batchResidualGradient (X 0) θ (y 0))
        (batchResidualGradient (X 1) θ (y 1)) := by
  rw [batchGradientRange_pair, convexHull_pair]

/-- The selected minimum-norm point on a two-sample residual-gradient hull
is exactly the closed-form segment minimum from `Hagi.Step`. -/
theorem batchGradientMinimizer_pair {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 2 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 2 → V) :
    batchGradientMinimizer X θ y =
      Hagi.Step.segmentMinNorm (batchResidualGradient (X 0) θ (y 0))
        (batchResidualGradient (X 1) θ (y 1)) := by
  apply Hagi.Step.eq_segmentMinNorm_of_mem_of_forall_norm_le
  · rw [← batchGradientHull_pair X θ y]
    exact batchGradientMinimizer_mem X θ y
  · intro p hp
    rw [← batchGradientHull_pair X θ y] at hp
    exact batchGradientMinimizer_norm_le X θ y hp

/-- Residual action is the dot product with the generating direction. -/
theorem dirAction_eq_dot {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ D : EuclideanSpace ℝ (Fin d)) (t : V) :
    dirAction X θ t D = ∑ j, residualTranspose X θ t j * D.ofLp j := by
  simp only [dirAction, ceLogits, residualTranspose, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro v _hv
  ring

/-- The finite-dimensional action is the Euclidean inner product with the
raw residual gradient. -/
theorem dirAction_eq_inner {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ D : EuclideanSpace ℝ (Fin d)) (t : V) :
    dirAction X θ t D = ⟪batchResidualGradient X θ t, D⟫_ℝ := by
  rw [dirAction_eq_dot, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  simp [batchResidualGradient_ofLp, RCLike.inner_apply, mul_comm]

/-- Projection variational inequality at `g0 = 0`: every sample raw
gradient has at least the minimizer's squared norm as alignment. -/
theorem batchGradientMinimizer_kkt {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (b : Fin B) :
    ‖batchGradientMinimizer X θ y‖ ^ 2 ≤
      ⟪batchResidualGradient (X b) θ (y b), batchGradientMinimizer X θ y⟫_ℝ := by
  letI : Nonempty (Fin B) := ⟨b⟩
  let C := convexHull ℝ (Set.range fun b => batchResidualGradient (X b) θ (y b))
  have hdist : ∀ c ∈ C,
      dist (batchGradientMinimizer X θ y) 0 ≤ dist c 0 := by
    intro c hc
    simpa [dist_eq_norm] using batchGradientMinimizer_norm_le X θ y hc
  have hvi := Hagi.Step.min_dist_to_vi C (convex_convexHull ℝ _) 0
    (batchGradientMinimizer X θ y) (batchGradientMinimizer_mem X θ y) hdist
    (batchResidualGradient (X b) θ (y b))
    (subset_convexHull ℝ _ ⟨b, rfl⟩)
  rw [zero_sub, inner_neg_left, inner_sub_right,
    real_inner_self_eq_norm_sq,
    real_inner_comm (batchResidualGradient (X b) θ (y b))
      (batchGradientMinimizer X θ y)] at hvi
  linarith

/-- Moving along minus the minimum-norm raw gradient gives the exact
per-sample directional action upper bound, with no mean-only step used. -/
theorem dirAction_neg_batchGradientMinimizer_le {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (b : Fin B) :
    dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y) ≤
      -‖batchGradientMinimizer X θ y‖ ^ 2 := by
  rw [dirAction_eq_inner, inner_neg_right]
  exact neg_le_neg (batchGradientMinimizer_kkt X θ y b)

/-- A nonzero minimizer can occur only on a nonempty batch. -/
theorem nonempty_fin_batch_of_minimizer_ne_zero {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y ≠ 0) : Nonempty (Fin B) := by
  classical
  by_contra hB
  apply hω
  simp [batchGradientMinimizer, hB]

/-- Strict KKT at nonzero minimizer forces every sample's exact CE range
along `-ω` to be positive. -/
theorem dirRange_neg_batchGradientMinimizer_pos {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y ≠ 0) (b : Fin B) :
    0 < dirRange (X b) (-batchGradientMinimizer X θ y) := by
  by_contra hpos
  have hR : dirRange (X b) (-batchGradientMinimizer X θ y) = 0 :=
    le_antisymm (le_of_not_gt hpos) (dirRange_nonneg _ _)
  have hzero := (dirRange_eq_zero_iff
    (X b) (-batchGradientMinimizer X θ y)).mp hR
  have hA := dirAction_neg_batchGradientMinimizer_le X θ y b
  have hA0 : dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y) = 0 := by
    simp [dirAction, hzero]
  have hn : 0 < ‖batchGradientMinimizer X θ y‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hω)
  rw [hA0] at hA
  linarith

/-- A nonzero minimum-norm raw gradient makes the feature-only batch range
coefficient strictly positive through the same exact range and norm facts. -/
theorem batchFeatureRangeCoefficient_pos_of_minimizer_ne_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y ≠ 0) :
    0 < batchFeatureRangeCoefficient X := by
  letI : Nonempty (Fin B) := nonempty_fin_batch_of_minimizer_ne_zero X θ y hω
  let b : Fin B := Classical.choice (inferInstance : Nonempty (Fin B))
  have hR := dirRange_neg_batchGradientMinimizer_pos X θ y hω b
  have hN : 0 < ‖batchGradientMinimizer X θ y‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hω)
  have hbound := dirRange_sq_le_batchFeatureRangeCoefficient_mul_norm_sq
    X (-batchGradientMinimizer X θ y) b
  rw [norm_neg] at hbound
  by_contra hC
  have hCzero : batchFeatureRangeCoefficient X = 0 :=
    le_antisymm (le_of_not_gt hC) (batchFeatureRangeCoefficient_nonneg X)
  rw [hCzero, zero_mul] at hbound
  nlinarith [sq_pos_of_pos hR]

/-- The common conflict-free finite window, using exact CE-range algebra.
These `eps` and `L` labels are not empirical smoothness assumptions. -/
noncomputable def batchCommonSafeWindow {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [Nonempty (Fin B)] : ℝ :=
  Hagi.Step.safeqpEtaMaxConflictFree
    (fun _ : Fin B => ‖batchGradientMinimizer X θ y‖ ^ 2)
    (fun b => (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 /
      (4 * ‖batchGradientMinimizer X θ y‖ ^ 2))
    (batchGradientMinimizer X θ y)

theorem batchCommonSafeWindow_pos {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [Nonempty (Fin B)]
    (hω : batchGradientMinimizer X θ y ≠ 0) : 0 < batchCommonSafeWindow X θ y := by
  unfold batchCommonSafeWindow
  apply Hagi.Step.safeqpEtaMaxConflictFree_pos
  · intro b
    exact div_pos (sq_pos_of_pos (dirRange_neg_batchGradientMinimizer_pos X θ y hω b))
      (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hω)))
  · intro b
    exact sq_pos_of_pos (norm_pos_iff.mpr hω)
  · exact hω

/-- Each raw SafeQP threshold simplifies to the exact CE-range threshold. -/
theorem batchCommonSafeWindow_le_threshold {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) [Nonempty (Fin B)]
    (hω : batchGradientMinimizer X θ y ≠ 0) (b : Fin B) :
    batchCommonSafeWindow X θ y ≤
      8 * ‖batchGradientMinimizer X θ y‖ ^ 2 /
        (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 := by
  have hraw := ((Hagi.Step.le_safeqpEtaMaxConflictFree_iff
    (fun _ : Fin B => ‖batchGradientMinimizer X θ y‖ ^ 2)
    (fun b => (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 /
      (4 * ‖batchGradientMinimizer X θ y‖ ^ 2))
    (batchGradientMinimizer X θ y)).mp
      (le_refl (batchCommonSafeWindow X θ y))).2 b
  have hn : ‖batchGradientMinimizer X θ y‖ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hω))
  have hR : (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (dirRange_neg_batchGradientMinimizer_pos X θ y hω b))
  unfold batchCommonSafeWindow
  calc
    Hagi.Step.safeqpEtaMaxConflictFree
        (fun _ : Fin B => ‖batchGradientMinimizer X θ y‖ ^ 2)
        (fun b => (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 /
          (4 * ‖batchGradientMinimizer X θ y‖ ^ 2))
        (batchGradientMinimizer X θ y) ≤
      2 * ‖batchGradientMinimizer X θ y‖ ^ 2 /
        ((dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 /
          (4 * ‖batchGradientMinimizer X θ y‖ ^ 2) *
            ‖batchGradientMinimizer X θ y‖ ^ 2) := hraw
    _ = 8 * ‖batchGradientMinimizer X θ y‖ ^ 2 /
        (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 := by
      field_simp [hn, hR]
      ring

/-- Canonical totalized common step: half the positive finite window at a
nonzero minimizer, and zero at an empty batch or zero direction. -/
noncomputable def batchCommonSafeEta {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : ℝ := by
  classical
  exact if hB : Nonempty (Fin B) then
    letI := hB
    if hω : batchGradientMinimizer X θ y = 0 then 0
    else batchCommonSafeWindow X θ y / 2
  else 0

@[simp] theorem batchCommonSafeEta_of_minimizer_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y = 0) :
    batchCommonSafeEta X θ y = 0 := by
  classical
  by_cases hB : Nonempty (Fin B)
  · simp [batchCommonSafeEta, hB, hω]
  · simp [batchCommonSafeEta, hB]

@[simp] theorem batchCommonSafeEta_empty {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 0 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 0 → V) : batchCommonSafeEta X θ y = 0 := by
  simp [batchCommonSafeEta]

theorem batchCommonSafeEta_pos_of_minimizer_ne_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y ≠ 0) :
    0 < batchCommonSafeEta X θ y := by
  classical
  letI : Nonempty (Fin B) := nonempty_fin_batch_of_minimizer_ne_zero X θ y hω
  rw [batchCommonSafeEta, dite_eq_left (inferInstance : Nonempty (Fin B)), dite_eq_right hω]
  exact half_pos (batchCommonSafeWindow_pos X θ y hω)

theorem batchCommonSafeEta_nonneg {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : 0 ≤ batchCommonSafeEta X θ y := by
  by_cases hω : batchGradientMinimizer X θ y = 0
  · rw [batchCommonSafeEta_of_minimizer_eq_zero X θ y hω]
  · exact (batchCommonSafeEta_pos_of_minimizer_ne_zero X θ y hω).le

/-- Halving the window makes eta strictly smaller than every sample's
quadratic-descent threshold. -/
theorem batchCommonSafeEta_lt_threshold {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y ≠ 0) (b : Fin B) :
    batchCommonSafeEta X θ y <
      8 * ‖batchGradientMinimizer X θ y‖ ^ 2 /
        (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 := by
  classical
  letI : Nonempty (Fin B) := nonempty_fin_batch_of_minimizer_ne_zero X θ y hω
  have heta : batchCommonSafeEta X θ y = batchCommonSafeWindow X θ y / 2 := by
    rw [batchCommonSafeEta, dite_eq_left (inferInstance : Nonempty (Fin B)), dite_eq_right hω]
  rw [heta]
  have hM := batchCommonSafeWindow_pos X θ y hω
  have hle := batchCommonSafeWindow_le_threshold X θ y hω b
  have hR : 0 < (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 :=
    sq_pos_of_pos (dirRange_neg_batchGradientMinimizer_pos X θ y hω b)
  have hth : 0 < 8 * ‖batchGradientMinimizer X θ y‖ ^ 2 /
      (dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 :=
    div_pos (mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hω))) hR
  linarith

/-- Parameter update in the common negative minimum-norm direction. -/
noncomputable def batchCommonNextParameters {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) : EuclideanSpace ℝ (Fin d) :=
  alongNext θ (-batchGradientMinimizer X θ y) (batchCommonSafeEta X θ y)

@[simp] theorem batchCommonNextParameters_of_minimizer_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y = 0) :
    batchCommonNextParameters X θ y = θ := by
  rw [batchCommonNextParameters, batchCommonSafeEta_of_minimizer_eq_zero X θ y hω,
    alongNext_zero]

@[simp] theorem batchCommonNextParameters_empty {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 0 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 0 → V) : batchCommonNextParameters X θ y = θ := by
  rw [batchCommonNextParameters, batchCommonSafeEta_empty, alongNext_zero]

/-- The half-window gives strict actual CE descent on every sample. -/
theorem ceOneHot_batchCommonNextParameters_lt {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y ≠ 0) (b : Fin B) :
    Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchCommonNextParameters X θ y)) <
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) := by
  letI : Nonempty V := ⟨y b⟩
  have heta := batchCommonSafeEta_pos_of_minimizer_ne_zero X θ y hω
  have hA := dirAction_neg_batchGradientMinimizer_le X θ y b
  have hR := dirRange_neg_batchGradientMinimizer_pos X θ y hω b
  have hwindow := batchCommonSafeEta_lt_threshold X θ y hω b
  have hscaled := (lt_div_iff₀ (sq_pos_of_pos hR)).mp hwindow
  have hlinear : batchCommonSafeEta X θ y *
      dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y) ≤
      -batchCommonSafeEta X θ y * ‖batchGradientMinimizer X θ y‖ ^ 2 := by
    calc
      batchCommonSafeEta X θ y *
          dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y) ≤
        batchCommonSafeEta X θ y * (-‖batchGradientMinimizer X θ y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hA heta.le
      _ = -batchCommonSafeEta X θ y * ‖batchGradientMinimizer X θ y‖ ^ 2 := by ring
  have hquadratic :
      (batchCommonSafeEta X θ y *
          dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 / 8 <
        batchCommonSafeEta X θ y * ‖batchGradientMinimizer X θ y‖ ^ 2 := by
    have hmul := mul_lt_mul_of_pos_left hscaled heta
    nlinarith [hmul]
  calc
    Hagi.ceOneHot (y b) (ceLogits (X b) (batchCommonNextParameters X θ y)) ≤
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) + batchCommonSafeEta X θ y *
        dirAction (X b) θ (y b) (-batchGradientMinimizer X θ y) +
        (batchCommonSafeEta X θ y *
          dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 / 8 := by
      rw [batchCommonNextParameters]
      exact ceOneHot_alongNext_le (X b) θ (-batchGradientMinimizer X θ y)
        (y b) heta.le
    _ ≤ Hagi.ceOneHot (y b) (ceLogits (X b) θ) -
        batchCommonSafeEta X θ y * ‖batchGradientMinimizer X θ y‖ ^ 2 +
        (batchCommonSafeEta X θ y *
          dirRange (X b) (-batchGradientMinimizer X θ y)) ^ 2 / 8 := by
      linarith
    _ < Hagi.ceOneHot (y b) (ceLogits (X b) θ) := by
      linarith

/-- Every sample is nonincreasing at the selected common update; the zero
direction branch is actual preservation rather than vacuous strict progress. -/
theorem ceOneHot_batchCommonNextParameters_le {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (b : Fin B) :
    Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchCommonNextParameters X θ y)) ≤
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) := by
  by_cases hω : batchGradientMinimizer X θ y = 0
  · rw [batchCommonNextParameters_of_minimizer_eq_zero X θ y hω]
  · exact (ceOneHot_batchCommonNextParameters_lt X θ y hω b).le

@[simp] theorem ceOneHot_batchCommonNextParameters_of_minimizer_eq_zero
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hω : batchGradientMinimizer X θ y = 0) (b : Fin B) :
    Hagi.ceOneHot (y b)
        (ceLogits (X b) (batchCommonNextParameters X θ y)) =
      Hagi.ceOneHot (y b) (ceLogits (X b) θ) := by
  rw [batchCommonNextParameters_of_minimizer_eq_zero X θ y hω]

@[simp] theorem batchLoss_batchCommonNextParameters_empty
    {V : Type} [Fintype V] {d : ℕ}
    (X : Fin 0 → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin 0 → V) : batchLoss X (batchCommonNextParameters X θ y) y = batchLoss X θ y := by
  rw [batchCommonNextParameters_empty]


end Hagi.Model.BatchCEDescent
