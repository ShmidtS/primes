import Hagi.Model.CEDescent
import Hagi.Model.CEGroupedScale
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Step.ProjectionDescent
import Hagi.Step.SafeQPStep
import Hagi.Optimization.MirrorHedge
import Hagi.Model.BatchCEDescentHalfEta

/-!
# BatchCEDescentResidualNorm

Residual-gradient feature-norm bounds: `featureNormSum` majorization of `batchResidualGradient` and selected-loss propensity support.
-/

set_option relaxedAutoImplicit false

open scoped Matrix
open InnerProductSpace

namespace Hagi.Model.BatchCEDescent

open scoped Classical BigOperators Matrix
open Hagi.Probability


open scoped Classical BigOperators Matrix
open Hagi.Probability

/-- The actual arithmetic-mean raw residual gradient, without a nonempty
premise: both totalized sides also agree on the empty batch. -/
theorem mean_batchResidualGradient {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) :
    (B : ℝ)⁻¹ • ∑ b, batchResidualGradient (X b) θ (y b) =
      WithLp.toLp 2 (meanResidualTranspose X θ y) := by
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, Finset.sum_apply, batchResidualGradient_ofLp,
    meanResidualTranspose]
  rw [div_eq_inv_mul]

/-- The arithmetic-mean selected-gradient objective about the public actual
batch residual-mean transpose. Support is unnecessary for this scaling law. -/
theorem selectedMeanGradientMSE_batchResidual_eq_pmfMean
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) (q : PMF (Fin B))
    (h_card : 0 < Fintype.card (Fin B)) :
    Hagi.Probability.selectedMeanGradientMSE q
        (fun b => batchResidualGradient (X b) θ (y b)) =
      pmfMean q (fun b =>
        ‖((B : ℝ) * (q b).toReal)⁻¹ • batchResidualGradient (X b) θ (y b) -
          WithLp.toLp 2 (meanResidualTranspose X θ y)‖ ^ 2) := by
  simpa only [Fintype.card_fin, mean_batchResidualGradient] using
    Hagi.Probability.selectedMeanGradientMSE_eq_sum q
      (fun b => batchResidualGradient (X b) θ (y b)) h_card

/-- Coordinatewise unbiasedness of the supported actual CE-gradient draw for
its arithmetic-mean target. Zero propensity forces a zero residual vector. -/
theorem pmfMean_selectedMean_batchResidualGradient
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) (q : PMF (Fin B))
    (h_support : ∀ b, q b ≠ 0 ∨ batchResidualGradient (X b) θ (y b) = 0)
    (h_card : 0 < Fintype.card (Fin B)) (j : Fin d) :
    pmfMean q (fun b =>
      (((Fintype.card (Fin B) : ℝ) * (q b).toReal)⁻¹ •
        batchResidualGradient (X b) θ (y b)) j) =
      (WithLp.toLp 2 (meanResidualTranspose X θ y)) j := by
  have h_card_fin : 0 < B := by
    simpa only [Fintype.card_fin] using h_card
  have h_card_real : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr h_card_fin
  have hterm (b : Fin B) :
      (q b).toReal * (((B : ℝ) * (q b).toReal)⁻¹ *
          (batchResidualGradient (X b) θ (y b)) j) =
        (B : ℝ)⁻¹ * (batchResidualGradient (X b) θ (y b)) j := by
    by_cases hb : q b = 0
    · have hzero : batchResidualGradient (X b) θ (y b) = 0 :=
        (h_support b).elim (fun hne => (hne hb).elim) (fun hz => hz)
      simp [hb, hzero]
    · have hbReal : (q b).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr ⟨hb, q.apply_ne_top b⟩
      field_simp
  unfold pmfMean
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Fintype.card_fin]
  calc
    (∑ b, (q b).toReal * (((B : ℝ) * (q b).toReal)⁻¹ *
        (batchResidualGradient (X b) θ (y b)) j)) =
        ∑ b, (B : ℝ)⁻¹ * (batchResidualGradient (X b) θ (y b)) j :=
      Finset.sum_congr rfl (fun b _ => hterm b)
    _ = (B : ℝ)⁻¹ * ∑ b, (batchResidualGradient (X b) θ (y b)) j := by
      rw [Finset.mul_sum]
    _ = meanResidualTranspose X θ y j := by
      simp only [batchResidualGradient_ofLp, meanResidualTranspose,
        div_eq_inv_mul]

/-- Feature-only mass computed from the actual input matrix `X`: the sum of
its Euclidean row norms. -/
noncomputable def featureNormSum {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) : ℝ :=
  ∑ v, ‖(WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d))‖

/-- Exact weighted-row representation of the raw CE residual gradient. -/
private theorem batchResidualGradient_eq_sum_ceResidual_smul
    {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    batchResidualGradient X θ t =
      ∑ v, ceResidual X θ t v •
        (WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d)) := by
  apply PiLp.ext
  intro j
  simp only [batchResidualGradient_ofLp, residualTranspose,
    WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul]

/-- The CE softmax residual has absolute value at most one. -/
private theorem abs_ceResidual_le_one {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t v : V) :
    |ceResidual X θ t v| ≤ 1 := by
  let : Nonempty V := ⟨t⟩
  have hnonneg : 0 ≤ Hagi.Energy.smax (ceLogits X θ) v :=
    Hagi.Energy.smax_nonneg _ _
  have hle : Hagi.Energy.smax (ceLogits X θ) v ≤ 1 := by
    calc
      Hagi.Energy.smax (ceLogits X θ) v ≤
          ∑ w, Hagi.Energy.smax (ceLogits X θ) w :=
        Finset.single_le_sum
          (fun w _hw => Hagi.Energy.smax_nonneg (ceLogits X θ) w)
          (Finset.mem_univ v)
      _ = 1 := Hagi.Energy.smax_sum_one _
  by_cases hvt : v = t
  · subst v
    simp only [ceResidual, ↓reduceIte]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [ceResidual, hvt, ↓reduceIte, sub_zero,
      abs_of_nonneg hnonneg]
    exact hle

/-- Feature mass is nonnegative on every finite carrier. -/
private theorem featureNormSum_nonneg {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) : 0 ≤ featureNormSum X := by
  unfold featureNormSum
  positivity

/-- Feature-only norm bound for every raw CE residual gradient. In particular,
zero feature mass forces the raw gradient to vanish; the converse is not
asserted because residuals can cancel. -/
theorem norm_batchResidualGradient_le_featureNormSum
    {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V) :
    ‖batchResidualGradient X θ t‖ ≤ featureNormSum X := by
  rw [batchResidualGradient_eq_sum_ceResidual_smul]
  calc
    ‖∑ v, ceResidual X θ t v •
        (WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d))‖ ≤
        ∑ v, ‖ceResidual X θ t v •
          (WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d))‖ :=
      norm_sum_le _ _
    _ = ∑ v, |ceResidual X θ t v| *
        ‖(WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d))‖ := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ v, ‖(WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d))‖ := by
      apply Finset.sum_le_sum
      intro v _hv
      calc
        |ceResidual X θ t v| *
            ‖(WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d))‖ ≤
            1 * ‖(WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d))‖ :=
          mul_le_mul_of_nonneg_right (abs_ceResidual_le_one X θ t v)
            (norm_nonneg _)
        _ = ‖(WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d))‖ := one_mul _
    _ = featureNormSum X := rfl

/-- Zero feature mass forces the raw CE gradient to vanish.
The converse is false in general because rows with different residuals can
cancel, so no `featureNormSum X = 0 ↔ batchResidualGradient X θ t = 0` claim
is made. This proof deliberately does not use the residual bound. -/
private theorem batchResidualGradient_eq_zero_of_featureNormSum_eq_zero
    {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (t : V)
    (hF : featureNormSum X = 0) : batchResidualGradient X θ t = 0 := by
  have hnorm (v : V) :
      ‖(WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d))‖ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun v _hv => norm_nonneg
      (WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d)))).mp hF
      v (Finset.mem_univ v)
  have hrow (v : V) :
      (WithLp.toLp 2 (X v) : EuclideanSpace ℝ (Fin d)) = 0 :=
    norm_eq_zero.mp (hnorm v)
  rw [batchResidualGradient_eq_sum_ceResidual_smul]
  apply Finset.sum_eq_zero
  intro v _hv
  rw [hrow v, smul_zero]

/-- Positive total absolute feature mass makes the batch carrier nonempty. -/
private theorem card_pos_of_sum_abs_featureNormSum_pos
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ)
    (hF : 0 < ∑ b, |featureNormSum (X b)|) :
    0 < Fintype.card (Fin B) := by
  obtain ⟨b, _hb, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (f := fun b => |featureNormSum (X b)|) hF.ne'
  exact Fintype.card_pos_iff.mpr ⟨b⟩

/-- The feature-mass proposal supports every nonzero raw CE gradient. -/
private theorem selectedLoss_optimalPropensity_featureNormSum_support
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (hF : 0 < ∑ b, |featureNormSum (X b)|) :
    ∀ b, selectedLoss_optimalPropensity
        (fun b => featureNormSum (X b)) hF b ≠ 0 ∨
      batchResidualGradient (X b) θ (y b) = 0 := by
  intro b
  rcases selectedLoss_optimalPropensity_support
      (fun b => featureNormSum (X b)) hF b with hq | hzero
  · exact Or.inl hq
  · exact Or.inr
      (batchResidualGradient_eq_zero_of_featureNormSum_eq_zero
        (X b) θ (y b) hzero)

/-- For the supported feature-mass propensity, every item has nonzero
propensity or a zero raw-gradient target, and the `(n*q)⁻¹` draw is
coordinatewise unbiased for the actual C199 arithmetic-mean CE residual
transpose. This is not an actual-gradient Neyman-oracle construction. -/
theorem pmfMean_featureNormSum_optimalPropensity
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (hF : 0 < ∑ b, |featureNormSum (X b)|) (j : Fin d) :
    pmfMean (selectedLoss_optimalPropensity
        (fun b => featureNormSum (X b)) hF) (fun b =>
      (((Fintype.card (Fin B) : ℝ) *
          (selectedLoss_optimalPropensity
            (fun b => featureNormSum (X b)) hF b).toReal)⁻¹ •
        batchResidualGradient (X b) θ (y b)) j) =
      (WithLp.toLp 2 (meanResidualTranspose X θ y)) j := by
  exact pmfMean_selectedMean_batchResidualGradient X θ y
    (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
    (selectedLoss_optimalPropensity_featureNormSum_support X θ y hF)
    (card_pos_of_sum_abs_featureNormSum_pos X hF) j

/-- The C200 upper-envelope bound for arithmetic-mean MSE under the exact
feature-mass proposal and its actual raw CE gradients. This is only an upper
bound for the fixed full-sum vector target, not a local-optimality claim. -/
theorem selectedMeanGradientMSE_featureNormSum_le
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hF : 0 < ∑ b, |featureNormSum (X b)|) :
    selectedMeanGradientMSE (selectedLoss_optimalPropensity
      (fun b => featureNormSum (X b)) hF)
        (fun b => batchResidualGradient (X b) θ (y b)) ≤
      (B : ℝ)⁻¹ ^ 2 * ((∑ b, |featureNormSum (X b)|) ^ 2 -
        ‖∑ b, batchResidualGradient (X b) θ (y b)‖ ^ 2) := by
  simpa only [Fintype.card_fin] using
    selectedMeanGradientMSE_upperBoundPropensity_le
      (fun b => batchResidualGradient (X b) θ (y b))
      (fun b => featureNormSum (X b)) hF
      (fun b => norm_batchResidualGradient_le_featureNormSum (X b) θ (y b))

end Hagi.Model.BatchCEDescent
