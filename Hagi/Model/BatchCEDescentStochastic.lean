import Hagi.Model.CEDescent
import Hagi.Model.CEGroupedScale
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Step.ProjectionDescent
import Hagi.Step.SafeQPStep
import Hagi.Optimization.MirrorHedge
import Hagi.Model.BatchCEDescentLogitRange

/-!
# BatchCEDescentStochastic

C249 stochastic minibatch R'-step (A8 F3): `stochasticStepDraw`, expected descent, and feature-norm budgets.
-/

set_option relaxedAutoImplicit false

open scoped Matrix
open InnerProductSpace

namespace Hagi.Model.BatchCEDescent

open scoped Classical BigOperators Matrix
open Hagi.Probability



/-! ## C249 stochastic minibatch R'-step (A8 F3)

One inverse-propensity stochastic minibatch step along the raw CE
residual-gradient draw, with an honest expected-descent theorem: the
descent term is `eta * ‖meanResidualTranspose‖^2` (unbiasedness), the
curvature term is the global C216 Böhning range majorizer
`eta^2/8 * batchFeatureRangeCoefficient * E[‖ĝ‖^2]`, and the variance
is bounded by the C200 featureNormSum propensity machinery
`selectedMeanGradientMSE_featureNormSum_le`. No Ville or concentration
duplication — this is the one-step expectation statement. -/

/-- `stochasticStepDraw X θ y q b`: the inverse-propensity scaled draw `(B * q b)⁻¹ • batchResidualGradient` of the raw per-sample CE residual gradient — one stochastic minibatch estimate of the arithmetic-mean gradient at fixed `θ`. -/
noncomputable def stochasticStepDraw {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (q : PMF (Fin B)) (b : Fin B) :
    EuclideanSpace ℝ (Fin d) :=
  ((B : ℝ) * (q b).toReal)⁻¹ • batchResidualGradient (X b) θ (y b)

/-- `dirRange` is invariant under direction negation (logits flip sign, absolute values do not). -/
private theorem dirRange_neg {V : Type} [Fintype V] {d : ℕ}
    (X : Matrix V (Fin d) ℝ) (D : EuclideanSpace ℝ (Fin d)) :
    dirRange X (-D) = dirRange X D := by
  have hlogit (v : V) : ceLogits X (-D) v = -ceLogits X D v := by
    change (∑ j, (X v j * (-(D.ofLp j)) : ℝ)) = -(∑ j, X v j * D.ofLp j)
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  unfold dirRange
  congr 1
  apply Finset.sum_congr rfl
  intro v _hv
  rw [hlogit v, abs_neg]

/-- Pointwise dampened-step bound: for any direction `D` and every `eta ≥ 0`, the whole-batch loss after `θ + eta • (-D)` is at most `batchLoss X θ y - eta • ⟪meanResidualTranspose, D⟫ + eta^2/8 • batchFeatureRangeCoefficient X • ‖D‖^2` (C216 Böhning majorizer summed over the batch; the coefficient is the batch-summed `4 * ∑ featureAbsSum^2`, conservative vs the per-sample sum). -/
private theorem batchLoss_alongNext_neg_le {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hB : 0 < B) (D : EuclideanSpace ℝ (Fin d))
    {eta : ℝ} (heta : 0 ≤ eta) :
    batchLoss X (alongNext θ (-D) eta) y ≤
      batchLoss X θ y - eta *
        ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d)), D⟫_ℝ
        + eta ^ 2 / 8 * batchFeatureRangeCoefficient X * ‖D‖ ^ 2 := by
  have hBne : (B : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hB)
  have hsample (b' : Fin B) :=
    ceOneHot_alongNext_le (X b') θ (-D) (y b') heta
  have hinner (b' : Fin B) : dirAction (X b') θ (y b') (-D) =
      -⟪(batchResidualGradient (X b') θ (y b') :
        EuclideanSpace ℝ (Fin d)), D⟫_ℝ := by
    rw [dirAction_eq_inner, inner_neg_right]
  have hsuminner : ∑ b', ⟪(batchResidualGradient (X b') θ (y b') :
      EuclideanSpace ℝ (Fin d)), D⟫_ℝ =
      (B : ℝ) * ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), D⟫_ℝ := by
    rw [← sum_inner, ← mean_batchResidualGradient X θ y,
      inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    field_simp
  have hso : ∑ b', (dirRange (X b') D) ^ 2 ≤
      (B : ℝ) * (batchFeatureRangeCoefficient X * ‖D‖ ^ 2) := by
    calc
      ∑ b', (dirRange (X b') D) ^ 2 ≤
          ∑ b', (batchFeatureRangeCoefficient X * ‖D‖ ^ 2) :=
        Finset.sum_le_sum (fun b' _hb' =>
          dirRange_sq_le_batchFeatureRangeCoefficient_mul_norm_sq X D b')
      _ = (B : ℝ) * (batchFeatureRangeCoefficient X * ‖D‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsumdir : ∑ b', (eta * dirRange (X b') D) ^ 2 / 8 =
      (eta ^ 2 / 8) * ∑ b', (dirRange (X b') D) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b' _hb'
    ring
  have hneg : ∑ b', dirAction (X b') θ (y b') (-D) =
      -((B : ℝ) * ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), D⟫_ℝ) := by
    have hcongr : ∑ b', dirAction (X b') θ (y b') (-D) =
        ∑ b', (-(⟪(batchResidualGradient (X b') θ (y b') :
          EuclideanSpace ℝ (Fin d)), D⟫_ℝ)) :=
      Finset.sum_congr rfl (fun b' _hb' => hinner b')
    rw [hcongr, Finset.sum_neg_distrib, hsuminner]
  have hsum : (∑ b', Hagi.ceOneHot (y b')
      (ceLogits (X b') (alongNext θ (-D) eta))) ≤
      (∑ b', Hagi.ceOneHot (y b') (ceLogits (X b') θ)) +
      (-(eta * ((B : ℝ) * ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), D⟫_ℝ))) +
      (eta ^ 2 / 8) * ∑ b', (dirRange (X b') D) ^ 2 := by
    have h1 : (∑ b', Hagi.ceOneHot (y b')
        (ceLogits (X b') (alongNext θ (-D) eta))) ≤
        ∑ b', (Hagi.ceOneHot (y b') (ceLogits (X b') θ) +
          eta * dirAction (X b') θ (y b') (-D) +
          (eta * dirRange (X b') D) ^ 2 / 8) := by
      apply Finset.sum_le_sum
      intro b' _hb'
      have h := hsample b'
      rwa [dirRange_neg] at h
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
    rw [← Finset.mul_sum, hneg, hsumdir] at h1
    linarith
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
  show (∑ b', Hagi.ceOneHot (y b')
      (ceLogits (X b') (alongNext θ (-D) eta))) / (B : ℝ) ≤
    batchLoss X θ y - eta *
      ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), D⟫_ℝ
      + eta ^ 2 / 8 * batchFeatureRangeCoefficient X * ‖D‖ ^ 2
  calc (∑ b', Hagi.ceOneHot (y b')
      (ceLogits (X b') (alongNext θ (-D) eta))) / (B : ℝ) ≤
      ((∑ b', Hagi.ceOneHot (y b') (ceLogits (X b') θ)) +
      (-(eta * ((B : ℝ) * ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), D⟫_ℝ))) +
      (eta ^ 2 / 8) * ∑ b', (dirRange (X b') D) ^ 2) / (B : ℝ) := hdiv
    _ = (∑ b', Hagi.ceOneHot (y b') (ceLogits (X b') θ)) / (B : ℝ) -
      eta * ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), D⟫_ℝ +
      (eta ^ 2 / 8) * ((∑ b', (dirRange (X b') D) ^ 2) / (B : ℝ)) := by
        field_simp
        ring
    _ ≤ (∑ b', Hagi.ceOneHot (y b') (ceLogits (X b') θ)) / (B : ℝ) -
      eta * ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), D⟫_ℝ +
      (eta ^ 2 / 8) * (batchFeatureRangeCoefficient X * ‖D‖ ^ 2) := by
        have h8 : (0 : ℝ) ≤ eta ^ 2 / 8 := by positivity
        have hdivle : ((∑ b', (dirRange (X b') D) ^ 2) / (B : ℝ)) ≤
            batchFeatureRangeCoefficient X * ‖D‖ ^ 2 := by
          field_simp
          rw [mul_assoc]
          exact hso
        have hmul := mul_le_mul_of_nonneg_left hdivle h8
        linarith
    _ = batchLoss X θ y - eta *
      ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), D⟫_ℝ
      + eta ^ 2 / 8 * batchFeatureRangeCoefficient X * ‖D‖ ^ 2 := by
        rw [batchLoss, Hagi.Probability.FiniteFamilyConfidence.empiricalMean]
        ring


/-! ### Expected descent of the stochastic minibatch R'-step -/

/-- Under coordinatewise unbiasedness of `stochasticStepDraw` for the arithmetic-mean residual transpose, the expected alignment equals the squared mean-gradient norm: `pmfMean q ⟪m, ĝ⟫ = ‖m‖^2`. -/
private theorem pmfMean_inner_stochasticStepDraw_eq
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (q : PMF (Fin B))
    (h_unb : ∀ j, pmfMean q (fun b =>
        (stochasticStepDraw X θ y q b).ofLp j) =
      (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j) :
    pmfMean q (fun b =>
      ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), stochasticStepDraw X θ y q b⟫_ℝ) =
      ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  have hexp : ∀ b : Fin B, (q b).toReal *
      ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)), stochasticStepDraw X θ y q b⟫_ℝ =
      ∑ j, (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j *
        ((q b).toReal * (stochasticStepDraw X θ y q b).ofLp j) := by
    intro b
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  calc pmfMean q (fun b =>
        ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d)), stochasticStepDraw X θ y q b⟫_ℝ) =
      ∑ b, (q b).toReal *
        ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d)), stochasticStepDraw X θ y q b⟫_ℝ := rfl
    _ = ∑ b, ∑ j, (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j *
        ((q b).toReal * (stochasticStepDraw X θ y q b).ofLp j) :=
      Finset.sum_congr rfl (fun b _hb => hexp b)
    _ = ∑ j, ∑ b, (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j *
        ((q b).toReal * (stochasticStepDraw X θ y q b).ofLp j) :=
      Finset.sum_comm
    _ = ∑ j, (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j *
        pmfMean q (fun b => (stochasticStepDraw X θ y q b).ofLp j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [pmfMean, ← Finset.mul_sum]
    _ = ∑ j, (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j *
        (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [h_unb j]
    _ = ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- `batchLoss_expectedStochasticStep_le`: expected-descent theorem for one stochastic minibatch R'-step at fixed `θ`, sampling scheme `q` over the batch index set, draw `ĝ = stochasticStepDraw`: `E[L(θ - eta • ĝ)] ≤ L(θ) - eta * ‖m‖^2 + eta^2/8 * batchFeatureRangeCoefficient X * E[‖ĝ‖^2]`. Descent term from unbiasedness, curvature term from the global (all `eta ≥ 0`) Böhning range majorizer — no safe-window premise is hidden. -/
theorem batchLoss_expectedStochasticStep_le
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (q : PMF (Fin B)) (hB : 0 < B)
    {eta : ℝ} (heta : 0 ≤ eta)
    (h_unb : ∀ j, pmfMean q (fun b =>
        (stochasticStepDraw X θ y q b).ofLp j) =
      (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j) :
    pmfMean q (fun b =>
      batchLoss X (θ - eta • stochasticStepDraw X θ y q b) y) ≤
      batchLoss X θ y - eta *
        ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d))‖ ^ 2
        + eta ^ 2 / 8 * batchFeatureRangeCoefficient X *
          pmfMean q (fun b => ‖stochasticStepDraw X θ y q b‖ ^ 2) := by
  have hpt (b : Fin B) :
      batchLoss X (θ - eta • stochasticStepDraw X θ y q b) y ≤
        batchLoss X θ y - eta *
          ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d)), stochasticStepDraw X θ y q b⟫_ℝ
          + eta ^ 2 / 8 * batchFeatureRangeCoefficient X *
            ‖stochasticStepDraw X θ y q b‖ ^ 2 := by
    have hkey : θ - eta • stochasticStepDraw X θ y q b =
        alongNext θ (-(stochasticStepDraw X θ y q b)) eta := by
      simp only [alongNext]
      module
    rw [hkey]
    exact batchLoss_alongNext_neg_le X θ y hB _ heta
  have hmono := pmfMean_mono q (fun b _hb => hpt b)
  have hsplit : pmfMean q (fun b =>
      batchLoss X θ y - eta *
        ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d)), stochasticStepDraw X θ y q b⟫_ℝ
        + eta ^ 2 / 8 * batchFeatureRangeCoefficient X *
          ‖stochasticStepDraw X θ y q b‖ ^ 2) =
      batchLoss X θ y - eta *
        ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d))‖ ^ 2
        + eta ^ 2 / 8 * batchFeatureRangeCoefficient X *
          pmfMean q (fun b => ‖stochasticStepDraw X θ y q b‖ ^ 2) := by
    rw [pmfMean_add, pmfMean_sub, pmfMean_const,
      pmfMean_const_mul,
      pmfMean_inner_stochasticStepDraw_eq X θ y q h_unb]
    congr 1
    rw [pmfMean_const_mul]
  rw [hsplit] at hmono
  exact hmono

/-- Exact bias-variance identity for the stochastic step draw: `E[‖ĝ‖^2] = selectedMeanGradientMSE q g + ‖m‖^2` — expected squared norm is estimator MSE plus squared bias target norm. -/
theorem pmfMean_normSq_stochasticStepDraw_eq
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (q : PMF (Fin B)) (hB : 0 < B)
    (h_unb : ∀ j, pmfMean q (fun b =>
        (stochasticStepDraw X θ y q b).ofLp j) =
      (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j) :
    pmfMean q (fun b => ‖stochasticStepDraw X θ y q b‖ ^ 2) =
      Hagi.Probability.selectedMeanGradientMSE q
        (fun b => batchResidualGradient (X b) θ (y b)) +
      ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  have hcard : 0 < Fintype.card (Fin B) := by simpa using hB
  have hmean : ((B : ℝ))⁻¹ •
      ∑ b, batchResidualGradient (X b) θ (y b) =
      (WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)) := by
    simpa using mean_batchResidualGradient X θ y
  have hMSE := Hagi.Probability.selectedMeanGradientMSE_eq_sum q
    (fun b => batchResidualGradient (X b) θ (y b)) hcard
  have hcross : pmfMean q (fun b =>
      ⟪stochasticStepDraw X θ y q b -
        (WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d)),
        (WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d))⟫_ℝ) = 0 := by
    have hterm : ∀ b : Fin B,
        ⟪stochasticStepDraw X θ y q b -
          (WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d)),
          (WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d))⟫_ℝ =
        ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d)),
          stochasticStepDraw X θ y q b⟫_ℝ -
          ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
      intro b
      rw [inner_sub_left, real_inner_comm,
        real_inner_self_eq_norm_sq]
    have hfun : (fun b =>
        ⟪stochasticStepDraw X θ y q b -
          (WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d)),
          (WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d))⟫_ℝ) =
        (fun b =>
          ⟪(WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d)),
            stochasticStepDraw X θ y q b⟫_ℝ -
          ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d))‖ ^ 2) := funext hterm
    rw [hfun, pmfMean_sub, pmfMean_const,
      pmfMean_inner_stochasticStepDraw_eq X θ y q h_unb]
    ring
  have hexp : ∀ b : Fin B, ‖stochasticStepDraw X θ y q b‖ ^ 2 =
      ‖stochasticStepDraw X θ y q b -
        (WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d))‖ ^ 2 +
      2 * ⟪stochasticStepDraw X θ y q b -
        (WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d)),
        (WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d))⟫_ℝ +
      ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
    intro b
    have h := norm_add_sq (𝕜 := ℝ)
      (x := stochasticStepDraw X θ y q b -
        (WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d)))
      (y := (WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)))
    rw [sub_add_cancel] at h
    simpa using h
  have hsplit : pmfMean q (fun b => ‖stochasticStepDraw X θ y q b‖ ^ 2) =
      pmfMean q (fun b =>
        ‖stochasticStepDraw X θ y q b -
          (WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d))‖ ^ 2) +
      ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
    have hfun : (fun b => ‖stochasticStepDraw X θ y q b‖ ^ 2) =
        (fun b => ‖stochasticStepDraw X θ y q b -
          (WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d))‖ ^ 2 +
          2 * ⟪stochasticStepDraw X θ y q b -
            (WithLp.toLp 2 (meanResidualTranspose X θ y) :
              EuclideanSpace ℝ (Fin d)),
            (WithLp.toLp 2 (meanResidualTranspose X θ y) :
              EuclideanSpace ℝ (Fin d))⟫_ℝ +
          ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
            EuclideanSpace ℝ (Fin d))‖ ^ 2) := funext hexp
    rw [hfun, pmfMean_add, pmfMean_add, pmfMean_const_mul,
      pmfMean_const, hcross]
    ring
  have hfun2 : ∀ b : Fin B,
      (((B : ℝ) * (q b).toReal)⁻¹ • batchResidualGradient (X b) θ (y b) -
        (B : ℝ)⁻¹ • ∑ a, batchResidualGradient (X a) θ (y a)) =
      stochasticStepDraw X θ y q b -
        (WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d)) := by
    intro b
    rw [stochasticStepDraw, ← hmean]
  rw [hsplit, hMSE, Fintype.card_fin]
  have hf : (fun b =>
      ‖stochasticStepDraw X θ y q b -
        (WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d))‖ ^ 2) =
    (fun b =>
      ‖((B : ℝ) * (q b).toReal)⁻¹ • batchResidualGradient (X b) θ (y b) -
        (B : ℝ)⁻¹ • ∑ a, batchResidualGradient (X a) θ (y a)‖ ^ 2) :=
    funext fun b => by rw [hfun2 b]
  rw [hf]


/-- For the featureNormSum optimal propensity, the second moment of the stochastic step draw is at most `(∑ |featureNormSum|)^2 / B^2` — the C200 propensity MSE bound with the mean term recombined. -/
theorem pmfMean_normSq_stochasticStepDraw_featureNormSum_le
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hF : 0 < ∑ b, |featureNormSum (X b)|) :
    pmfMean (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
      (fun b => ‖stochasticStepDraw X θ y
        (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF) b‖ ^ 2) ≤
      (∑ b, |featureNormSum (X b)|) ^ 2 / (B : ℝ) ^ 2 := by
  have hB : 0 < B := by
    obtain ⟨b, _hb, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) (f := fun b => |featureNormSum (X b)|) hF.ne'
    simpa using Fintype.card_pos_iff.mpr ⟨b⟩
  have hcard : 0 < Fintype.card (Fin B) := by simpa using hB
  have hmean : ((B : ℝ))⁻¹ •
      ∑ b, batchResidualGradient (X b) θ (y b) =
      (WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d)) := by
    simpa using mean_batchResidualGradient X θ y
  have hunb : ∀ j, pmfMean
      (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
      (fun b => (stochasticStepDraw X θ y
        (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF) b).ofLp j) =
      (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j := by
    intro j
    simpa only [stochasticStepDraw, Fintype.card_fin] using
      pmfMean_featureNormSum_optimalPropensity X θ y hF j
  have hMSE := selectedMeanGradientMSE_featureNormSum_le X θ y hF
  have hnormmean : ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
      EuclideanSpace ℝ (Fin d))‖ ^ 2 =
      (B : ℝ)⁻¹ ^ 2 *
      ‖∑ b, batchResidualGradient (X b) θ (y b)‖ ^ 2 := by
    rw [← hmean, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < (B : ℝ)⁻¹ by positivity)]
    ring
  have h2 := pmfMean_normSq_stochasticStepDraw_eq X θ y
    (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
    hB hunb
  have hsq : (B : ℝ)⁻¹ ^ 2 *
      ((∑ b, |featureNormSum (X b)|) ^ 2 -
        ‖∑ b, batchResidualGradient (X b) θ (y b)‖ ^ 2) +
      (B : ℝ)⁻¹ ^ 2 *
      ‖∑ b, batchResidualGradient (X b) θ (y b)‖ ^ 2 =
      (∑ b, |featureNormSum (X b)|) ^ 2 / (B : ℝ) ^ 2 := by
    field_simp
    ring
  calc pmfMean (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
        (fun b => ‖stochasticStepDraw X θ y
          (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF) b‖ ^ 2) =
      Hagi.Probability.selectedMeanGradientMSE
        (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
        (fun b => batchResidualGradient (X b) θ (y b)) +
      ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d))‖ ^ 2 := h2
    _ ≤ (B : ℝ)⁻¹ ^ 2 *
        ((∑ b, |featureNormSum (X b)|) ^ 2 -
          ‖∑ b, batchResidualGradient (X b) θ (y b)‖ ^ 2) +
      (B : ℝ)⁻¹ ^ 2 *
      ‖∑ b, batchResidualGradient (X b) θ (y b)‖ ^ 2 := by
        rw [hnormmean]
        exact add_le_add hMSE (le_refl _)
    _ = (∑ b, |featureNormSum (X b)|) ^ 2 / (B : ℝ) ^ 2 := hsq

/-- `batchLoss_expectedStochasticStep_featureNormSum_le`: specialized expected-descent with an explicit feature-only variance term: `E[L(θ - eta • ĝ)] ≤ L(θ) - eta * ‖m‖^2 + eta^2/8 * batchFeatureRangeCoefficient X * (∑ |featureNormSum|)^2 / B^2` under the positive feature-mass premise. -/
theorem batchLoss_expectedStochasticStep_featureNormSum_le
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hF : 0 < ∑ b, |featureNormSum (X b)|)
    {eta : ℝ} (heta : 0 ≤ eta) :
    pmfMean (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
      (fun b => batchLoss X (θ - eta • stochasticStepDraw X θ y
        (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF) b) y) ≤
      batchLoss X θ y - eta *
        ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d))‖ ^ 2
        + eta ^ 2 / 8 * batchFeatureRangeCoefficient X *
          ((∑ b, |featureNormSum (X b)|) ^ 2 / (B : ℝ) ^ 2) := by
  have hB : 0 < B := by
    obtain ⟨b, _hb, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ) (f := fun b => |featureNormSum (X b)|) hF.ne'
    simpa using Fintype.card_pos_iff.mpr ⟨b⟩
  have hunb : ∀ j, pmfMean
      (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
      (fun b => (stochasticStepDraw X θ y
        (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF) b).ofLp j) =
      (WithLp.toLp 2 (meanResidualTranspose X θ y)).ofLp j := fun j => by
    simpa only [stochasticStepDraw, Fintype.card_fin] using
      pmfMean_featureNormSum_optimalPropensity X θ y hF j
  have hmain := batchLoss_expectedStochasticStep_le X θ y
    (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
    hB heta hunb
  have h2 := pmfMean_normSq_stochasticStepDraw_featureNormSum_le X θ y hF
  have h8 : (0 : ℝ) ≤ eta ^ 2 / 8 * batchFeatureRangeCoefficient X := by
    have : (0 : ℝ) ≤ eta ^ 2 / 8 := by positivity
    nlinarith [batchFeatureRangeCoefficient_nonneg X, sq_nonneg eta]
  have hmul := mul_le_mul_of_nonneg_left h2 h8
  nlinarith [hmain, hmul]

/-- `batchLoss_expectedStochasticStep_featureNormSum_lt`: the dampened step —
for `0 < eta` inside the gauge `eta * batchFeatureRangeCoefficient X * V̂ <
8 * ‖m‖^2` (with `V̂ = (∑ |featureNormSum|)^2 / B^2`), the expected loss
strictly decreases. The gauge is unsatisfiable when the mean gradient
vanishes, so the statement carries no vacuous branch. -/
theorem batchLoss_expectedStochasticStep_featureNormSum_lt
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (hF : 0 < ∑ b, |featureNormSum (X b)|)
    {eta : ℝ} (heta : 0 < eta)
    (hdamp : eta * batchFeatureRangeCoefficient X *
      ((∑ b, |featureNormSum (X b)|) ^ 2 / (B : ℝ) ^ 2) <
      8 * ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d))‖ ^ 2) :
    pmfMean (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF)
      (fun b => batchLoss X (θ - eta • stochasticStepDraw X θ y
        (selectedLoss_optimalPropensity (fun b => featureNormSum (X b)) hF) b) y) <
      batchLoss X θ y := by
  have hbound := batchLoss_expectedStochasticStep_featureNormSum_le X θ y hF heta.le
  have hnm : (0 : ℝ) ≤ ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
    EuclideanSpace ℝ (Fin d))‖ ^ 2 := by positivity
  have hc : (0 : ℝ) ≤ batchFeatureRangeCoefficient X *
      ((∑ b, |featureNormSum (X b)|) ^ 2 / (B : ℝ) ^ 2) := by
    have h1 := batchFeatureRangeCoefficient_nonneg X
    have h2 : (0 : ℝ) ≤ (∑ b, |featureNormSum (X b)|) ^ 2 /
        (B : ℝ) ^ 2 := by positivity
    nlinarith [h1, h2]
  have hkey : eta ^ 2 / 8 *
      (batchFeatureRangeCoefficient X *
        ((∑ b, |featureNormSum (X b)|) ^ 2 / (B : ℝ) ^ 2)) <
      eta * ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
        EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
    have h8 : (0 : ℝ) < eta / 8 := by linarith
    have hmul := mul_lt_mul_of_pos_left hdamp h8
    have e1 : (eta / 8) * (eta * batchFeatureRangeCoefficient X *
        ((∑ b, |featureNormSum (X b)|) ^ 2 / (B : ℝ) ^ 2)) =
        eta ^ 2 / 8 * (batchFeatureRangeCoefficient X *
          ((∑ b, |featureNormSum (X b)|) ^ 2 / (B : ℝ) ^ 2)) := by ring
    have e2 : (eta / 8) * (8 * ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d))‖ ^ 2) =
        eta * ‖(WithLp.toLp 2 (meanResidualTranspose X θ y) :
          EuclideanSpace ℝ (Fin d))‖ ^ 2 := by ring
    rw [e1, e2] at hmul
    exact hmul
  nlinarith [hbound, hkey, hnm, hc, heta.le]



end Hagi.Model.BatchCEDescent
