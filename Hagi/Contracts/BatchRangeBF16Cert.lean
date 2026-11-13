/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEQuantized
import Hagi.Cert.Adapters
import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Runtime.BF16Delta

/-!
# BF16-guarded batch range-safe-step descent and cert transition

This file wires the C223 batch range-safe step into the canonical
`Hagi.Cert` transition kernel under a BF16 representation-error guard.

The certified drop is the exact C223 expression
`2 * batchAlignment^2 / batchLogitRangeSquare` from
`Hagi.Model.BatchCEDescent.batchLoss_logitSafeStep_le_residual`.  If
the logit update passes through a BF16 representation with uniform
per-logit error at most `eps` (a premise supplied by the caller — no
universal bf16 rounding claim is made), and the strict gate
`4 * eps < certified drop` holds, then the real bf16 next state
strictly decreases the true arithmetic-mean batch cross-entropy by
`Δ = drop - 2 * eps > 0` (the mean perturbation penalty is `2 * eps`
per the 2-Lipschitz one-hot CE bound
`Hagi.Model.CEQuantized.ceOneHot_le_of_abs_sub_le`; the gate keeps a
2x safety margin).  The eps = 0 regime corresponds to exact logit
readback, the case certified at the code level by
`Hagi.Runtime.BF16Delta.exists_sameBinade_difference` (same positive
normal binade differences are exactly representable); the code carrier
is rational `decode` while logits are real, so the eps = 0 theorem
takes an exact logit-equality premise rather than a cast.

The concrete instantiation `batchCEMetrics` puts the true batch loss
on the Euclidean parameter carrier with constant remaining budget/risk
levels (R1 polarity slice: `riskRem = riskTotalLimit - protectedRisk`
supplied by the caller, since the GrowthState carrier lives in
quarantined `Hagi.Legacy`), and the two `TransitionStep` constructors
realize the two-stage acceptance gate slice: progress when the gate is
active and `0 ≤ riskRem - opRisk`, hold via `HoldStep.id` otherwise.
These are formal one-step certificates, not runtime code.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Contracts.BatchRangeBF16Cert

open Hagi.Model
open Hagi.Model.BatchCEDescent

/-! ## BF16-guarded descent -/

/-- Uniform per-logit perturbation bound: if every logit of `θ'` is
within `eps` of the corresponding logit of `θ`, the true
arithmetic-mean batch loss moves by at most `2 * eps` (per-sample
2-Lipschitz one-hot cross-entropy). -/
theorem batchLoss_le_of_logitPerturbation {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ θ' : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) {eps : ℝ}
    (heps : 0 ≤ eps)
    (h : ∀ b v, |ceLogits (X b) θ' v - ceLogits (X b) θ v| ≤ eps) :
    batchLoss X θ' y ≤ batchLoss X θ y + 2 * eps := by
  have hsum : (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ')) ≤
      ∑ b, (Hagi.ceOneHot (y b) (ceLogits (X b) θ) + 2 * eps) :=
    Finset.sum_le_sum fun b _hb =>
      Hagi.Model.CEQuantized.ceOneHot_le_of_abs_sub_le (y b)
        (ceLogits (X b) θ') (ceLogits (X b) θ) eps (h b)
  by_cases hB : B = 0
  · subst hB
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    simp [batchLoss, Hagi.Probability.FiniteFamilyConfidence.empiricalMean]
    linarith
  · have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hB)
    unfold batchLoss Hagi.Probability.FiniteFamilyConfidence.empiricalMean
    have hsplit : (∑ b, (Hagi.ceOneHot (y b) (ceLogits (X b) θ) + 2 * eps)) =
        (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)) + (B : ℝ) * (2 * eps) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hsplit] at hsum
    show (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ')) / (B : ℝ)
        ≤ (∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)) / (B : ℝ) + 2 * eps
    have hkey : ((∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ')) : ℝ) / (B : ℝ)
        ≤ ((∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)) + (B : ℝ) * (2 * eps))
            / (B : ℝ) :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
    have h2 : ((∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ)) : ℝ) / (B : ℝ)
        + 2 * eps = ((∑ b, Hagi.ceOneHot (y b) (ceLogits (X b) θ))
          + (B : ℝ) * (2 * eps)) / (B : ℝ) := by
      rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hBpos)]
    rw [h2]
    exact hkey

/-- Workhorse: the C223 range-safe-step certified drop
`2 * batchAlignment^2 / batchLogitRangeSquare` survives a uniform
per-logit BF16 representation error `eps` whenever the strict gate
`4 * eps < certified drop` holds; the retained margin is
`drop - 2 * eps`. -/
theorem bf16_guarded_ceRange_descent_le {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ θbf : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) {eps : ℝ}
    (heps : 0 ≤ eps)
    (hbf : ∀ b v, |ceLogits (X b) θbf v
      - ceLogits (X b) (batchLogitNextParameters X θ y) v| ≤ eps)
    (hR : 0 < batchLogitRangeSquare X θ y)
    (hgate : 4 * eps <
      2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y) :
    batchLoss X θbf y ≤ batchLoss X θ y
      - (2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y
          - 2 * eps) := by
  have hres := batchLoss_logitSafeStep_le_residual X θ y hR
  have hpert := batchLoss_le_of_logitPerturbation X
    (batchLogitNextParameters X θ y) θbf y heps hbf
  linarith

/-- MAIN (C230): under the BF16 per-logit error guard and the strict
gate `4 * eps < 2 * batchAlignment^2 / batchLogitRangeSquare`, the
real bf16 next state strictly decreases the true arithmetic-mean batch
cross-entropy by some positive certified `Δ`. -/
theorem bf16_guarded_ceRange_descent {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ θbf : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) {eps : ℝ}
    (heps : 0 ≤ eps)
    (hbf : ∀ b v, |ceLogits (X b) θbf v
      - ceLogits (X b) (batchLogitNextParameters X θ y) v| ≤ eps)
    (hR : 0 < batchLogitRangeSquare X θ y)
    (hgate : 4 * eps <
      2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y) :
    ∃ Δ : ℝ, 0 < Δ ∧ batchLoss X θbf y ≤ batchLoss X θ y - Δ := by
  refine ⟨2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y
    - 2 * eps, ?_, ?_⟩
  · linarith
  · exact bf16_guarded_ceRange_descent_le X θ θbf y heps hbf hR hgate

/-- The eps = 0 regime: when the bf16 readback reproduces the ideal
range-safe-step logits exactly (the exact-difference case certified at
the code level by
`Hagi.Runtime.BF16Delta.exists_sameBinade_difference`), the whole
certified drop is retained. -/
theorem bf16_exact_binade_ceRange_descent {V : Type} [Fintype V] [Nonempty V]
    {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ θbf : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (hbf : ∀ b v, ceLogits (X b) θbf v
      = ceLogits (X b) (batchLogitNextParameters X θ y) v)
    (hR : 0 < batchLogitRangeSquare X θ y) :
    ∃ Δ : ℝ, 0 < Δ ∧ batchLoss X θbf y ≤ batchLoss X θ y - Δ := by
  refine bf16_guarded_ceRange_descent X θ θbf y (le_refl 0)
    (fun b v => by simp [hbf b v]) hR ?_
  have hA := batchAlignment_pos_of_logitRangeSquare_pos X θ y hR
  norm_num
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hA)) hR

/-! ## Cert/Core TransitionStep instantiation for the batch-CE setting -/

open Hagi.Cert.Adapters

/-- Concrete system metrics for the batch-CE setting on the Euclidean
parameter carrier: the objective is the true arithmetic-mean batch
loss; risk and budget are the concrete remaining levels (R1 polarity
slice: the caller supplies `riskRem = riskTotalLimit - protectedRisk`,
since the GrowthState carrier lives in quarantined `Hagi.Legacy`);
the task tag is `Unit`. -/
noncomputable def batchCEMetrics {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (y : Fin B → V)
    (riskRem budgetRem : ℝ) :
    Hagi.Cert.SystemMetrics (EuclideanSpace ℝ (Fin d)) Unit where
  objective := fun θ => batchLoss X θ y
  risk := fun _ => riskRem
  budget := fun _ => budgetRem
  task := fun _ => ()

/-- Projection law: the concrete objective readout is the true batch
loss. The two sides are not syntactically identical, so this
reflexivity proof involves definitional unfolding (legitimate). -/
theorem batchCEMetrics_objective {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (y : Fin B → V)
    (riskRem budgetRem : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    (batchCEMetrics X y riskRem budgetRem).objective θ = batchLoss X θ y :=
  rfl

/-- Projection law: the risk level is the constant remaining-risk
parameter at every state. -/
theorem batchCEMetrics_risk {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (y : Fin B → V)
    (riskRem budgetRem : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    (batchCEMetrics X y riskRem budgetRem).risk θ = riskRem := rfl

/-- Projection law: the budget level is the constant remaining-budget
parameter at every state. -/
theorem batchCEMetrics_budget {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (y : Fin B → V)
    (riskRem budgetRem : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    (batchCEMetrics X y riskRem budgetRem).budget θ = budgetRem := rfl

/-- Gate-active branch: the bf16-guarded range descent assembles into
a canonical progress `TransitionStep` on the batch-CE metrics with
zero floor obligations.  Budget/risk levels are preserved (zero spend)
and must be nonnegative; the operational-risk gate
`0 ≤ riskRem - opRisk` is an explicit premise (`opRisk` stays symbolic
until a slow-loop consumer exists). -/
noncomputable def batchCE_bf16_transitionStep_progress {V : Type} [Fintype V]
    [Nonempty V] {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ θbf : EuclideanSpace ℝ (Fin d)) (y : Fin B → V) {eps : ℝ}
    (heps : 0 ≤ eps) (opRisk riskRem budgetRem : ℝ)
    (hbf : ∀ b v, |ceLogits (X b) θbf v
      - ceLogits (X b) (batchLogitNextParameters X θ y) v| ≤ eps)
    (hR : 0 < batchLogitRangeSquare X θ y)
    (hgate : 4 * eps <
      2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y)
    (hbudgetnn : 0 ≤ budgetRem) (hrisknn : 0 ≤ riskRem)
    (hriskgate : 0 ≤ riskRem - opRisk) :
    Hagi.Cert.TransitionStep (batchCEMetrics X y riskRem budgetRem)
      (zeroFloorObligations Unit) θ θbf := by
  have hdesc : (batchCEMetrics X y riskRem budgetRem).objective θbf
      ≤ (batchCEMetrics X y riskRem budgetRem).objective θ
        - (2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y
            - 2 * eps) := by
    rw [batchCEMetrics_objective, batchCEMetrics_objective]
    exact bf16_guarded_ceRange_descent_le X θ θbf y heps hbf hR hgate
  have hdrop : 0 < 2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y
      - 2 * eps := by linarith
  have hfloors : Hagi.Cert.FloorsKept (batchCEMetrics X y riskRem budgetRem)
      (zeroFloorObligations Unit) θbf :=
    floorsKept_zeroFloor
      (Hagi.Contracts.BatchCETrajectory.batchLoss_nonneg X θbf y)
  have hbudget : (batchCEMetrics X y riskRem budgetRem).budget θbf
      = (batchCEMetrics X y riskRem budgetRem).budget θ :=
    (batchCEMetrics_budget X y riskRem budgetRem θbf).trans
      ((batchCEMetrics_budget X y riskRem budgetRem θ).symm)
  have hrisk : (batchCEMetrics X y riskRem budgetRem).risk θbf
      = (batchCEMetrics X y riskRem budgetRem).risk θ :=
    (batchCEMetrics_risk X y riskRem budgetRem θbf).trans
      ((batchCEMetrics_risk X y riskRem budgetRem θ).symm)
  have hbudgetnn : 0 ≤ (batchCEMetrics X y riskRem budgetRem).budget θbf := by
    rw [batchCEMetrics_budget]
    exact hbudgetnn
  have hrisknn : 0 ≤ (batchCEMetrics X y riskRem budgetRem).risk θbf := by
    rw [batchCEMetrics_risk]
    exact hrisknn
  exact Hagi.Cert.TransitionStep.progress
    (descentCertStep _ hdrop hdesc hbudget hbudgetnn hrisk hrisknn hfloors)

/-- Gate-inactive branch: at any floor-keeping parameter state the
identity hold `TransitionStep` is available with no progress claim. -/
noncomputable def batchCE_transitionStep_hold {V : Type} [Fintype V]
    [Nonempty V] {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (riskRem budgetRem : ℝ) :
    Hagi.Cert.TransitionStep (batchCEMetrics X y riskRem budgetRem)
      (zeroFloorObligations Unit) θ θ :=
  holdTransition (floorsKept_zeroFloor
    (Hagi.Contracts.BatchCETrajectory.batchLoss_nonneg X θ y))


/-! ## C249 derived-eps bridge from the rational BF16 carrier (A8 F3)

The eps premise of the guarded-descent gate is normally supplied by
the caller. For rational-valued target logits inside the bf16 normal
range read back through nearest codes, the per-logit perturbation is
bounded by the DERIVED `eps = 2 ^ (-8) * M` (unit roundoff of the
8-significant-bit carrier, `Hagi.Runtime.BF16Delta.abs_sub_le_of_isNearest_normal`),
removing the manual eps premise. The FP32-master necessity is
documented by the anchor round-trip counterexample
`Hagi.Runtime.BF16Delta.bf16_nearestRoundTrip_relativeError_gt`. -/

/-- `bf16_logitPerturbation_of_nearestNormalCodes`: if every target
logit of `θtarget` is the cast of a rational in the bf16 normal range
and the bf16 next state `θbf` reads each logit back through a nearest
finite code, then the uniform per-logit perturbation is at most the
derived `eps = 2 ^ (-8) * M` for any bound `M` on the target logits.
The rational-logit premise is explicit — a rational carrier cannot
round arbitrary real logits, and no universal rounding claim is made. -/
theorem bf16_logitPerturbation_of_nearestNormalCodes
    {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ)
    (θtarget θbf : EuclideanSpace ℝ (Fin d))
    (M : ℝ) (hM : 0 ≤ M)
    (hlogit : ∀ b v, |ceLogits (X b) θtarget v| ≤ M)
    (hcode : ∀ b v, ∃ q : ℚ, ∃ c : Hagi.Runtime.BF16Delta.Code,
      ceLogits (X b) θtarget v = (q : ℝ) ∧
        (2 : ℚ) ^ (-126 : ℤ) ≤ |q| ∧ |q| ≤ (2 : ℚ) ^ (127 : ℤ) ∧
        Hagi.Runtime.BF16Delta.IsNearest q c ∧
        ceLogits (X b) θbf v = ((Hagi.Runtime.BF16Delta.decode c : ℚ) : ℝ)) :
    ∀ b v, |ceLogits (X b) θbf v - ceLogits (X b) θtarget v| ≤
      ((2 : ℚ) ^ (-8 : ℤ) : ℝ) * M := by
  intro b v
  obtain ⟨q, c, hq, hmin, hmax, hnear, hread⟩ := hcode b v
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, abs_zero] at hmin
    exact absurd hmin (not_le.mpr (by positivity))
  have hbound := Hagi.Runtime.BF16Delta.abs_sub_le_of_isNearest_normal hq0 hmin hmax hnear
  rw [hread, hq]
  have hcast : |((Hagi.Runtime.BF16Delta.decode c : ℚ) : ℝ) - ((q : ℚ) : ℝ)| =
      (((|Hagi.Runtime.BF16Delta.decode c - q| : ℚ)) : ℝ) := by
    rw [Rat.cast_abs]
    congr 1
    push_cast
    ring
  rw [hcast]
  have h2 := (by exact_mod_cast hbound :
    (((|Hagi.Runtime.BF16Delta.decode c - q| : ℚ)) : ℝ) ≤
      (((2 : ℚ) ^ (-8 : ℤ) * |q| : ℚ) : ℝ))
  rw [Rat.cast_mul, show (((|q| : ℚ)) : ℝ) =
    |ceLogits (X b) θtarget v| from by rw [Rat.cast_abs, ← hq]] at h2
  push_cast at h2 ⊢
  exact h2.trans (mul_le_mul_of_nonneg_left (hlogit b v)
    (by positivity : (0 : ℝ) ≤ ((2 : ℚ) ^ (-8 : ℤ) : ℝ)))

/-- `bf16_guarded_ceRange_descent_of_nearestNormalCodes`: the C223
guarded-descent gate with the eps premise DERIVED from the rational
BF16 carrier instead of supplied manually: whenever the nearest-code
readback hypotheses of the bridge hold and the strict gate
`4 * (2 ^ (-8) * M) < 2 * batchAlignment^2 / batchLogitRangeSquare`
holds, the real bf16 next state strictly decreases the true batch
cross-entropy by some positive certified margin. -/
theorem bf16_guarded_ceRange_descent_of_nearestNormalCodes
    {V : Type} [Fintype V] [Nonempty V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (θbf : EuclideanSpace ℝ (Fin d))
    (y : Fin B → V) (M : ℝ) (hM : 0 ≤ M)
    (hlogit : ∀ b v,
      |ceLogits (X b) (batchLogitNextParameters X θ y) v| ≤ M)
    (hcode : ∀ b v, ∃ q : ℚ, ∃ c : Hagi.Runtime.BF16Delta.Code,
      ceLogits (X b) (batchLogitNextParameters X θ y) v = (q : ℝ) ∧
        (2 : ℚ) ^ (-126 : ℤ) ≤ |q| ∧ |q| ≤ (2 : ℚ) ^ (127 : ℤ) ∧
        Hagi.Runtime.BF16Delta.IsNearest q c ∧
        ceLogits (X b) θbf v = ((Hagi.Runtime.BF16Delta.decode c : ℚ) : ℝ))
    (hR : 0 < batchLogitRangeSquare X θ y)
    (hgate : 4 * (((2 : ℚ) ^ (-8 : ℤ) : ℝ) * M) <
      2 * batchAlignment X θ y ^ 2 / batchLogitRangeSquare X θ y) :
    ∃ Δ : ℝ, 0 < Δ ∧ batchLoss X θbf y ≤ batchLoss X θ y - Δ := by
  have hheps : 0 ≤ ((2 : ℚ) ^ (-8 : ℤ) : ℝ) * M :=
    mul_nonneg (by positivity) hM
  have hbf := bf16_logitPerturbation_of_nearestNormalCodes X
    (batchLogitNextParameters X θ y) θbf M hM hlogit hcode
  exact bf16_guarded_ceRange_descent X θ θbf y hheps hbf hR hgate

end Hagi.Contracts.BatchRangeBF16Cert
