/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.EnergyReasoning.Pseudolikelihood
import Hagi.Contracts.ComputeToQuality
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Data efficiency: samples to quality

The DATA-side complement of the compute-to-quality arc (
`Hagi.Contracts.ComputeToQuality`): how many SAMPLES certify that the
selected energy model is near-optimal in population PL-risk — the data-side
frontier item of the compute-to-quality arc.

All carriers are landed and CITED, not re-proved:

* the concentration carrier is
  (`Hagi.Probability.Concentration`): the canonical one-sided [0,1]
  confidence `concConfidence ε n = exp(−2nε²)` and the radius
  `concRadius δ n = sqrt(log(1/δ)/(2n))` (`concRadius_valid`);
* the finite-class carrier is
  (`finite_class_pl_margin_argmax`): empirical margin ≥ 2η over the
  winner ⟹ population-best with confidence
  `1 − 2|ι|·exp(−2nη²)`;
* the compute-ledger pattern is
  (`steps_to_quality`, `total_compute_to_quality`): the minimal-
  witness honesty interface.

The only NEW mathematics is the radius INVERSION — solving
`concConfidence η n ≤ δ/m` for n (the radius run backwards):

* `sampleComplexity m δ η = log(m/δ)/(2η²)`;
* `concConfidence_le_of_sample_bound`: `sampleComplexity m δ η ≤ n`
  ⟹ `concConfidence η n ≤ δ/m` (exact algebra: `exp` monotone plus
  `exp(−log(m/δ)) = δ/m`; no new concentration).

Compositions on top:

* MAIN 1 `samples_to_quality`: finite class + margin premise +
  `n ≥ sampleComplexity (2|ι|) δ η` ⟹ w.p. ≥ 1 − δ the empirical
  winner is the POPULATION-best hypothesis (C315's argmax with the
  explicit sample count; the union constant 2 of C264's two-sided
  event is why m = 2|ι|).  `samples_to_quality_subopt` is the
  γ-slack reading ("within γ of best"): η plays the role of the
  empirical accuracy below the margin (the frontier's γ−ε).
* MAIN 2 `data_compute_budget`: the JOINT resource certificate — the
  data book (selection event, probabilistic) AND the compute book
  (descent to quality, deterministic) AND the total ledger
  `n·w + Σ spends ≤ (sampleComplexity+1)·w + (Δ₀+d)/d·W`.  The two
  books are INDEPENDENT: no claim that the learned model improves
  descent.

Honest scope: finite classes only (`Fintype ι`); the margin is a
PREMISE on the sample (the interface, no margin-model claim);
NO active learning, NO curriculum, NO adaptive sampling (separate
frontier candidates, not claimed); sample minimality is a premise
(the step-ceiling honesty shape); no asymptotics; numbers live
in the numeric `Anchor` lemma only.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.DataToQuality

open Hagi.Probability Hagi.Probability.FiniteFamilyConfidence
open Hagi.Model.EnergyReasoning

/-! ## The inversion of the radius -/

/-- **Sample complexity functional** — the radius run backwards:
the minimal sample count at which the canonical one-sided confidence
`concConfidence η n = exp(−2nη²)` fits a per-class budget `δ/m`
(the inversion lemma below proves sufficiency; m is the union
multiplicity, `2·|class|` in MAIN 1). -/
noncomputable def sampleComplexity (m delta eta : ℝ) : ℝ :=
  Real.log (m / delta) / (2 * eta ^ 2)

/-- **The radius inversion** (the new glue): if the
sample count `n` reaches `sampleComplexity m δ η = log(m/δ)/(2η²)`,
then the canonical confidence fits the per-class budget:
`concConfidence η n ≤ δ/m`.  Exact algebra — the canonical [0,1]
exponent `exp(−2nε²)` of `hoeffding_mean_tail` inverted; no new
concentration mathematics (`exp` monotone + `exp(−log x) = 1/x`). -/
theorem concConfidence_le_of_sample_bound {delta m : ℝ}
    (hdelta : 0 < delta) (hm : 0 < m) {eta : ℝ} (heta : 0 < eta)
    {n : ℕ} (hn : sampleComplexity m delta eta ≤ (n : ℝ)) :
    concConfidence eta n ≤ delta / m := by
  have hmd : 0 < m / delta := div_pos hm hdelta
  have hsq : eta ^ 2 * (2 * sampleComplexity m delta eta)
      = Real.log (m / delta) := by
    unfold sampleComplexity
    field_simp
  have h2e : (0:ℝ) ≤ 2 * eta ^ 2 := by nlinarith [sq_nonneg eta]
  have hkey : Real.log (m / delta) ≤ 2 * (n : ℝ) * eta ^ 2 := by
    rw [← hsq]
    calc eta ^ 2 * (2 * sampleComplexity m delta eta)
        = sampleComplexity m delta eta * (2 * eta ^ 2) := by ring
      _ ≤ (n : ℝ) * (2 * eta ^ 2) := mul_le_mul_of_nonneg_right hn h2e
      _ = 2 * (n : ℝ) * eta ^ 2 := by ring
  calc concConfidence eta n = Real.exp (-2 * (n : ℝ) * eta ^ 2) := rfl
    _ ≤ Real.exp (-Real.log (m / delta)) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = delta / m := by
        rw [Real.exp_neg, Real.exp_log hmd, inv_div]

/-! ## MAIN 1: samples to quality -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- **MAIN 1 — samples to quality** (finite class, margin form): with
the margin premise (the empirical winner `best` beats every `k`
by ≥ 2η on the empirical PL-loss mean) and the EXPLICIT sample count
`n ≥ sampleComplexity (2|ι|) δ η = log(2|ι|/δ)/(2η²)`, the selected
hypothesis is the POPULATION-best with probability ≥ 1 − δ.
Composition `finite_class_pl_margin_argmax` gives confidence
`1 − 2|ι|·exp(−2nη²)`; the inversion at the union multiplicity
m = 2|ι| (the two-sided constant
`finite_family_abs_error_confidence`) fits the budget, closing the
remaining mass at δ. -/
theorem samples_to_quality {n : ℕ} {ι : Type} [Fintype ι]
    (hcard : 0 < Fintype.card ι)
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ) (hX : ∀ k i v, 0 ≤ X k i v ∧ X k i v ≤ 1)
    (hn : 0 < n) (eta : ℝ) (heta : 0 < eta) (best : ι)
    (hmargin : ∀ ω k,
      2 * eta ≤ empiricalMean (X k) ω - empiricalMean (X best) ω)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdcard : delta < 2 * (Fintype.card ι : ℝ))
    (hnsamp : sampleComplexity (2 * (Fintype.card ι : ℝ)) delta eta
      ≤ (n : ℝ)) :
    1 - delta ≤ prodPq p (fun ω => ∀ k,
      populationMean p (X best) ≤ populationMean p (X k)) := by
  have hc1 : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hcard2 : (0:ℝ) < 2 * (Fintype.card ι : ℝ) := by nlinarith
  have hinv := concConfidence_le_of_sample_bound hdelta hcard2 heta hnsamp
  have hmain := finite_class_pl_margin_argmax p hp X hX hn eta heta best hmargin
  have hmul : 2 * (Fintype.card ι : ℝ) * concConfidence eta n
      ≤ 2 * (Fintype.card ι : ℝ) * (delta / (2 * (Fintype.card ι : ℝ))) :=
    mul_le_mul_of_nonneg_left hinv (le_of_lt hcard2)
  have hsimp : 2 * (Fintype.card ι : ℝ) * (delta / (2 * (Fintype.card ι : ℝ)))
      = delta := by field_simp
  unfold concConfidence at hmul
  linarith

/-- **MAIN 1, γ-slack form** — the frontier's "within γ of best"
reading: under the same premises (η is the empirical accuracy below
the margin — the γ−ε of the sample-complexity folklore), the selected
hypothesis is γ-optimal in population PL-risk: its population loss is
within γ of every hypothesis's, in particular the best one's.  A
strict weakening of `samples_to_quality` (γ = 0 recovers
identification); no new bookkeeping. -/
theorem samples_to_quality_subopt {n : ℕ} {ι : Type} [Fintype ι]
    (hcard : 0 < Fintype.card ι)
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ) (hX : ∀ k i v, 0 ≤ X k i v ∧ X k i v ≤ 1)
    (hn : 0 < n) (eta : ℝ) (heta : 0 < eta) (best : ι)
    (hmargin : ∀ ω k,
      2 * eta ≤ empiricalMean (X k) ω - empiricalMean (X best) ω)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdcard : delta < 2 * (Fintype.card ι : ℝ))
    (hnsamp : sampleComplexity (2 * (Fintype.card ι : ℝ)) delta eta
      ≤ (n : ℝ)) (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    1 - delta ≤ prodPq p (fun ω => ∀ k,
      populationMean p (X best) ≤ populationMean p (X k) + gamma) := by
  have h := samples_to_quality hcard p hp X hX hn eta heta best hmargin
    hdelta hdcard hnsamp
  refine le_trans h ?_
  apply prodPq_mono p hp
  intro ω hω k
  have hk := hω k
  linarith

/-! ## MAIN 2: the joint data-compute ledger -/

variable {S TaskId : Type*}
variable (M : Hagi.Cert.SystemMetrics S TaskId) (obl : Hagi.Cert.StepObligations TaskId)

/-- **MAIN 2 — the joint data-compute budget certificate** (the GOAL's
unified resource account: quality at minimal compute AND data): a
conjunction of three INDEPENDENT books — no premise links the learned
model to the descent constants, and none is claimed:

* the DATA book (probabilistic): with `n` samples where
  `sampleComplexity (2|ι|) δ η ≤ n`, the selected energy model is the
  population-best w.p. ≥ 1 − δ (`samples_to_quality`);
* the COMPUTE book (deterministic): after `k` certified steps of
  uniform drop `d` with gap `Δ₀ ≤ k·d`, quality ε is met
  (`steps_to_quality`);
* the RESOURCE ledger: the total account
  `n·w + Σ spends ≤ (sampleComplexity+1)·w + (Δ₀+d)/d·W`, where w is
  the per-sample work (a premise-carried constant) and W the per-step
  spend cap.  Minimality of BOTH witnesses is honest-premise-form
  (`hnsamp_min`: n < sC+1; `hceil`: k·d ≤ Δ₀+d — the ceiling):
  nothing forces a bigger lab or a longer trajectory not to spend
  more; the bounds are SUFFICIENCY bounds for the minimal witnesses.
-/
theorem data_compute_budget (deltaLevel : S → ℝ)
    {n : ℕ} {ι : Type} [Fintype ι]
    (hcard : 0 < Fintype.card ι)
    (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : ι → Fin n → V → ℝ) (hX : ∀ k i v, 0 ≤ X k i v ∧ X k i v ≤ 1)
    (hn : 0 < n) (eta : ℝ) (heta : 0 < eta) (best : ι)
    (hmargin : ∀ ω k,
      2 * eta ≤ empiricalMean (X k) ω - empiricalMean (X best) ω)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdcard : delta < 2 * (Fintype.card ι : ℝ))
    (hnsamp : sampleComplexity (2 * (Fintype.card ι : ℝ)) delta eta
      ≤ (n : ℝ))
    (hnsamp_min : (n : ℝ) < sampleComplexity (2 * (Fintype.card ι : ℝ)) delta eta + 1)
    (w : ℝ) (hw0 : 0 ≤ w)
    (ε d W : ℝ) (k : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (t j) (t (j + 1)))
    (hdrop : ∀ j ∈ Finset.range k, d ≤ (steps j).drop)
    (hgap : M.objective (t 0) - ε ≤ k * d)
    (hceil : k * d ≤ M.objective (t 0) - ε + d)
    (hW : ∀ j ∈ Finset.range k, (steps j).budgetSpend ≤ W)
    (hd0 : 0 < d) (hW0 : 0 ≤ W) :
    (1 - delta ≤ prodPq p (fun ω => ∀ k',
        populationMean p (X best) ≤ populationMean p (X k')))
      ∧ M.objective (t k) ≤ ε
      ∧ (n : ℝ) * w + ∑ j ∈ Finset.range k, (steps j).budgetSpend
        ≤ (sampleComplexity (2 * (Fintype.card ι : ℝ)) delta eta + 1) * w
          + (M.objective (t 0) - ε + d) / d * W := by
  refine ⟨samples_to_quality hcard p hp X hX hn eta heta best hmargin
    hdelta hdcard hnsamp, ?_, ?_⟩
  · exact Hagi.Contracts.ComputeToQuality.steps_to_quality M obl deltaLevel
      ε d k t steps hdrop hgap
  · have hnw : (n : ℝ) * w ≤ (sampleComplexity (2 * (Fintype.card ι : ℝ)) delta eta + 1) * w :=
      mul_le_mul_of_nonneg_right (by linarith) hw0
    have hcomp := Hagi.Contracts.ComputeToQuality.total_compute_to_quality
      M obl deltaLevel ε d W k t steps hceil hW hd0 hW0
    linarith

/-! ## Numeric anchor -/

/-- numeric anchor: at class size `|ι| = 10`, `δ = 0.05`,
accuracy `η = 0.1` (the frontier's γ−ε), the sample-complexity
functional is `sampleComplexity 20 0.05 0.1 = log 400 / 0.02 ≈ 299.6`
(float, orientation only; log 400, not 200 — the union multiplicity
is m = 2|ι| = 20) — 300 samples suffice.  The PROVED bound is
the honest loose form `≤ 450` via `log 400 ≤ 9` (since `400 ≤ 2^9 ≤
e^9`, using `2 = 1 + 1 ≤ exp 1`) `concRadius_anchor_315`
style (slack 9 vs the true 5.99 documented). -/
theorem sample_complexity_anchor_334 :
    sampleComplexity (2 * 10) 0.05 0.1 ≤ 450 := by
  have h91 : (9:ℝ) / (2 * (0.1:ℝ) ^ 2) = 450 := by norm_num
  have hlog : Real.log ((2 * 10 : ℝ) / 0.05) ≤ 9 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < (2 * 10 : ℝ) / 0.05)]
    calc (2 * 10 : ℝ) / 0.05 ≤ (2:ℝ) ^ 9 := by norm_num
      _ ≤ (Real.exp 1) ^ 9 :=
          pow_le_pow_left₀ (by norm_num)
            (le_trans (by rw [add_comm]; norm_num) (Real.add_one_le_exp 1)) 9
      _ = Real.exp 9 := by rw [← Real.exp_nat_mul]; norm_num
  unfold sampleComplexity
  calc Real.log ((2 * 10 : ℝ) / 0.05) / (2 * (0.1:ℝ) ^ 2)
      ≤ 9 / (2 * (0.1:ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hlog (by norm_num)
    _ = 450 := h91

end Hagi.Contracts.DataToQuality
