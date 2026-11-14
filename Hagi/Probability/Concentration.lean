import Hagi.Probability.CertifiedEstimator

/-!
# Unified concentration radius/confidence API (C287, A10 merge map)

One parameterized `radius`/`confidence` pair for the Hoeffding mean-tail
family, with the canonical theorem chain routed through it and comparison
lemmas fixing the strongest–weakest spine of the tree's concentration
statements (survey `.tmp/C287/survey.md`):

* `concConfidence ε n = exp(−2nε²)` — the CANONICAL one-sided [0,1]
  mean-tail confidence (`hoeffding_mean_tail`, the exponent the audit
  names as the one backing the Python gate);
* `concConfidenceTwoSided ε n = 2·exp(−2nε²)` — canonical two-sided;
* `concRadius δ n = sqrt(log(1/δ)/(2n))` — the matching radius, with the
  duality `concRadius_valid`;
* `concConfidence_pm1_rescale` — the C264 gate's [−1,1] form
  `exp(−nη²/2)` IS `concConfidence (η/2) n` (radius doubles on the
  [−1,1] scale);
* `hoeffdingBridge_weaker` — `Ensemble/HoeffdingBridge`'s
  `exp(−t²/(2n²))` bound follows from the canonical `exp(−2t²/n)`:
  deletion evidence (audit A10: bridge is the WEAKER leaf; quarantine
  disposition, not deleted here — the freeze lock awaits `--update`).
-/

namespace Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-- One-sided [0,1] Hoeffding mean-tail confidence: `concConfidence ε n
= exp(−2nε²)`, the canonical exponent of `hoeffding_mean_tail`. -/
noncomputable def concConfidence (eps : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-2 * (n : ℝ) * eps ^ 2)

/-- Two-sided [0,1] Hoeffding confidence: `2·exp(−2nε²)` (union of both
tails, `hoeffding_two_sided`). -/
noncomputable def concConfidenceTwoSided (eps : ℝ) (n : ℕ) : ℝ :=
  2 * concConfidence eps n

/-- Radius of the canonical one-sided confidence: the smallest ε at
which `concConfidence ε n ≤ δ`, `concRadius δ n =
sqrt(log(1/δ)/(2n))`. -/
noncomputable def concRadius (delta : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (1 / delta) / (2 * (n : ℝ)))

theorem concConfidence_nonneg (eps : ℝ) (n : ℕ) : 0 ≤ concConfidence eps n :=
  Real.exp_nonneg _

theorem concConfidenceTwoSided_nonneg (eps : ℝ) (n : ℕ) :
    0 ≤ concConfidenceTwoSided eps n :=
  mul_nonneg (by norm_num) (concConfidence_nonneg eps n)

/-- Radius nonnegativity (the square root is always nonnegative). -/
theorem concRadius_nonneg (delta : ℝ) (n : ℕ) : 0 ≤ concRadius delta n := by
  unfold concRadius
  exact Real.sqrt_nonneg _

/-- Duality: at the radius, the canonical confidence fits the budget
(`concConfidence (concRadius δ n) n ≤ δ` for `0 < δ < 1`, `n > 0`). -/
theorem concRadius_valid {delta : ℝ} {n : ℕ} (hdelta : 0 < delta)
    (hdelta1 : delta < 1) (hn : 0 < n) :
    concConfidence (concRadius delta n) n ≤ delta := by
  have hlog : 0 ≤ Real.log (1 / delta) :=
    Real.log_nonneg (le_of_lt ((one_lt_div hdelta).2 hdelta1))
  have hsq : (Real.sqrt (Real.log (1 / delta) / (2 * (n : ℝ)))) ^ 2
      = Real.log (1 / delta) / (2 * (n : ℝ)) :=
    Real.sq_sqrt (by positivity)
  unfold concConfidence concRadius
  rw [hsq]
  have hkey : (-2 * (n : ℝ)) * (Real.log (1 / delta) / (2 * (n : ℝ)))
      = -Real.log (1 / delta) := by
    field_simp
  rw [hkey]
  have hed : Real.exp (-Real.log (1 / delta)) = delta := by
    rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hdelta)]
    field_simp
  rw [hed]

/-- Canonical confidence is a confidence: strictly below 1 for any
positive radius and sample size. -/
theorem concConfidence_lt_one {eps : ℝ} {n : ℕ} (heps : 0 < eps)
    (hn : 0 < n) : concConfidence eps n < 1 := by
  unfold concConfidence
  apply Real.exp_lt_one_iff.mpr
  have hpos : (0:ℝ) < 2 * (n : ℝ) * eps ^ 2 := by positivity
  linarith

/-! ## Canonical theorem chain via the API -/

/-- `hoeffding_mean_tail` via the unified API: the canonical mean tail
`P(μ̂ − μ ≥ ε) ≤ concConfidence ε n`. -/
theorem hoeffding_mean_tail_api {n : ℕ} (p : Fin n → V → ℝ)
    (hp : IsProbSys p) (X : Fin n → V → ℝ)
    (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1) (hn : 0 < n)
    (eps : ℝ) (heps : 0 < eps) :
    prodPq p (fun ω => (n : ℝ) * eps ≤ centeredSum p X ω)
      ≤ concConfidence eps n :=
  hoeffding_mean_tail p hp X hX hn eps heps

/-- `hoeffding_two_sided` via the unified API:
`P(|μ̂ − μ| ≥ ε) ≤ concConfidenceTwoSided ε n`. -/
theorem hoeffding_two_sided_api {n : ℕ} (p : Fin n → V → ℝ)
    (hp : IsProbSys p) (X : Fin n → V → ℝ)
    (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1) (hn : 0 < n)
    (eps : ℝ) (heps : 0 < eps) :
    prodPq p (fun ω => (n : ℝ) * eps ≤ centeredSum p X ω
        ∨ centeredSum p X ω ≤ - (n : ℝ) * eps)
      ≤ concConfidenceTwoSided eps n := by
  unfold concConfidenceTwoSided
  exact hoeffding_two_sided p hp X hX hn eps heps

/-- `cert_upper` via the unified API: the certified upper confidence
`1 − concConfidence ε n ≤ P(ΣX − Σμ ≤ nε)`. -/
theorem cert_upper_api {n : ℕ} (p : Fin n → V → ℝ) (hp : IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps) :
    1 - concConfidence eps n
      ≤ prodPq p (fun ω => centeredSum p X ω ≤ (n : ℝ) * eps) :=
  cert_upper p hp X hX hn eps heps

/-! ## Consumer-form identity lemmas -/

/-- C264 gate [−1,1] rescale form: `exp(−nη²/2) = concConfidence (η/2)
n` — the [−1,1] radius η corresponds to [0,1] radius η/2 (radius
doubles on the doubled scale). Backs
`Contracts.GatePipeline.hoeffding_pm1_two_sided`. -/
theorem concConfidence_pm1_rescale {n : ℕ} (hn : 0 < n) (eta : ℝ) :
    Real.exp (- (n : ℝ) * eta ^ 2 / 2) = concConfidence (eta / 2) n := by
  unfold concConfidence
  congr 1
  have : ((eta / 2) ^ 2) = eta ^ 2 / 4 := by ring
  rw [this]
  field_simp
  ring

/-! ## Weaker-bridge comparison (deletion evidence, audit A10) -/

/-- `Ensemble/HoeffdingBridge.hoeffding_tail_via_weighted` bounds the
sum tail by `exp(−t²/(2n²))`; the canonical
`hoeffding_tail`/`hoeffding_mean_tail` chain bounds it by
`exp(−2t²/n)`, which is SMALLER for every `n ≥ 1` (exponent gap factor
n/4): the canonical bound IMPLIES the bridge bound. Together with the
bridge being an in-tree leaf (survey: no consumers), this is the
deletion evidence; disposition = quarantine flag awaiting the freeze
lock `--update`, per audit A10. -/
theorem hoeffdingBridge_weaker {n : ℕ} (hn : 0 < n) {t : ℝ} (_ht : 0 ≤ t) :
    Real.exp (-2 * t ^ 2 / (n : ℝ))
      ≤ Real.exp (-t ^ 2 / (2 * ((n : ℝ)) ^ 2)) := by
  have hnn : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : (1:ℝ) ≤ 4 * (n : ℝ) := by
    have hle : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    nlinarith
  apply Real.exp_le_exp.mpr
  have h4 : (0:ℝ) < 2 * ((n : ℝ)) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hnn h4]
  have h5 : (0:ℝ) ≤ t ^ 2 * (n : ℝ) * (4 * (n : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (sq_nonneg t) hnn.le) (by nlinarith)
  nlinarith [h5]

end Hagi.Probability
