import Hagi.Probability.CertifiedEstimator
import Hagi.Probability.Freedman

/-!
# Unified concentration radius/confidence API (A10 merge map)

One parameterized `radius`/`confidence` pair for the Hoeffding mean-tail
family, with the canonical theorem chain routed through it and comparison
lemmas fixing the strongest–weakest spine of the tree's concentration
statements:

* `concConfidence ε n = exp(−2nε²)` — the CANONICAL one-sided [0,1]
  mean-tail confidence (`hoeffding_mean_tail`, the exponent the audit
  names as the one backing the Python gate);
* `concConfidenceTwoSided ε n = 2·exp(−2nε²)` — canonical two-sided;
* `concRadius δ n = sqrt(log(1/δ)/(2n))` — the matching radius, with the
  duality `concRadius_valid`;
* `concConfidence_pm1_rescale` — the gate's [−1,1] form
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

/-- gate [−1,1] rescale form: `exp(−nη²/2) = concConfidence (η/2)
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

/-! ## Unified premise API for the Freedman family (A17
stage 4)

The audit ask: ONE premise shape for the concentration family so
consumers take the radius from ONE place. The record below
packages the premise tuple; the radius corollaries are
BRIDGES (direct citations of the frozen carriers in
the Freedman canon (`Hagi.Probability.Freedman`)), not reproofs. The regime
split is kept honest: the variance-regime bound
(`concRadiusVar`, `exp(−r²/(4V))` under `c·r ≤ 2·V`) and the
all-regime mixed bound (`concRadiusMixed`, `exp(−r²/(4(V+c·r)))`)
are SEPARATE theorems with the regime premise explicit; the
constant-σ specialization is a lemma (`concPremise_comp_const`),
not a merged premise field. -/

/-- The unified concentration premise: the Markov-noise
premise tuple of the Freedman family — initial law, state kernel,
noise increments `g`, compensator rate `v` (per-state conditional
variance bound), horizon `T`, magnitude bound `c`, and the three
premise laws (bounded / centered / variance-dominated). ONE shape
covering (const `v = σ`) (actual compensator). -/
structure ConcPremise (α : Type*) [Fintype α] where
  /-- initial law of the state chain -/
  initial : PMF α
  /-- state kernel (adaptive: depends on step and state) -/
  K : ℕ → α → PMF α
  /-- noise increments (the martingale differences) -/
  g : ℕ → α → α → ℝ
  /-- compensator rate: per-state conditional variance bound -/
  v : ℕ → α → ℝ
  /-- horizon -/
  T : ℕ
  /-- noise magnitude bound -/
  c : ℝ
  /-- positivity of the magnitude bound -/
  hc : 0 < c
  /-- conditional noise boundedness -/
  hbounded : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
    ∀ b ∈ (K k a).support, |g k a b| ≤ c
  /-- conditional noise centeredness -/
  hmean : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
    pmfMean (K k a) (g k a) = 0
  /-- conditional variance domination -/
  hvar : ∀ k < T, ∀ a ∈ (markovLaw initial K k).support,
    pmfMean (K k a) (fun b => (g k a b) ^ 2) ≤ v k a

/-- The master fixed-λ tail on the record: for λ ∈ [0, 1/c]
and a deterministic compensator cap `V`, the Freedman tail
`P[S_k ≥ r ∧ C_k ≤ V] ≤ exp(−λr + λ²V)`. Direct citation of the
 `history_variance_freedman_lam` on the record fields. -/
theorem concPremise_tail_lam {α : Type*} [Fintype α] (P : ConcPremise α)
    (lam : ℝ) (hlam : 0 ≤ lam) (hclam : lam * P.c ≤ 1)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw P.initial P.K P.T k)
      (fun ω => if r ≤ historyAdditive P.g P.T k ω ∧
        historyCounter P.v P.T k ω ≤ V then 1 else 0)
      ≤ Real.exp (-lam * r + lam ^ 2 * V) :=
  history_variance_freedman_lam P.initial P.K P.g P.v P.T P.c lam
    hlam hclam P.hbounded P.hmean P.hvar k r V hr hV

/-- The variance-regime radius: in the regime `c·r ≤ 2·V`
the λ = r/(2V) optimization gives `exp(−r²/(4V))` — NO linear
term, strictly stronger than the mixed radius in this regime.
Direct citation `freedman_variance_radius`. The regime
premise is explicit: this bound is NOT available outside it. -/
theorem concRadiusVar {α : Type*} [Fintype α] (P : ConcPremise α)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 < V) (hrc : P.c * r ≤ 2 * V) :
    pmfMean (historyLaw P.initial P.K P.T k)
      (fun ω => if r ≤ historyAdditive P.g P.T k ω ∧
        historyCounter P.v P.T k ω ≤ V then 1 else 0)
      ≤ Real.exp (-r ^ 2 / (4 * V)) :=
  freedman_variance_radius P.initial P.K P.g P.v P.T P.c P.hc
    P.hbounded P.hmean P.hvar k r V hr hV hrc

/-- The all-regime mixed radius: with NO regime premise,
`exp(−r²/(4·(V + c·r)))`. Direct citation
`history_additive_freedman`. -/
theorem concRadiusMixed {α : Type*} [Fintype α] (P : ConcPremise α)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    pmfMean (historyLaw P.initial P.K P.T k)
      (fun ω => if r ≤ historyAdditive P.g P.T k ω ∧
        historyCounter P.v P.T k ω ≤ V then 1 else 0)
      ≤ Real.exp (-r ^ 2 / (4 * (V + P.c * r))) :=
  history_additive_freedman P.initial P.K P.g P.v P.T P.c P.hc
    P.hbounded P.hmean P.hvar k r V hr hV

/-- The constant-σ regime identification (regime honesty):
if the compensator rate is the constant `σ`, the actual
compensator `historyCounter` at any `k` is at most `T·σ` (the
 deterministic cap). This lemma is the ONLY bridge between
the constant-σ and compensator forms — the premise record itself
never blurs them. -/
theorem concPremise_comp_const {α : Type*} [Fintype α] (P : ConcPremise α)
    {σ : ℝ} (hσ : 0 ≤ σ) (hv : ∀ k a, P.v k a = σ) (k : ℕ)
    (ω : History α P.T) :
    historyCounter P.v P.T k ω ≤ (P.T : ℝ) * σ := by
  have heq : P.v = fun _ _ => σ := funext fun k => funext fun a => hv k a
  rw [heq, historyCounter_const]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.min_le_right k P.T)) hσ

/-- The exponent recovered through the unified API:
at `V := T·σ` the mixed radius is exactly
`stochastic_safe_step_whp` failure bound
`exp(−r²/(4·(T·σ + c·r)))`. The consumers of the form take
the radius from HERE; the Freedman canon's (`Hagi.Probability.Freedman`) own bridges stay frozen
(pin: they carry drift semantics, not radius derivation). -/
theorem concRadiusMixed_const {α : Type*} [Fintype α] (P : ConcPremise α)
    {σ : ℝ} (hσ : 0 ≤ σ) (k : ℕ) (r : ℝ)
    (hr : 0 < r) :
    pmfMean (historyLaw P.initial P.K P.T k)
      (fun ω => if r ≤ historyAdditive P.g P.T k ω ∧
        historyCounter P.v P.T k ω ≤ (P.T : ℝ) * σ then 1 else 0)
      ≤ Real.exp (-r ^ 2 / (4 * ((P.T : ℝ) * σ + P.c * r))) :=
  concRadiusMixed P k r ((P.T : ℝ) * σ) hr
    (mul_nonneg (Nat.cast_nonneg _) hσ)

/-- The one-draw variance-form confidence: the radius of a
single bounded centered measurement with variance at most `σ` —
`exp(−r²/(4σ))` in the regime `c·r ≤ 2σ`. Exposed as a def so
consumers (`noise_tail_le` and successors) take the
single-draw radius from the unified layer. -/
noncomputable def concOneDrawConfidence (σ r : ℝ) : ℝ :=
  Real.exp (-r ^ 2 / (4 * σ))

/-- The one-draw variance-form tail: for a bounded centered
`g` with variance at most `σ`, in the regime `c·r ≤ 2σ`, the
one-sided tail obeys `P[r ≤ g] ≤ concOneDrawConfidence σ r`.
This is the one-measurement instance of the variance-regime
radius (`freedman_variance_radius` at `V := σ`); the λ = r/(2σ)
optimization runs on the same carrier pair
(`pmfMean_exp_le` + `pmfMean_compensated_tail`). -/
theorem concOneDrawRadius {Ω : Type} [Fintype Ω] (law : PMF Ω)
    (g : Ω → ℝ) (c σ r : ℝ)
    (hσ : 0 < σ) (hr : 0 < r) (hrc : c * r ≤ 2 * σ)
    (hbounded : ∀ ω ∈ law.support, |g ω| ≤ c)
    (hmean : pmfMean law g = 0)
    (hvar : pmfMean law (fun ω => g ω ^ 2) ≤ σ) :
    pmfMean law (fun ω => if r ≤ g ω then 1 else 0)
      ≤ concOneDrawConfidence σ r := by
  unfold concOneDrawConfidence
  have hlam : 0 ≤ r / (2 * σ) := by positivity
  have hclam : r / (2 * σ) * c ≤ 1 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * σ)).mpr (by linarith)
  have hmgf := pmfMean_exp_le law g c σ (r / (2 * σ)) hlam hclam
    hbounded hmean.le hvar
  have hcomp : pmfMean law
      (fun ω => Real.exp (r / (2 * σ) * g ω - (r / (2 * σ)) ^ 2 * σ)) ≤ 1 := by
    have hmul : pmfMean law
        (fun ω => Real.exp (r / (2 * σ) * g ω - (r / (2 * σ)) ^ 2 * σ))
        = pmfMean law (fun ω => Real.exp (r / (2 * σ) * g ω))
          * Real.exp (-(r / (2 * σ)) ^ 2 * σ) := by
      rw [← pmfMean_mul_const]
      apply pmfMean_congr
      intro ω _
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hmul]
    calc pmfMean law (fun ω => Real.exp (r / (2 * σ) * g ω))
          * Real.exp (-(r / (2 * σ)) ^ 2 * σ)
        ≤ Real.exp ((r / (2 * σ)) ^ 2 * σ)
          * Real.exp (-(r / (2 * σ)) ^ 2 * σ) :=
          mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have htail := pmfMean_compensated_tail law g (fun _ => σ)
    (r / (2 * σ)) r σ hlam hcomp
  have hex : -(r / (2 * σ)) * r + (r / (2 * σ)) ^ 2 * σ
      = -r ^ 2 / (4 * σ) := by
    field_simp
    ring
  rw [hex] at htail
  convert htail using 1
  apply pmfMean_congr
  intro ω _
  simp

/-- The full Freedman radius: the Bennett-chord form
`exp(−r²/(2(V + c·r/3)))` through the unified premise record,
with NO regime premise (the λ = r/(V+cr/3) optimization is
admissible whenever V > 0). Direct citation
`freedman_full`. Strictly dominates `concRadiusMixed` (constants
4 → 2, c·r → c·r/3; equality only at c·r = 0) and is
incomparable with the variance-regime `concRadiusVar`: the
regime split is explicit in the comparison lemmas
(`freedman_full_exp_le_variance_exp` at c·r/3 ≤ V,
`freedman_variance_exp_le_full_exp` at V ≤ c·r/3). -/
theorem concRadiusFull {α : Type*} [Fintype α] (P : ConcPremise α)
    (k : ℕ) (r V : ℝ) (hr : 0 < r) (hV : 0 < V) :
    pmfMean (historyLaw P.initial P.K P.T k)
      (fun ω => if r ≤ historyAdditive P.g P.T k ω ∧
        historyCounter P.v P.T k ω ≤ V then 1 else 0)
      ≤ Real.exp (-r ^ 2 / (2 * (V + P.c * r / 3))) :=
  freedman_full P.initial P.K P.g P.v P.T P.c P.hc.le
    P.hbounded P.hmean P.hvar k r V hr hV

/-- The full radius dominates the mixed radius: through
the record, exp(−r²/(2(V+cr/3))) ≤ exp(−r²/(4(V+cr))) with NO
regime premise — the unified API now serves the strongest
all-regime bound. -/
theorem concRadiusFull_le_mixed {α : Type*} [Fintype α]
    (P : ConcPremise α) (r V : ℝ) (hr : 0 < r) (hV : 0 ≤ V) :
    Real.exp (-r ^ 2 / (2 * (V + P.c * r / 3)))
      ≤ Real.exp (-r ^ 2 / (4 * (V + P.c * r))) :=
  freedman_full_exp_le_mixed_exp r V P.c hr hV P.hc

section VilleChannel

open MeasureTheory ProbabilityTheory

/-- The Ville-channel premise record: the anytime-valid side
of the unified API. A significance `level` (α), a filtration, an
e-process `L` with the supermartingale / nonnegativity /
unit-budget premises — the premise shape behind `EProcMonitor`
 and the anytime-valid consumers. DATA only: the engine
(`ville_anytime_false_alarm`) lives above layer 2; the
master theorem `Hagi.Contracts.VilleMonitor.concVilleAnytime`
cites it once against this record. Adaptive-data caveat
inherited: the e-process premises are premise-form, exactly as in
 — nothing here claims validity on adaptively reused
data. -/
structure ConcVilleChannel {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- significance level -/
  level : ℝ
  /-- positivity of the level -/
  hlevel : 0 < level
  /-- the filtration the e-process is adapted to -/
  filt : Filtration ℕ m0
  /-- the e-process -/
  L : ℕ → Ω → ℝ
  /-- supermartingale premise -/
  hsuper : Supermartingale L filt μ
  /-- nonnegativity premise -/
  hnn : 0 ≤ L
  /-- unit-budget premise -/
  hL0 : μ[L 0] ≤ 1

end VilleChannel

end Hagi.Probability
