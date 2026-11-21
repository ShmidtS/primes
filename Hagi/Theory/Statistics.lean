/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.CertifiedEstimator
import Hagi.Probability.Concentration
import Hagi.Probability.FreedmanAdaptive
import Hagi.Probability.Azuma
import Hagi.Probability.FiniteFamilyConfidence
import Hagi.Unified.ParetoExecution
import Hagi.Unified.AnytimeMartingale
import Mathlib.Tactic

/-!
# Statistics — the holdout / anytime canon (W3, C435–C487)

One line of development, one canonical module. Each statistical
concept is described ONCE here; the five sections keep their
historical namespaces so every fully-qualified name is stable.

* Honest finite-population holdout risk (W3 / C435): a model
  fixed BEFORE the draw is a loss table; the holdout law is the
  uniform product law — unbiasedness, Hoeffding concentration,
  the selection-bias counterexample, and the finite-codebook
  uniform guarantee (`Hagi.Theory.HoldoutRisk`).
* Anytime e-process layer (source #71, FormalSLT direction):
  the Catoni × Ville composition gives time-uniform bounds —
  the check time may be adaptive (`Hagi.Unified.AnytimePACBayes`).
* Conditional two-domain confidence transport for guarded
  selection (`Hagi.Unified.TwoDomainConfidence`).
* Holdout WITHOUT replacement (C487): the sequential
  without-replacement kernel, the Doob martingale identity, and
  the Freedman-adapted concentration with partial fpc credit —
  strictly better than the with-replacement surrogate under an
  explicit checkable variance condition
  (`Hagi.Theory.HoldoutWithoutReplacement`).
* The anytime holdout admission-stop (C446, the statistics→growth
  bridge) lives in `Hagi.Theory.AnytimeHoldoutStop`: it consumes
  `Hagi.Theory.BlockAdmission`, which sits BELOW this canon
  (`BlockAdmission → CertCEHoldout → Statistics`), so merging it
  here would create an import cycle — kept separate, names stable.

Honest pins live in each section; the with-replacement surrogate
pin of C435 is closed by the C487 section above it.  Layer
decision: Theory — consumes the `Hagi.Probability` tower
(CertifiedEstimator / Concentration / Azuma / FreedmanAdaptive),
`Hagi.Unified.AnytimeMartingale` (Ville) and
`Hagi.Unified.ParetoExecution`; the bench mode `wrbound` of
`scripts/bench_bridge.py` consumes this module directly and
`grow-stop` via `Hagi.Theory.AnytimeHoldoutStop`.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

/-! ## Honest finite-population holdout (C435) — `Hagi.Theory.HoldoutRisk` -/

namespace Hagi.Theory.HoldoutRisk

open Hagi.Probability

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

/-! ## The finite-population setup -/

/-- Uniform density over the finite population. -/
noncomputable def popDens (_ω : Ω) : ℝ := (Fintype.card Ω : ℝ)⁻¹

theorem popDens_sum : ∑ ω : Ω, popDens (Ω := Ω) ω = 1 := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
    mod_cast Fintype.card_ne_zero (α := Ω)
  simp only [popDens, Finset.sum_const, Finset.card_univ]
  simp [hn]

/-- The `k`-fold holdout law (uniform product) is a probability
system in the `CertifiedEstimator` sense. -/
theorem popIsProb {k : ℕ} :
    IsProbSys (fun _ : Fin k => popDens (Ω := Ω)) := by
  intro _
  exact ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg _), popDens_sum⟩

/-- Population (true) risk of a fixed model: the uniform mean. -/
noncomputable def popMean (f : Ω → ℝ) : ℝ := (∑ ω, f ω) / (Fintype.card Ω : ℝ)

/-- Holdout estimate: the mean loss over the `k` sampled points. -/
noncomputable def holdoutMean {k : ℕ} (f : Ω → ℝ) (ωs : Fin k → Ω) : ℝ :=
  (∑ i, f (ωs i)) / (k : ℝ)

omit [Nonempty Ω] in
/-- Every coordinate mean of the uniform product system is the
population mean. -/
theorem coordMean_eq_popMean {k : ℕ} (f : Ω → ℝ) (i : Fin k) :
    coordMean (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) i
      = popMean f := by
  simp only [coordMean, popMean, popDens]
  rw [div_eq_inv_mul, Finset.mul_sum]

omit [Nonempty Ω] in
theorem coordSum_eq_popMean {k : ℕ} (f : Ω → ℝ) :
    ∑ i : Fin k, coordMean (fun _ : Fin k => popDens (Ω := Ω))
        (fun _ => f) i = ((k : ℕ) : ℝ) * popMean f := by
  rw [Finset.sum_congr rfl (fun i _ => coordMean_eq_popMean f i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-! ## (a) Unbiasedness for a fixed model -/

/-- **Holdout unbiasedness** (fixed model): under the uniform holdout
law, the expected holdout estimate equals the population risk. -/
theorem holdout_unbiased {k : ℕ} (hk : 0 < k) (f : Ω → ℝ) :
    prodE (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => holdoutMean f ωs) = popMean f := by
  have hkr : ((k : ℕ) : ℝ) ≠ 0 := mod_cast ne_of_gt hk
  have hmarg : ∑ ωs : Fin k → Ω,
      prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs * ∑ i, f (ωs i)
      = ∑ i : Fin k, coordMean
        (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) i := by
    have hexpand : ∀ ωs : Fin k → Ω,
        prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs * ∑ i, f (ωs i)
          = ∑ i, prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs
              * f (ωs i) := fun ωs => Finset.mul_sum _ _ _
    rw [Finset.sum_congr rfl (fun ωs _ => hexpand ωs), Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact marginal_prodE (fun _ : Fin k => popDens (Ω := Ω)) popIsProb i f
  calc prodE (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => holdoutMean f ωs)
      = ∑ ωs : Fin k → Ω,
          prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs
            * ((∑ i, f (ωs i)) / (k : ℝ)) := rfl
    _ = (∑ ωs : Fin k → Ω,
          prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs
            * ∑ i, f (ωs i)) / (k : ℝ) := by
        rw [Finset.sum_congr rfl (fun ωs _ => (mul_div_assoc
          (prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs)
          (∑ i, f (ωs i)) ((k : ℝ))).symm)]
        exact (Finset.sum_div (Finset.univ)
          (fun ωs => prodDens (fun _ : Fin k => popDens (Ω := Ω)) ωs
            * ∑ i, f (ωs i)) ((k : ℝ))).symm
    _ = (((k : ℕ) : ℝ) * popMean f) / (k : ℝ) := by
        rw [hmarg, coordSum_eq_popMean]
    _ = popMean f := by simp [hkr]

/-! ## (b) Concentration for a fixed model -/

omit [Nonempty Ω] in
/-- The deviation event implies the two-sided centered event of
`hoeffding_two_sided`: `|holdout − pop| ≥ ε` forces the centered sum
outside `[−kε, kε]` (only this direction is needed for the bound). -/
theorem holdout_dev_imp {k : ℕ} (hk : 0 < k) (f : Ω → ℝ) (eps : ℝ)
    (ωs : Fin k → Ω) (hdev : eps ≤ |holdoutMean f ωs - popMean f|) :
    ((k : ℝ) * eps ≤ centeredSum (fun _ : Fin k => popDens (Ω := Ω))
            (fun _ => f) ωs
        ∨ centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
            ≤ -((k : ℝ) * eps)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hkey : holdoutMean f ωs - popMean f
      = centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
          / (k : ℝ) := by
    unfold holdoutMean centeredSum
    rw [coordSum_eq_popMean]
    field_simp
  have habs : eps * (k : ℝ) ≤ |centeredSum
      (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs| := by
    rw [hkey, abs_div, abs_of_pos hkpos, le_div_iff₀ hkpos] at hdev
    exact hdev
  by_cases hcs : 0 ≤ centeredSum
        (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
  · exact Or.inl (by
      rw [abs_of_nonneg hcs] at habs
      linarith)
  · exact Or.inr (by
      have hn : centeredSum (fun _ : Fin k => popDens (Ω := Ω))
          (fun _ => f) ωs < 0 := lt_of_not_ge hcs
      rw [abs_of_neg hn] at habs
      linarith)

/-- **Holdout concentration** (fixed model, [0,1] losses): the
two-sided Hoeffding guarantee at the canonical exponent. -/
theorem holdout_concentration {k : ℕ} (hk : 0 < k) {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) (eps : ℝ) (heps : 0 < eps) :
    prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => eps ≤ |holdoutMean f ωs - popMean f|)
      ≤ concConfidenceTwoSided eps k := by
  have hmono := prodPq_mono (fun _ : Fin k => popDens (Ω := Ω)) popIsProb
    (fun ωs => eps ≤ |holdoutMean f ωs - popMean f|)
    (fun ωs => ((k : ℝ) * eps ≤ centeredSum
        (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
      ∨ centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
        ≤ -((k : ℝ) * eps)))
    (fun ωs hdev => holdout_dev_imp hk f eps ωs hdev)
  unfold concConfidenceTwoSided concConfidence
  have hconv : prodPq (fun _ : Fin k => popDens (Ω := Ω))
      (fun ωs => ((k : ℝ) * eps ≤ centeredSum
          (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
        ∨ centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ωs
          ≤ -((k : ℝ) * eps)))
    = prodPq (fun _ : Fin k => popDens (Ω := Ω))
      (fun ω => ((k : ℝ) * eps ≤ centeredSum
          (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ω
        ∨ centeredSum (fun _ : Fin k => popDens (Ω := Ω)) (fun _ => f) ω
          ≤ -((k : ℝ)) * eps)) := by
    refine prodPq_iff _ _ _ fun ωs => ?_
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  exact hmono.trans ((le_of_eq hconv).trans
    (hoeffding_two_sided (fun _ : Fin k => popDens (Ω := Ω)) popIsProb
      (fun _ => f) (fun _ _ => hf _) hk eps heps))

/-! ## (c) Selection bias: the honesty warning (negative theorem) -/
/-! ## (c) Selection bias: the honesty warning (negative theorem) -/

/-- The two-point counterexample loss: model `j` (of `Fin 2`) has zero
loss on point `j` and unit loss on the other point. -/
def twoPointLoss (j ω : Fin 2) : ℝ := if ω = j then 0 else 1

/-- **Population risk of every counterexample model is 1/2** — no
model in the two-point codebook beats chance on the population. -/
theorem selection_bias_pop_eq_half (j : Fin 2) :
    popMean (twoPointLoss j) = 1 / 2 := by
  unfold popMean twoPointLoss
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  rw [hcard]
  fin_cases j
  all_goals simp [Fin.sum_univ_two]

/-- **Selection bias breaks unbiasedness**: with `k = 1`, choosing the
model AFTER viewing the holdout point (`sel ωs = ωs 0`, which
minimizes the holdout loss — the selected model has zero loss on the
observed point) makes the holdout risk of the selected model
identically ZERO, while its population risk is 1/2
(`selection_bias_pop_eq_half`).  The expectation of the data-dependent
holdout estimate is `E[holdoutRisk θ*] = 0 ≠ 1/2 = E[popRisk θ*]` —
maximal bias; the fixed-`f` premise of `holdout_unbiased` is
essential. -/
theorem selection_bias_holdout_eq_zero (ωs : Fin 1 → Fin 2) :
    holdoutMean (twoPointLoss (ωs 0)) ωs = 0 := by
  unfold holdoutMean twoPointLoss
  simp

/-- The full negative statement: the expected holdout risk of the
holdout-selected model is ZERO while every model's population risk is
ONE HALF — unbiasedness fails by the maximal margin 1/2. -/
theorem selection_bias_expected_gap :
    prodE (fun _ : Fin 1 => popDens (Ω := Fin 2))
        (fun ωs => holdoutMean (twoPointLoss (ωs 0)) ωs) = 0
      ∧ ∀ j : Fin 2, popMean (twoPointLoss j) = 1 / 2 :=
  ⟨by
    unfold prodE
    refine Finset.sum_eq_zero fun ωs _ => ?_
    show prodDens (fun _ : Fin 1 => popDens (Ω := Fin 2)) ωs
      * holdoutMean (twoPointLoss (ωs 0)) ωs = 0
    rw [selection_bias_holdout_eq_zero, mul_zero],
  fun j => selection_bias_pop_eq_half j⟩

/-! ## (d) Uniform guarantee over a finite codebook -/

omit [Nonempty Ω] in
/-- Both the holdout and the population mean scale linearly, so the
deviation event for `g` at radius `eps` IS the deviation event for
`g / B` at radius `eps / B`. -/
theorem holdout_dev_rescale {k : ℕ} {B : ℝ} (hB : 0 < B) (g : Ω → ℝ)
    (ωs : Fin k → Ω) (eps : ℝ) :
    (eps ≤ |holdoutMean g ωs - popMean g|
      ↔ eps / B ≤ |holdoutMean (fun ω => g ω / B) ωs
          - popMean (fun ω => g ω / B)|) := by
  have h1 : holdoutMean (fun ω => g ω / B) ωs
      = holdoutMean g ωs / B := by
    rw [holdoutMean, holdoutMean, ← Finset.sum_div, div_div, div_div,
      mul_comm B ((k : ℝ))]
  have h2 : popMean (fun ω => g ω / B) = popMean g / B := by
    rw [popMean, popMean, ← Finset.sum_div, div_div, div_div,
      mul_comm B ((Fintype.card Ω : ℝ))]
  have hsub : holdoutMean g ωs / B - popMean g / B
      = (holdoutMean g ωs - popMean g) / B :=
    div_sub_div_same (holdoutMean g ωs) (popMean g) B
  rw [h1, h2, hsub, abs_div, abs_of_pos hB]
  constructor
  · intro h
    rw [le_div_iff₀ hB, mul_comm, mul_div_cancel₀ _ hB.ne']
    exact h
  · intro h
    have h' := (le_div_iff₀ hB).mp h
    rwa [mul_comm, mul_div_cancel₀ _ hB.ne'] at h'

/-- **Uniform holdout guarantee for a finite codebook**: losses bounded
by `B > 0`, codebook `Θ` fixed before sampling.  The CEHeldout
finite-codebook pattern, now with the population-risk tie: every model
in the codebook is simultaneously within `eps` of its population risk
except with probability at most `|Θ| · 2·exp(−2k(eps/B)²)`. -/
theorem holdout_uniform_codebook {Θ : Type} [Fintype Θ] {k : ℕ} (hk : 0 < k)
    (ℓ : Θ → Ω → ℝ) {B : ℝ} (hB : 0 < B)
    (hℓ : ∀ θ ω, 0 ≤ ℓ θ ω ∧ ℓ θ ω ≤ B) (eps : ℝ) (heps : 0 < eps) :
    prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => ∃ θ : Θ,
          eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
      ≤ (Fintype.card Θ : ℝ) * concConfidenceTwoSided (eps / B) k := by
  -- mono: the raw exist-event implies the scaled exist-event
  have himp : ∀ ωs : Fin k → Ω,
      (∃ θ : Θ, eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
        → ∃ θ : Θ, eps / B ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
            - popMean (fun ω => ℓ θ ω / B)| :=
    fun ωs ⟨θ, hθ⟩ => ⟨θ, (holdout_dev_rescale hB (ℓ θ) ωs eps).mp hθ⟩
  have hmono := prodPq_mono (fun _ : Fin k => popDens (Ω := Ω)) popIsProb
    (fun ωs => ∃ θ : Θ, eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
    (fun ωs => ∃ θ : Θ, eps / B ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
        - popMean (fun ω => ℓ θ ω / B)|)
    himp
  -- bridge to the ∃ ∈ univ form of the union bound
  have hmono2 := prodPq_mono (fun _ : Fin k => popDens (Ω := Ω)) popIsProb
    (fun ωs => ∃ θ : Θ, eps / B ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
        - popMean (fun ω => ℓ θ ω / B)|)
    (fun ωs => ∃ θ ∈ (Finset.univ : Finset Θ), eps / B
        ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
            - popMean (fun ω => ℓ θ ω / B)|)
    (fun ωs ⟨θ, hθ⟩ => ⟨θ, Finset.mem_univ θ, hθ⟩)
  have hunion := prodPq_union_finset
    (fun _ : Fin k => popDens (Ω := Ω)) popIsProb (Finset.univ : Finset Θ)
    (fun θ ωs => eps / B
      ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
          - popMean (fun ω => ℓ θ ω / B)|)
  -- per-model concentration at the scaled radius
  have hbound : ∀ θ : Θ,
      prodPq (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => eps / B
            ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
                - popMean (fun ω => ℓ θ ω / B)|)
        ≤ concConfidenceTwoSided (eps / B) k := by
    intro θ
    have hunit : ∀ ω : Ω, 0 ≤ ℓ θ ω / B ∧ ℓ θ ω / B ≤ 1 := by
      intro ω
      constructor
      · exact div_nonneg (hℓ θ ω).1 hB.le
      · exact (div_le_one hB).2 (hℓ θ ω).2
    exact holdout_concentration (f := fun ω => ℓ θ ω / B) hk hunit
      (eps / B) (div_pos heps hB)
  calc prodPq (fun _ : Fin k => popDens (Ω := Ω))
        (fun ωs => ∃ θ : Θ,
          eps ≤ |holdoutMean (ℓ θ) ωs - popMean (ℓ θ)|)
      ≤ prodPq (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => ∃ θ : Θ, eps / B
            ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
                - popMean (fun ω => ℓ θ ω / B)|) := hmono
    _ ≤ prodPq (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => ∃ θ ∈ (Finset.univ : Finset Θ), eps / B
            ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
                - popMean (fun ω => ℓ θ ω / B)|) := hmono2
    _ ≤ ∑ θ : Θ, prodPq (fun _ : Fin k => popDens (Ω := Ω))
          (fun ωs => eps / B
            ≤ |holdoutMean (fun ω => ℓ θ ω / B) ωs
                - popMean (fun ω => ℓ θ ω / B)|) := hunion
    _ ≤ ∑ θ : Θ, concConfidenceTwoSided (eps / B) k :=
          Finset.sum_le_sum fun θ _ => hbound θ
    _ = (Fintype.card Θ : ℝ) * concConfidenceTwoSided (eps / B) k := by
          rw [Finset.sum_const, Finset.card_univ]
          simp

end Hagi.Theory.HoldoutRisk

/-! ## Anytime PAC-Bayes / Ville e-process (source #71) — `Hagi.Unified.AnytimePACBayes` -/

namespace Hagi.Unified.AnytimePACBayes

open MeasureTheory Hagi.Unified

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}


/-- Монотонность реальной меры для вероятностных мер. -/
theorem real_mono_prob {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {s t : Set Ω} (h : s ⊆ t) :
    μ.real s ≤ μ.real t := by
  have h1 : μ s ≤ μ t := MeasureTheory.measure_mono h
  have h2 : μ t ≤ (1 : ENNReal) := by
    have hu : μ Set.univ = 1 := measure_univ
    calc μ t ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ t)
      _ = (1 : ENNReal) := hu
  have hu : μ Set.univ = 1 := measure_univ
  have h4 : μ t ≠ ⊤ := by
    have h : μ t < ⊤ :=
      lt_of_le_of_lt (le_trans (MeasureTheory.measure_mono (Set.subset_univ t)) hu.le)
        ENNReal.one_lt_top
    exact ne_of_lt h
  exact ENNReal.toReal_mono h4 h1

/-- ANYTIME CATONI: если L_t = exp(λ·S_t − ψ·t) —
неотрицательный супермартингал с E[L_0] ≤ 1, то с
вероятностью ≥ 1−δ при ВСЕХ t ≤ n одновременно
S_t ≤ (ψ·t + log(1/δ))/λ. Time-uniform гарантия: момент
проверки можно выбирать адаптивно (в т.ч. по данным),
неравенство держится равномерно. -/
theorem anytime_catoni {S : ℕ → Ω → ℝ} {lam ψ : ℝ}
    (hlam : 0 < lam)
    (L : ℕ → Ω → ℝ)
    (hL : Supermartingale L 𝒢 μ) (hLnn : 0 ≤ L)
    (hL0 : (∫ x, L 0 x ∂μ) ≤ 1)
    (hexp : ∀ t ω, L t ω = Real.exp (lam * S t ω - ψ * t))
    (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1),
      (ψ * t + Real.log (1/δ)) / lam < S t ω} ≤ δ := by
  have hcpos : 0 < 1 / δ := by positivity
  have hcross := ville_supermartingale hL hLnn n hcpos
  -- Markov/Ville: Pr[cross] ≤ E[L₀]/(1/δ) ≤ δ
  have hbound : (∫ x, L 0 x ∂μ) / (1 / δ) ≤ δ := by
    rw [div_le_iff₀ hcpos]
    have hdd : δ * (1 / δ) = 1 := by field_simp
    linarith [hL0, hdd]
  -- {S_t > threshold} ⊆ {L_t ≥ 1/δ} via strict monotonicity of exp
  have hsub : {ω | ∃ t ∈ Finset.range (n + 1),
      (ψ * ↑t + Real.log (1/δ)) / lam < S t ω}
      ⊆ {ω | ∃ t ∈ Finset.range (n + 1), 1 / δ ≤ L t ω} := by
    rintro ω ⟨t, ht, hSt⟩
    refine ⟨t, ht, ?_⟩
    rw [hexp t ω]
    rw [div_lt_iff₀ hlam] at hSt
    have h2 : Real.log (1/δ) < lam * S t ω - ψ * ↑t := by linarith
    have h3 : 1 / δ < Real.exp (lam * S t ω - ψ * ↑t) := by
      have h4 : Real.exp (Real.log (1/δ))
          < Real.exp (lam * S t ω - ψ * ↑t) :=
        Real.exp_lt_exp.mpr h2
      rwa [Real.exp_log hcpos] at h4
    exact le_of_lt h3
  calc μ.real {ω | ∃ t ∈ Finset.range (n + 1),
        (ψ * ↑t + Real.log (1/δ)) / lam < S t ω}
      ≤ μ.real {ω | ∃ t ∈ Finset.range (n + 1), 1 / δ ≤ L t ω} :=
        real_mono_prob hsub
    _ ≤ (∫ x, L 0 x ∂μ) / (1 / δ) := hcross
    _ ≤ δ := hbound

end Hagi.Unified.AnytimePACBayes

/-! ## Two-domain confidence transport — `Hagi.Unified.TwoDomainConfidence` -/

namespace Hagi.Unified.TwoDomainConfidence

open Hagi.Probability
open Hagi.Probability.FiniteFamilyConfidence
open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection

open scoped Classical in
/-- A common union-bound allowance transports old guarded non-regression and
an observed fixed-family target margin to a strict population-loss gap. -/
theorem finite_family_two_domain_guarded_improvement
    {V A : Type} {S : Type*} [Fintype V] [Nonempty V] [Fintype A]
    {n : ℕ} (law : Fin n → V → ℝ) (hp : IsProbSys law)
    (p : ControllerProblem A S) [DecidablePred p.safe]
    (estimate : (Fin n → V) → S → ℝ)
    (target : A → Fin n → V → ℝ)
    (h_target : ∀ a i v, 0 ≤ target a i v ∧ target a i v ≤ 1)
    (s : S) (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (eps_old eps_target delta : ℝ)
    (hn : 0 < n) (h_eps_old : 0 < eps_old) (h_eps_target : 0 < eps_target)
    (h_old : 1 - delta ≤ prodPq law (fun ω => ∀ a,
      |p.value (p.step a s) - estimate ω (p.step a s)| ≤ eps_old))
    (h_delta : 2 * (Fintype.card A : ℝ) *
      Real.exp (-2 * (n : ℝ) * eps_target ^ 2) ≤ delta)
    (h_observed : ∀ ω a, a ∈ feasible p M C →
      guardedRobustNext p (estimate ω) eps_old s M C stay h0 = p.step a s →
      2 * eps_target < empiricalMean (target stay) ω -
        empiricalMean (target a) ω) :
    1 - 2 * delta ≤ prodPq law (fun ω =>
      p.value (p.step stay s) ≤
        p.value (guardedRobustNext p (estimate ω) eps_old s M C stay h0) ∧
      ∃ a ∈ feasible p M C,
        guardedRobustNext p (estimate ω) eps_old s M C stay h0 = p.step a s ∧
        0 < populationMean law (target stay) - populationMean law (target a)) := by
  classical
  let OldGood : (Fin n → V) → Prop := fun ω => ∀ a,
    |p.value (p.step a s) - estimate ω (p.step a s)| ≤ eps_old
  let TargetGood : (Fin n → V) → Prop := fun ω => ∀ a,
    |populationMean law (target a) - empiricalMean (target a) ω| ≤ eps_target
  let Branches : Bool → (Fin n → V) → Prop := fun b ω =>
    if b then TargetGood ω else OldGood ω
  have hTargetConfidence : 1 - delta ≤ prodPq law TargetGood := by
    have ht := finite_family_abs_error_confidence law hp target h_target hn
      eps_target h_eps_target
    dsimp only [TargetGood]
    calc
      1 - delta ≤ 1 - 2 * (Fintype.card A : ℝ) *
          Real.exp (-2 * (n : ℝ) * eps_target ^ 2) := by linarith
      _ ≤ prodPq law TargetGood := ht
  have hBranches : ∀ b ∈ (Finset.univ : Finset Bool),
      1 - delta ≤ prodPq law (Branches b) := by
    intro b _hb
    cases b
    · simpa only [Branches, Bool.false_eq_true, ↓reduceIte] using h_old
    · simpa only [Branches, ↓reduceIte] using hTargetConfidence
  have hmain := probable_conclusion law hp (Finset.univ : Finset Bool) Branches
    (fun ω =>
      p.value (p.step stay s) ≤
        p.value (guardedRobustNext p (estimate ω) eps_old s M C stay h0) ∧
      ∃ a ∈ feasible p M C,
        guardedRobustNext p (estimate ω) eps_old s M C stay h0 = p.step a s ∧
        0 < populationMean law (target stay) - populationMean law (target a))
    delta hBranches (by
      intro ω hω
      have hOldGood : OldGood ω := by
        simpa only [Branches, Bool.false_eq_true, ↓reduceIte] using
          hω false (Finset.mem_univ false)
      have hTargetGood : TargetGood ω := by
        simpa only [Branches, ↓reduceIte] using
          hω true (Finset.mem_univ true)
      have hold := guardedRobustNext_quality_ge_stay p (estimate ω) eps_old
        s M C stay h0 (fun a _ha => hOldGood a)
      obtain ⟨a, ha, hnext⟩ := guardedRobustNext_exists p (estimate ω) eps_old
        s M C stay h0
      refine ⟨hold, a, ha, hnext, ?_⟩
      have hobs := h_observed ω a ha hnext
      have hb := abs_le.mp (hTargetGood stay)
      have haError := abs_le.mp (hTargetGood a)
      dsimp only [TargetGood] at hTargetGood
      linarith)
  simpa only [Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat] using hmain

end Hagi.Unified.TwoDomainConfidence

/-! ## Holdout without replacement: Serfling-oriented concentration (C487) — `Hagi.Theory.HoldoutWithoutReplacement` -/

namespace Hagi.Theory.HoldoutWithoutReplacement

open Hagi.Probability

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ## Постановка: без-возвратное ядро -/

/-- Дополнение до диапазона префикса — множество ещё не вытянутых. -/
def prefComp (t : ℕ) (pref : Fin t → Ω) : Finset Ω :=
  Finset.univ \ Finset.image pref Finset.univ

/-- **Без-возвратное ядро**: uniform на дополнении диапазона
префикса (паддинг uniform на всём Ω, когда дополнение пусто). -/
noncomputable def qdWR (t : ℕ) (pref : Fin t → Ω) (v : Ω) : ℝ :=
  if (prefComp t pref).card = 0 then (Fintype.card Ω : ℝ)⁻¹
  else if v ∈ prefComp t pref then (prefComp t pref).card⁻¹ else 0

/-- Условное среднее `f` по ядру (среднее оставшихся). -/
noncomputable def muCond (f : Ω → ℝ) (t : ℕ) (pref : Fin t → Ω) : ℝ :=
  ∑ v, qdWR t pref v * f v

/-- Holdout-оценка без возвращения: среднее по k вытянутым. -/
noncomputable def wrMean {k : ℕ} (f : Ω → ℝ) (ω : Fin k → Ω) : ℝ :=
  (∑ i, f (ω i)) / (k : ℝ)

/-- Среднее по популяции (как в `HoldoutRisk.popMean`). -/
noncomputable def wrPopMean (f : Ω → ℝ) : ℝ :=
  (∑ v, f v) / (Fintype.card Ω : ℝ)

/-- Дисперсия популяции `σ̂² = (1/N)Σ(f−μ)²`. -/
noncomputable def wrPopVar (f : Ω → ℝ) : ℝ :=
  (∑ v, (f v - wrPopMean f) ^ 2) / (Fintype.card Ω : ℝ)

/-! ## Ядро — вероятностные веса -/

theorem qdWR_nonneg (t : ℕ) (pref : Fin t → Ω) (v : Ω) :
    0 ≤ qdWR t pref v := by
  unfold qdWR
  split
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · split
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_refl _

theorem qdWR_sum [Nonempty Ω] (t : ℕ) (pref : Fin t → Ω) :
    ∑ v, qdWR t pref v = 1 := by
  unfold qdWR
  split
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := Ω))]
  · have hcard : 0 < (prefComp t pref).card := by omega
    have hsub : ∑ v ∈ prefComp t pref,
        (if v ∈ prefComp t pref then ((prefComp t pref).card : ℝ)⁻¹
          else 0)
        = ∑ v ∈ Finset.univ,
            (if v ∈ prefComp t pref then ((prefComp t pref).card : ℝ)⁻¹
              else 0) :=
      Finset.sum_subset (Finset.subset_univ _)
        (fun v _ hv => by simp [hv])
    have hcoe : ∑ v ∈ prefComp t pref,
        (if v ∈ prefComp t pref then ((prefComp t pref).card : ℝ)⁻¹
          else 0)
        = (prefComp t pref).card • ((prefComp t pref).card : ℝ)⁻¹ := by
      rw [Finset.sum_congr rfl (fun v hv =>
        (if_pos hv : (if v ∈ prefComp t pref
          then ((prefComp t pref).card : ℝ)⁻¹ else 0)
          = ((prefComp t pref).card : ℝ)⁻¹)), Finset.sum_const]
    rw [← hsub, hcoe]
    have hne : ((prefComp t pref).card : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hcard
    rw [nsmul_eq_mul, mul_inv_cancel₀ hne]

theorem wrIsProbSysD [Nonempty Ω] : IsProbSysD (qdWR (Ω := Ω)) :=
  fun t pref => ⟨fun v => qdWR_nonneg t pref v, qdWR_sum t pref⟩


/-! ## Свойства ядра и условные моменты -/


theorem prefComp_nonempty (t : ℕ) (pref : Fin t → Ω)
    (ht : t < Fintype.card Ω) :
    0 < (prefComp t pref).card := by
  have h1 : (Finset.image pref Finset.univ).card ≤ t := by
    have h2 := Finset.card_image_le
      (f := pref) (s := (Finset.univ : Finset (Fin t)))
    rwa [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : (prefComp t pref).card + (Finset.image pref Finset.univ).card
      = (Finset.univ : Finset Ω).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have h4 : (Finset.univ : Finset Ω).card = Fintype.card Ω :=
    Finset.card_univ
  omega

/-- Ключевое тождество суммирования по ядру: uniform-среднее по
дополнению диапазона. -/
theorem sum_qdWR_mul (t : ℕ) (pref : Fin t → Ω) (g : Ω → ℝ)
    (hC : (prefComp t pref).card ≠ 0) :
    ∑ v, qdWR t pref v * g v
      = (∑ v ∈ prefComp t pref, g v) / ((prefComp t pref).card : ℝ) := by
  unfold qdWR
  simp only [ite_mul, zero_mul, if_neg hC]
  have hsub : ∑ v ∈ prefComp t pref,
      (if v ∈ prefComp t pref
        then ((prefComp t pref).card : ℝ)⁻¹ * g v else 0)
      = ∑ v ∈ Finset.univ,
          (if v ∈ prefComp t pref
            then ((prefComp t pref).card : ℝ)⁻¹ * g v else 0) :=
    Finset.sum_subset (Finset.subset_univ _) fun v _ hv => by simp [hv]
  rw [← hsub]
  have hcoe : ∑ v ∈ prefComp t pref,
      (if v ∈ prefComp t pref
        then ((prefComp t pref).card : ℝ)⁻¹ * g v else 0)
      = ((prefComp t pref).card : ℝ)⁻¹ * ∑ v ∈ prefComp t pref, g v := by
    rw [Finset.sum_congr rfl fun v hv =>
      (if_pos hv : (if v ∈ prefComp t pref
        then ((prefComp t pref).card : ℝ)⁻¹ * g v else 0)
        = ((prefComp t pref).card : ℝ)⁻¹ * g v),
      Finset.mul_sum]
  rw [hcoe]
  field_simp

/-- Условное среднее — среднее по оставшимся. -/
theorem muCond_eq (f : Ω → ℝ) (t : ℕ) (pref : Fin t → Ω)
    (hC : (prefComp t pref).card ≠ 0) :
    muCond f t pref
      = (∑ v ∈ prefComp t pref, f v) / ((prefComp t pref).card : ℝ) :=
  sum_qdWR_mul t pref f hC

/-- Условное среднее лежит в выпуклой оболочке значений. -/
theorem muCond_mem [Nonempty Ω] {f : Ω → ℝ} (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    (t : ℕ) (pref : Fin t → Ω) :
    0 ≤ muCond f t pref ∧ muCond f t pref ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun v _ =>
      mul_nonneg (qdWR_nonneg t pref v) (hf v).1
  · have hle : muCond f t pref ≤ ∑ v, qdWR t pref v * 1 :=
      Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (hf v).2 (qdWR_nonneg t pref v)
    have hsum : ∑ v, qdWR t pref v * 1 = 1 := by
      rw [Finset.sum_congr rfl
        (fun v _ => mul_one (qdWR t pref v)), qdWR_sum]
    linarith

/-- **(b) Условное центрирование** — мартингальность приращений:
среднее центрированного приращения по ядру равно нулю (тождество
для ЛЮБОГО префикса — посылки машины C438). -/
theorem wr_cond_mean_zero [Nonempty Ω] (f : Ω → ℝ) (t : ℕ) (pref : Fin t → Ω) :
    ∑ v, qdWR t pref v * (f v - muCond f t pref) = 0 := by
  have h1 : ∑ v, qdWR t pref v * (f v - muCond f t pref)
      = ∑ v, (qdWR t pref v * f v
          - qdWR t pref v * muCond f t pref) :=
    Finset.sum_congr rfl fun v _ => by ring
  have h2 : ∑ v, qdWR t pref v * muCond f t pref
      = muCond f t pref := by
    calc ∑ v, qdWR t pref v * muCond f t pref
        = ∑ v, muCond f t pref * qdWR t pref v :=
          Finset.sum_congr rfl fun v _ => mul_comm _ _
      _ = muCond f t pref * ∑ v, qdWR t pref v :=
          (Finset.mul_sum Finset.univ (fun v => qdWR t pref v)
            (muCond f t pref)).symm
      _ = muCond f t pref * 1 := by rw [qdWR_sum]
      _ = muCond f t pref := mul_one _
  have h3 : ∑ v, qdWR t pref v * f v = muCond f t pref := rfl
  rw [h1, Finset.sum_sub_distrib, h3, h2]
  ring

/-- **(b) Условная дисперсия — точная гипер-формула шага**:
среднее квадрата центрированного значения = SS_C/|C|, сумма
квадратов отклонений от среднего оставшихся, делённая на их
число (гипергеометрическая структура без гипергеометрии). -/
theorem wr_cond_var (f : Ω → ℝ) (t : ℕ) (pref : Fin t → Ω)
    (hC : (prefComp t pref).card ≠ 0) :
    ∑ v, qdWR t pref v * (f v - muCond f t pref) ^ 2
      = (∑ v ∈ prefComp t pref, (f v - muCond f t pref) ^ 2)
        / ((prefComp t pref).card : ℝ) :=
  sum_qdWR_mul t pref _ hC

/-! ## Junk-траектории (повторы) имеют нулевую плотность -/

theorem qdWR_zero_of_mem_range {t : ℕ} (pref : Fin t → Ω) {v : Ω}
    (hv : v ∈ Finset.image pref Finset.univ)
    (hN : t < Fintype.card Ω) :
    qdWR t pref v = 0 := by
  have hne : (prefComp t pref).card ≠ 0 :=
    Nat.ne_of_gt (prefComp_nonempty t pref hN)
  unfold qdWR
  rw [if_neg hne]
  have hnmem : ¬ (v ∈ prefComp t pref) := fun hmem =>
    (Finset.mem_sdiff.mp hmem).2 hv
  rw [if_neg hnmem]

/-- Плотность не-инъективной (с повторами) траектории равна нулю:
первый повтор даёт нулевой условный вес. -/
theorem densD_zero_of_noninj : ∀ (n : ℕ), n < Fintype.card Ω →
    ∀ w : Fin n → Ω, ¬ Function.Injective w → densD qdWR w = 0 := by
  intro n
  induction n with
  | zero => intro _ w hw; exact absurd (Function.injective_of_subsingleton w) hw
  | succ n ih =>
      intro hn w hw
      have hn' : n < Fintype.card Ω := by omega
      have hw' : Fin.snoc (α := fun _ => Ω) (Fin.init w)
          (w (Fin.last n)) = w := Fin.snoc_init_self (q := w)
      have hstep := densD_snoc (qdWR (Ω := Ω)) (n := n)
        (Fin.init w) (w (Fin.last n))
      rw [hw'] at hstep
      rw [hstep]
      by_cases hinj : Function.Injective (Fin.init w)
      · -- из ¬inj w и inj (init w): повтор обязан задействовать последний
        have hcls : ∀ i : Fin (n + 1),
            (∃ j : Fin n, i = j.castSucc) ∨ i = Fin.last n :=
          fun i => Fin.eq_castSucc_or_eq_last i
        have hin : ∀ j : Fin n, Fin.init w j = w (j.castSucc) :=
          fun j => rfl
        have hmem : w (Fin.last n) ∈ Finset.image (Fin.init w)
            Finset.univ := by
          by_contra hcon
          apply hw
          intro a b hab
          rcases hcls a with ⟨ja, hja⟩ | hla
          · rcases hcls b with ⟨jb, hjb⟩ | hlb
            · have hjj : ja = jb := hinj (by
                rw [hin, hin]
                rw [← hja, ← hjb]
                exact hab)
              rw [hja, hjb, hjj]
            · have hj : Fin.init w ja = w (Fin.last n) := by
                rw [hin, ← hja, ← hlb]
                exact hab
              exact absurd (Finset.mem_image.mpr
                ⟨ja, Finset.mem_univ _, hj⟩) hcon
          · rcases hcls b with ⟨jb, hjb⟩ | hlb
            · have hj : Fin.init w jb = w (Fin.last n) := by
                rw [hin, ← hjb, ← hla]
                exact hab.symm
              exact absurd (Finset.mem_image.mpr
                ⟨jb, Finset.mem_univ _, hj⟩) hcon
            · rw [hla, hlb]
        have hz := qdWR_zero_of_mem_range (Fin.init w) hmem hn'
        rw [hz, mul_zero]
      · rw [ih hn' (Fin.init w) hinj, zero_mul]

/-- Вероятность множества junk-траекторий равна нулю. -/
theorem probD_noninj_eq_zero [Nonempty Ω] {n : ℕ} (hn : n < Fintype.card Ω) :
    probD (qdWR (Ω := Ω))
        (fun w : Fin n → Ω => ¬ Function.Injective w) = 0 := by
  unfold probD expD
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : Function.Injective w
  · simp [hw]
  · rw [densD_zero_of_noninj n hn w hw]
    ring

/-- Union bound для зависимого произведения. -/
theorem probD_union_le [Nonempty Ω] {n : ℕ}
    (P Q : (Fin n → Ω) → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred (fun w => P w ∨ Q w)] :
    probD (qdWR (Ω := Ω)) (fun w : Fin n → Ω => P w ∨ Q w)
      ≤ probD (qdWR (Ω := Ω)) P + probD (qdWR (Ω := Ω)) Q := by
  simp only [probD, expD]
  have key : ∀ w ∈ (Finset.univ : Finset (Fin n → Ω)),
      densD qdWR w * (if P w ∨ Q w then (1 : ℝ) else 0)
        ≤ densD qdWR w * (if P w then (1 : ℝ) else 0)
          + densD qdWR w * (if Q w then (1 : ℝ) else 0) := by
    intro w _
    have hd0 : 0 ≤ densD qdWR w := densD_nonneg qdWR wrIsProbSysD w
    by_cases hP : P w
    · by_cases hQ : Q w <;> simp [hP, hQ, hd0] <;> norm_num
    · by_cases hQ : Q w <;> simp [hP, hQ, hd0] <;> norm_num
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum key


/-! ## Мартингал Дуба целевой статистики -/

/-- Предсказуемый масштаб `c_t = (N−k)/(N−1−t)` (частичный
fpc-кредит: при k ≪ N ≈ 1−k/N). -/
noncomputable def cSc (N k t : ℕ) : ℝ :=
  ((N - k : ℕ) : ℝ) / ((N - 1 - t : ℕ) : ℝ)

/-- Приращения Дуба-мартингала `M_t = Σ_{s<t} f(ω_s) + (k−t)·μ_t`:
`X_{t+1} = c_t·(f(вытянутый) − среднее оставшихся)` — в
точности «a_{σ(t)} − среднее оставшихся» с масштабом c_t. -/
noncomputable def wrX (f : Ω → ℝ) (k : ℕ) (t : ℕ) (w : Fin t → Ω) : ℝ :=
  match t, w with
  | 0, _ => 0
  | t + 1, w =>
      if t < k then
        cSc (Fintype.card Ω) k t * (f (w (Fin.last t)) - muCond f t (Fin.init w))
      else 0

/-- Точная предсказуемая условная дисперсия шага (гипер-формула
шага, возведённая в бюджет). -/
noncomputable def sigWR (f : Ω → ℝ) (k : ℕ) (t : ℕ) (pref : Fin t → Ω) : ℝ :=
  (cSc (Fintype.card Ω) k t) ^ 2
    * ∑ v, qdWR t pref v * (f v - muCond f t pref) ^ 2

theorem cSc_nonneg (N k t : ℕ) (ht : t < k) (hkN : k + 1 ≤ N) :
    0 ≤ cSc N k t ∧ cSc N k t ≤ 1 := by
  have hpos : (0 : ℝ) < ((N - 1 - t : ℕ) : ℝ) := by
    have h3 : (N - 1 - t : ℕ) ≥ 1 := by omega
    exact_mod_cast h3
  have hle : (N - k : ℕ) ≤ (N - 1 - t : ℕ) := by omega
  constructor
  · exact div_nonneg (by positivity) hpos.le
  · exact (div_le_one hpos).mpr (by exact_mod_cast hle)

/-- **(b) Диапазон приращений**: |X_{t+1}| ≤ 1 при t < k ≤ N−1 и
0 ≤ f ≤ 1 (масштаб c_t ≤ 1, центрирование внутри [0,1]). -/
theorem wr_cond_range [Nonempty Ω] {f : Ω → ℝ} (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    {k t : ℕ} (ht : t < k) (hkN : k + 1 ≤ Fintype.card Ω)
    (pref : Fin t → Ω) (v : Ω) :
    |wrX f k (t + 1) (Fin.snoc pref v)| ≤ 1 := by
  have hc := cSc_nonneg (Fintype.card Ω) k t ht hkN
  have hm := muCond_mem hf t pref
  have h1 : wrX f k (t + 1) (Fin.snoc pref v)
      = cSc (Fintype.card Ω) k t * (f v - muCond f t pref) := by
    simp only [wrX, Fin.snoc_last, Fin.init_snoc]
    rw [if_pos ht]
  rw [h1, abs_mul]
  have h2 : |f v - muCond f t pref| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hf v, hm.1, hm.2]
  rw [abs_of_nonneg hc.1]
  have habs : 0 ≤ |f v - muCond f t pref| :=
    abs_nonneg (f v - muCond f t pref)
  have hstep := mul_le_mul_of_nonneg_left (b := |f v - muCond f t pref|)
    (c := (1 : ℝ)) h2 hc.1
  rw [mul_one] at hstep
  linarith

/-- **(b) Условное центрирование приращений машины**:
`Σ_v qd·X_{t+1}(snoc) = 0` — для ЛЮБОГО префикса (t < k). -/
theorem wr_mean_machine [Nonempty Ω] (f : Ω → ℝ) {k t : ℕ}
    (pref : Fin t → Ω) :
    ∑ v, qdWR t pref v
      * wrX f k (t + 1) (Fin.snoc (α := fun _ => Ω) pref v) = 0 := by
  by_cases ht : t < k
  · have h1 : ∀ v, qdWR t pref v
      * wrX f k (t + 1) (Fin.snoc (α := fun _ => Ω) pref v)
      = cSc (Fintype.card Ω) k t * (qdWR t pref v * (f v - muCond f t pref)) := by
      intro v
      simp only [wrX, Fin.snoc_last, Fin.init_snoc]
      rw [if_pos ht]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h1 v), ← Finset.mul_sum,
      wr_cond_mean_zero f t pref, mul_zero]
  · have h1 : ∀ v, qdWR t pref v
      * wrX f k (t + 1) (Fin.snoc (α := fun _ => Ω) pref v) = 0 := by
      intro v
      simp only [wrX, Fin.snoc_last, Fin.init_snoc]
      rw [if_neg ht]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h1 v)]
    exact Finset.sum_const_zero

/-- Предсказуемая дисперсионная граница неотрицательна. -/
theorem sigWR_nonneg (f : Ω → ℝ) (k : ℕ) (t : ℕ) (pref : Fin t → Ω) :
    0 ≤ sigWR f k t pref := by
  refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun v _ => ?_)
  exact mul_nonneg (qdWR_nonneg t pref v) (sq_nonneg _)

/-- **Точная дисперсионная посылка машины**: условная дисперсия
приращения равна `sigWR` по определению. -/
theorem wr_var_machine (f : Ω → ℝ) (k : ℕ) {t : ℕ}
    (pref : Fin t → Ω) :
    ∑ v, qdWR t pref v
      * (wrX f k (t + 1) (Fin.snoc (α := fun _ => Ω) pref v)) ^ 2
      ≤ sigWR f k t pref := by
  by_cases ht : t < k
  · have h1 : ∀ v, qdWR t pref v
      * (wrX f k (t + 1) (Fin.snoc (α := fun _ => Ω) pref v)) ^ 2
      = (cSc (Fintype.card Ω) k t) ^ 2
        * (qdWR t pref v * (f v - muCond f t pref) ^ 2) := by
      intro v
      simp only [wrX, Fin.snoc_last, Fin.init_snoc]
      rw [if_pos ht]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h1 v), ← Finset.mul_sum]
    rfl
  · have h1 : ∀ v, qdWR t pref v
      * (wrX f k (t + 1) (Fin.snoc (α := fun _ => Ω) pref v)) ^ 2 = 0 := by
      intro v
      simp only [wrX, Fin.snoc_last, Fin.init_snoc]
      rw [if_neg ht]
      ring
    rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_const_zero]
    exact sigWR_nonneg f k t pref


/-! ## Тождество Дуба-мартингала на инъективных траекториях -/

theorem muCond_zero [Nonempty Ω] (f : Ω → ℝ) (p : Fin 0 → Ω) :
    muCond f 0 p = wrPopMean f := by
  have hC : prefComp 0 p = Finset.univ := by
    simp [prefComp]
  have hcard : (prefComp 0 p).card ≠ 0 := by
    rw [hC]
    simpa using Fintype.card_ne_zero (α := Ω)
  rw [muCond_eq f 0 p hcard, hC, wrPopMean, ← Finset.card_univ]

/-- Сумма по дополнению диапазона через его карточку. -/
theorem sum_prefComp_eq (f : Ω → ℝ) (t : ℕ) (pref : Fin t → Ω)
    (hC : (prefComp t pref).card ≠ 0) :
    (∑ v ∈ prefComp t pref, f v)
      = ((prefComp t pref).card : ℝ) * muCond f t pref := by
  rw [muCond_eq f t pref hC]
  have hR : ((prefComp t pref).card : ℝ) ≠ 0 := by exact_mod_cast hC
  field_simp


/-- Значения snoc-префикса: новый элемент плюс старые. -/
theorem mem_image_snoc {t : ℕ} (p : Fin t → Ω) (v u : Ω) :
    u ∈ Finset.image (Fin.snoc p v) Finset.univ
      ↔ u = v ∨ u ∈ Finset.image p Finset.univ := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hlast
    · refine Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩)
      rw [← hi, hj, Fin.snoc_castSucc]
    · refine Or.inl ?_
      rw [← hi, hlast, Fin.snoc_last]
  · rintro (rfl | hj)
    · exact Finset.mem_image.mpr ⟨Fin.last t, Finset.mem_univ _, by simp⟩
    · obtain ⟨j, _, hjv⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr ⟨j.castSucc, Finset.mem_univ _, by
        rw [Fin.snoc_castSucc, hjv]⟩

/-- Дополнение snoc-префикса — удаление нового элемента. -/
theorem prefComp_snoc_erase {t : ℕ} (p : Fin t → Ω) (v : Ω) :
    prefComp (t + 1) (Fin.snoc p v) = (prefComp t p).erase v := by
  classical
  apply Finset.ext
  intro u
  simp only [prefComp, Finset.mem_sdiff, Finset.mem_erase,
    Finset.mem_univ, true_and, mem_image_snoc]
  tauto

theorem sum_prefComp_snoc (f : Ω → ℝ) {t : ℕ} (p : Fin t → Ω) {v : Ω}
    (hv : v ∈ prefComp t p) :
    ∑ u ∈ prefComp (t + 1) (Fin.snoc p v), f u
      = (∑ u ∈ prefComp t p, f u) - f v := by
  rw [prefComp_snoc_erase]
  have hins : ∑ u ∈ prefComp t p, f u
      = f v + ∑ u ∈ (prefComp t p).erase v, f u := by
    conv_lhs => rw [← Finset.insert_erase hv]
    rw [Finset.sum_insert (Finset.notMem_erase v (prefComp t p))]
  linarith

theorem card_prefComp_snoc {t : ℕ} (p : Fin t → Ω) {v : Ω}
    (hv : v ∈ prefComp t p) :
    (prefComp (t + 1) (Fin.snoc p v)).card
      = (prefComp t p).card - 1 := by
  rw [prefComp_snoc_erase, Finset.card_erase_of_mem hv]


/-- Дуб-мартингал `M_t = Σ_{s<t} f(ω_s) + (k−t)·μ_t`. -/
noncomputable def wrM (f : Ω → ℝ) (k : ℕ) :
    ∀ (t : ℕ), (Fin t → Ω) → ℝ :=
  fun t p => (∑ s, f (p s)) + ((k : ℝ) - (t : ℝ)) * muCond f t p

/-- Шаговая лемма: на инъективном префиксе приращение Дуба
`M_{t+1}(snoc) − M_t` равно машинному приращению
`c_t·(f v − μ_t)` — «a_{σ(t)} − среднее оставшихся» с масштабом. -/
theorem wrM_step (f : Ω → ℝ) {k t : ℕ} (htk : t < k)
    (hkN : k + 1 ≤ Fintype.card Ω)
    (p : Fin t → Ω) (hinj : Function.Injective p) {v : Ω}
    (hv : v ∈ prefComp t p) :
    wrM f k (t + 1) (Fin.snoc p v) - wrM f k t p
      = wrX f k (t + 1) (Fin.snoc p v) := by
  set N := Fintype.card Ω with hN
  -- карточки и суммы дополнений
  have hcard : (prefComp t p).card = N - t := by
    have h3 := Finset.card_sdiff_add_card_eq_card
      (s := Finset.image p Finset.univ) (t := (Finset.univ : Finset Ω))
      (Finset.subset_univ _)
    have h1 : (Finset.image p Finset.univ).card = t := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have h4 : (Finset.univ : Finset Ω).card = N := Finset.card_univ
    have h5 : (prefComp t p).card + (Finset.image p Finset.univ).card
      = (Finset.univ : Finset Ω).card := h3
    omega
  have hcard1 : (prefComp t p).card ≠ 0 := by omega
  have hcard' : (prefComp (t + 1) (Fin.snoc p v)).card = N - t - 1 := by
    rw [card_prefComp_snoc p hv, hcard]
  have hcard1' : (prefComp (t + 1) (Fin.snoc p v)).card ≠ 0 := by
    have : (prefComp (t + 1) (Fin.snoc p v)).card + 1 = (prefComp t p).card := by
      rw [card_prefComp_snoc p hv]; omega
    omega
  -- средние через суммы
  have hsum : ∑ u ∈ prefComp t p, f u
      = ((prefComp t p).card : ℝ) * muCond f t p :=
    sum_prefComp_eq f t p hcard1
  have hsum' : ∑ u ∈ prefComp (t + 1) (Fin.snoc p v), f u
      = ((prefComp (t + 1) (Fin.snoc p v)).card : ℝ)
        * muCond f (t + 1) (Fin.snoc p v) :=
    sum_prefComp_eq f (t + 1) (Fin.snoc p v) hcard1'
  have hsum2 : ∑ u ∈ prefComp (t + 1) (Fin.snoc p v), f u
      = (∑ u ∈ prefComp t p, f u) - f v :=
    sum_prefComp_snoc f p hv
  -- числовые positivity
  have hm2 : (2 : ℝ) ≤ ((prefComp t p).card : ℝ) := by
    have : 2 ≤ (prefComp t p).card := by omega
    exact_mod_cast this
  have hmpos : (0 : ℝ) < ((prefComp t p).card : ℝ) := by
    have : 1 ≤ (prefComp t p).card := by omega
    exact_mod_cast this
  -- снoc-разложение wrM
  have hsnoc : (Fin.snoc (α := fun _ => Ω) p v) (Fin.last t) = v := by
    simp
  have hinit : Fin.init (Fin.snoc (α := fun _ => Ω) p v) = p := by
    simp
  -- сумма f по snoc = сумма по p + f v
  have hfsnoc : ∑ s, f ((Fin.snoc (α := fun _ => Ω) p v) s)
      = (∑ s, f (p s)) + f v := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  -- muCond-зависимость: μ' = (m·μ − f v)/(m−1), m = card C
  have hme : ((prefComp t p).card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ ((prefComp t p).card : ℝ) := hm2
    linarith
  have hmu' : muCond f (t + 1) (Fin.snoc p v)
      = (((prefComp t p).card : ℝ) * muCond f t p - f v)
        / (((prefComp t p).card : ℝ) - 1) := by
    have hcn : (prefComp (t + 1) (Fin.snoc p v)).card + 1
        = (prefComp t p).card := by
      have := card_prefComp_snoc p hv
      omega
    have hR : ((prefComp (t + 1) (Fin.snoc p v)).card : ℝ) + 1
        = ((prefComp t p).card : ℝ) := by exact_mod_cast hcn
    have e1 : (((prefComp t p).card : ℝ) - 1)
        * muCond f (t + 1) (Fin.snoc p v)
        = ∑ u ∈ prefComp (t + 1) (Fin.snoc p v), f u := by
      rw [← hR]
      have hx : (((prefComp (t + 1) (Fin.snoc p v)).card : ℝ)) + 1 - 1
          = ((prefComp (t + 1) (Fin.snoc p v)).card : ℝ) := by ring
      rw [hx]
      exact hsum'.symm
    have e2 : ∑ u ∈ prefComp (t + 1) (Fin.snoc p v), f u
        = ((prefComp t p).card : ℝ) * muCond f t p - f v := by
      rw [hsum2, hsum]
    rw [eq_div_iff hme, mul_comm]
    exact e1.trans e2
  -- алгебра приращения: чистая ℝ-цель
  have hc1n : (N - 1 - t : ℕ) = (prefComp t p).card - 1 := by omega
  have hn2n : (N - k : ℕ) = (prefComp t p).card - (k - t) := by omega
  have hkt : t ≤ k := htk.le
  have hR1 : ((N - 1 - t : ℕ) : ℝ)
      = ((prefComp t p).card : ℝ) - 1 := by
    rw [hc1n, Nat.cast_sub (show 1 ≤ (prefComp t p).card by omega),
      Nat.cast_one]
  have hR2 : ((N - k : ℕ) : ℝ)
      = ((prefComp t p).card : ℝ) - ((k - t : ℕ) : ℝ) := by
    rw [hn2n, Nat.cast_sub (show k - t ≤ (prefComp t p).card by omega)]
  have hR3 : ((k - t : ℕ) : ℝ) = ((k : ℝ) - (t : ℝ)) := by
    rw [Nat.cast_sub hkt]
  have hcSc' : cSc N k t
      = (((prefComp t p).card : ℝ) - ((k : ℝ) - (t : ℝ)))
        / (((prefComp t p).card : ℝ) - 1) := by
    rw [cSc, hR1, hR2, hR3]
  rw [wrM, wrM, hfsnoc, hmu', wrX, if_pos htk]
  simp only [hsnoc, hinit]
  rw [hcSc']
  have hα1 : ((k : ℝ) - (((t + 1 : ℕ) : ℕ) : ℝ))
      = ((k : ℝ) - (t : ℝ)) - 1 := by
    push_cast
    ring
  rw [hα1]
  field_simp
  ring


/-- **Тождество Дуба**: на инъективной траектории суммы приращений
машины равны в точности отклонению holdout-суммы от k·μ. -/
theorem wr_azuma_identity [Nonempty Ω] (f : Ω → ℝ) {k : ℕ}
    (hkN : k + 1 ≤ Fintype.card Ω)
    (ω : Fin k → Ω) (hinj : Function.Injective ω) :
    azumaSum (wrX f k) k ω
      = (∑ s, f (ω s)) - (k : ℝ) * wrPopMean f := by
  have hind : ∀ (n : ℕ), n ≤ k → ∀ p : Fin n → Ω, Function.Injective p →
      azumaSum (wrX f k) n p = wrM f k n p - (k : ℝ) * wrPopMean f := by
    intro n
    induction n with
    | zero =>
        intro _ p _
        show (0 : ℝ) = wrM f k 0 p - (k : ℝ) * wrPopMean f
        rw [wrM, muCond_zero f p]
        simp
    | succ n ih =>
        intro hnle p hinjp
        have hnlt : n < k := by omega
        have hinitinj : Function.Injective (Fin.init p) := by
          intro a b hab
          simpa using hinjp hab
        have hmem : p (Fin.last n) ∈ prefComp n (Fin.init p) := by
          rw [prefComp, Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hcon
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hcon
          exact Fin.castSucc_ne_last j
            (hinjp (show p j.castSucc = p (Fin.last n) from hj))
        have hstep := wrM_step f hnlt hkN (Fin.init p) hinitinj
          (v := p (Fin.last n)) hmem
        have hw' : Fin.snoc (α := fun _ => Ω) (Fin.init p)
            (p (Fin.last n)) = p := Fin.snoc_init_self (q := p)
        rw [hw'] at hstep
        have haz : azumaSum (wrX f k) (n + 1) p
            = azumaSum (wrX f k) n (Fin.init p) + wrX f k (n + 1) p := rfl
        rw [haz, ih (by omega) (Fin.init p) hinitinj, ← hstep]
        ring
  have hfin := hind k (le_refl k) ω hinj
  rw [hfin, wrM]
  simp


/-! ## Дисперсионный бюджет -/


/-- Среднее минимизирует сумму квадратов (на дополнении). -/
theorem ss_min_mean (f : Ω → ℝ) (t : ℕ) (pref : Fin t → Ω)
    (hC : (prefComp t pref).card ≠ 0) (c : ℝ) :
    ∑ u ∈ prefComp t pref, (f u - muCond f t pref) ^ 2
      ≤ ∑ u ∈ prefComp t pref, (f u - c) ^ 2 := by
  have hm : ((prefComp t pref).card : ℝ) ≠ 0 := by exact_mod_cast hC
  have hsum : ∑ u ∈ prefComp t pref, f u
      = ((prefComp t pref).card : ℝ) * muCond f t pref :=
    sum_prefComp_eq f t pref hC
  -- линейная часть исчезает
  have hlin : ∑ u ∈ prefComp t pref, (f u - muCond f t pref) = 0 := by
    have h2 : ∑ u ∈ prefComp t pref, (f u - muCond f t pref)
        = ∑ u ∈ prefComp t pref, f u
          - ((prefComp t pref).card : ℝ) * muCond f t pref := by
      rw [Finset.sum_sub_distrib]
      rw [show ∑ u ∈ prefComp t pref, muCond f t pref
        = ((prefComp t pref).card : ℝ) * muCond f t pref from by
        rw [Finset.sum_const, nsmul_eq_mul]]
    rw [h2, hsum]
    ring
  -- разложение: SS(c) = SS(μ) + m·(μ−c)²
  have hpt : ∀ u ∈ prefComp t pref,
      (f u - c) ^ 2
        = (f u - muCond f t pref) ^ 2
          + 2 * (f u - muCond f t pref) * (muCond f t pref - c)
          + (muCond f t pref - c) ^ 2 := fun u _ => by ring
  have hlin2 : ∑ u ∈ prefComp t pref,
      2 * (f u - muCond f t pref) * (muCond f t pref - c) = 0 := by
    have h1 : ∑ u ∈ prefComp t pref,
        2 * (f u - muCond f t pref) * (muCond f t pref - c)
        = 2 * (muCond f t pref - c)
          * ∑ u ∈ prefComp t pref, (f u - muCond f t pref) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [h1, hlin, mul_zero]
  have hcnt : ∑ u ∈ prefComp t pref, (muCond f t pref - c) ^ 2
      = ((prefComp t pref).card : ℝ) * (muCond f t pref - c) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit : ∑ u ∈ prefComp t pref, (f u - c) ^ 2
      = ∑ u ∈ prefComp t pref, (f u - muCond f t pref) ^ 2
        + ((prefComp t pref).card : ℝ) * (muCond f t pref - c) ^ 2 := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hlin2, hcnt]
    ring
  rw [hsplit]
  nlinarith [sq_nonneg (muCond f t pref - c)]

/-- SS_C ≤ SS_pop: дисперсия подмножества ≤ дисперсии популяции. -/
theorem ss_le_pop (f : Ω → ℝ) (t : ℕ) (pref : Fin t → Ω) :
    ∑ u ∈ prefComp t pref, (f u - muCond f t pref) ^ 2
      ≤ ∑ u, (f u - wrPopMean f) ^ 2 := by
  have hC : (prefComp t pref).card ≠ 0 ∨ (prefComp t pref).card = 0 := by omega
  rcases hC with hC | hC
  · have h1 := ss_min_mean f t pref hC (wrPopMean f)
    have h2 : ∑ u ∈ prefComp t pref, (f u - wrPopMean f) ^ 2
        ≤ ∑ u, (f u - wrPopMean f) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun u => sq_nonneg _)
    exact h1.trans h2
  · have hempty : prefComp t pref = ∅ := Finset.card_eq_zero.mp hC
    rw [hempty, Finset.sum_empty]
    exact Finset.sum_nonneg fun u _ => sq_nonneg _


/-! ## varComp-бюджет и телескоп -/

/-- Слагаемое бюджета: c_t²·SS_C/|C| ≤ c_t²·Nσ̂²/(N−t)
(SS_C ≤ SS_pop, |C| ≥ N−t). -/
theorem sigWR_le (f : Ω → ℝ) (k : ℕ) {t : ℕ} [Nonempty Ω]
    (htk : t < k) (hkN : k + 1 ≤ Fintype.card Ω) (pref : Fin t → Ω) :
    sigWR f k t pref
      ≤ (cSc (Fintype.card Ω) k t) ^ 2
        * ((Fintype.card Ω : ℝ) * wrPopVar f) / ((Fintype.card Ω : ℝ)
          - (t : ℝ)) := by
  have hCne : (prefComp t pref).card ≠ 0 := by
    have := prefComp_nonempty t pref (by omega)
    omega
  have hvar := wr_cond_var f t pref hCne
  have hss := ss_le_pop f t pref
  have hcard : (Fintype.card Ω : ℝ) - (t : ℝ)
      ≤ ((prefComp t pref).card : ℝ) := by
    have h1 : (Finset.image pref Finset.univ).card ≤ t := by
      have h2 := Finset.card_image_le
        (f := pref) (s := (Finset.univ : Finset (Fin t)))
      rwa [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : (prefComp t pref).card + (Finset.image pref Finset.univ).card
      = (Finset.univ : Finset Ω).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
    have h4 : (Finset.univ : Finset Ω).card = Fintype.card Ω := Finset.card_univ
    have h5 : ((prefComp t pref).card : ℝ)
        + ((Finset.image pref Finset.univ).card : ℝ)
      = (Fintype.card Ω : ℝ) := by exact_mod_cast (h3.trans h4)
    have h6 : ((Finset.image pref Finset.univ).card : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast h1
    linarith
  have hpop : (∑ u, (f u - wrPopMean f) ^ 2)
      = (Fintype.card Ω : ℝ) * wrPopVar f := by
    rw [wrPopVar]
    have hN : ((Fintype.card Ω : ℝ)) ≠ 0 := by
      simpa using Fintype.card_ne_zero (α := Ω)
    field_simp
  have hcardpos : (0 : ℝ) < ((prefComp t pref).card : ℝ) := by
    have h1 : 0 < (prefComp t pref).card :=
      Nat.pos_of_ne_zero hCne
    exact_mod_cast h1
  have hpos : (0 : ℝ) < ((Fintype.card Ω : ℝ) - (t : ℝ)) := by
    have htN : t + 1 ≤ Fintype.card Ω := by omega
    have h7 : ((t + 1 : ℕ) : ℝ) ≤ (Fintype.card Ω : ℝ) := by
      exact_mod_cast htN
    have h8 : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
    rw [h8] at h7
    linarith
  have hSSpos : (0 : ℝ) ≤ (∑ u ∈ prefComp t pref, (f u - muCond f t pref) ^ 2) :=
    Finset.sum_nonneg fun u _ => sq_nonneg _
  have hkey : ((∑ u ∈ prefComp t pref, (f u - muCond f t pref) ^ 2)
      / ((prefComp t pref).card : ℝ))
      ≤ ((Fintype.card Ω : ℝ) * wrPopVar f)
        / ((Fintype.card Ω : ℝ) - (t : ℝ)) := by
    rw [div_le_iff₀ hcardpos, div_mul_eq_mul_div, le_div_iff₀ hpos]
    have hvarpos : (0 : ℝ) ≤ (Fintype.card Ω : ℝ) * wrPopVar f := by
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      rw [wrPopVar]
      exact div_nonneg
        (Finset.sum_nonneg fun u _ => sq_nonneg (f u - wrPopMean f))
        (Nat.cast_nonneg _)
    exact mul_le_mul (hss.trans_eq hpop) hcard hpos.le hvarpos
  rw [sigWR, hvar, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hkey (sq_nonneg (cSc (Fintype.card Ω) k t))


/-! ## Дисперсионный бюджет: телескоп -/

/-- Дисперсия популяции неотрицательна. -/
theorem wrPopVar_nonneg (f : Ω → ℝ) : 0 ≤ wrPopVar f := by
  rw [wrPopVar]
  exact div_nonneg (Finset.sum_nonneg fun u _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- varComp-бюджет: сумма предсказуемых границ шага по любой
траектории длины `n ≤ k` мажорируется почленной суммой. -/
theorem varComp_le_sum [Nonempty Ω] (f : Ω → ℝ) (k : ℕ)
    (hkN : k + 1 ≤ Fintype.card Ω) :
    ∀ n : ℕ, n ≤ k → ∀ ω : Fin n → Ω,
      varComp (sigWR f k) (n := n) ω
        ≤ ∑ t ∈ Finset.range n, (cSc (Fintype.card Ω) k t) ^ 2
            * ((Fintype.card Ω : ℝ) * wrPopVar f)
              / ((Fintype.card Ω : ℝ) - (t : ℝ)) := by
  intro n
  induction n with
  | zero => intro _ _; exact le_refl _
  | succ n ih =>
      intro hnle ω
      have hnlt : n < k := by omega
      have hrw : varComp (sigWR f k) (n := n + 1) ω
          = varComp (sigWR f k) (n := n) (fun i => ω i.castSucc)
            + sigWR f k n (fun i => ω i.castSucc) := rfl
      rw [hrw, Finset.sum_range_succ]
      have h1 := sigWR_le f k hnlt hkN (fun i => ω i.castSucc)
      have h2 := ih (by omega) (fun i => ω i.castSucc)
      linarith

/-- Чистая ℝ-посылка телескопа: `A²σ/(B²S) ≤ σA²(1/B² − 1/S²)`
при `1 ≤ B`, `S = B + 1` (тогда `S ≤ S² − B² = S + B`). -/
theorem term_le_pair (A σ B S : ℝ) (hB : 1 ≤ B) (hS : B + 1 = S)
    (hσ : 0 ≤ σ) :
    A ^ 2 * σ / (B ^ 2 * S)
      ≤ σ * A ^ 2 * ((B : ℝ) ^ 2)⁻¹ - σ * A ^ 2 * ((S : ℝ) ^ 2)⁻¹ := by
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB
  have hS0 : (0 : ℝ) < S := by linarith
  have hc : (0 : ℝ) ≤ σ * A ^ 2 := mul_nonneg hσ (sq_nonneg A)
  have h1 : S - B = 1 := by linarith
  have h2 : S ^ 2 - B ^ 2 = S + B := by nlinarith
  field_simp
  nlinarith [h1, mul_nonneg hc (by linarith : (0:ℝ) ≤ S + B)]


/-- Телескопная сумма бюджета: Σ_{t<k} c_t²·Nσ̂²/(N−t) ≤ σ̂²·k·(2N−k)/N
(почленно `1/(s(s−1)²) ≤ 1/(s−1)² − 1/s²`, затем телескоп по
`g t = 1/(N−t)²`). -/
theorem telescope_budget [Nonempty Ω] (f : Ω → ℝ) (k : ℕ) (hk : 0 < k)
    (hkN : k + 1 ≤ Fintype.card Ω) :
    ∑ t ∈ Finset.range k, (cSc (Fintype.card Ω) k t) ^ 2
        * ((Fintype.card Ω : ℝ) * wrPopVar f)
          / ((Fintype.card Ω : ℝ) - (t : ℝ))
      ≤ wrPopVar f * (k : ℝ) * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
        / (Fintype.card Ω : ℝ) := by
  classical
  -- почленная пара: слагаемое бюджета ≤ A²σ'·B²⁻¹ − A²σ'·S²⁻¹
  have hpair : ∀ t ∈ Finset.range k,
      (cSc (Fintype.card Ω) k t) ^ 2
        * ((Fintype.card Ω : ℝ) * wrPopVar f)
          / ((Fintype.card Ω : ℝ) - (t : ℝ))
        ≤ ((Fintype.card Ω : ℝ) * wrPopVar f)
            * ((Fintype.card Ω - k : ℕ) : ℝ) ^ 2
            * ((((Fintype.card Ω - 1 - t : ℕ) : ℝ) ^ 2)⁻¹
              - (((Fintype.card Ω - t : ℕ) : ℝ) ^ 2)⁻¹) := by
    intro t ht
    have htk : t < k := Finset.mem_range.mp ht
    have htN : t ≤ Fintype.card Ω := by omega
    have hB1 : 1 ≤ (Fintype.card Ω - 1 - t : ℕ) := by omega
    have hsn : (Fintype.card Ω - 1 - t : ℕ) + 1 = Fintype.card Ω - t := by omega
    have hsub : ((Fintype.card Ω - 1 - t : ℕ) : ℝ) + 1
        = ((Fintype.card Ω - t : ℕ) : ℝ) := by
      have e : (Fintype.card Ω - 1 - t : ℕ) + 1 = Fintype.card Ω - t := by omega
      have e2 : (((Fintype.card Ω - 1 - t : ℕ) + 1 : ℕ) : ℝ)
          = ((Fintype.card Ω - t : ℕ) : ℝ) := by rw [e]
      push_cast at e2
      linarith
    have hB0 : (1 : ℝ) ≤ ((Fintype.card Ω - 1 - t : ℕ) : ℝ) := by
      exact_mod_cast hB1
    have hterm := term_le_pair ((Fintype.card Ω - k : ℕ) : ℝ)
      ((Fintype.card Ω : ℝ) * wrPopVar f)
      ((Fintype.card Ω - 1 - t : ℕ) : ℝ) ((Fintype.card Ω - t : ℕ) : ℝ)
      hB0 hsub (mul_nonneg (Nat.cast_nonneg _) (wrPopVar_nonneg f))
    have hc2 : ((Fintype.card Ω : ℝ) - (t : ℝ))
        = ((Fintype.card Ω - t : ℕ) : ℝ) := by
      rw [Nat.cast_sub htN]
    have hc3 : cSc (Fintype.card Ω) k t
        = (((Fintype.card Ω - k : ℕ) : ℝ)
          / ((Fintype.card Ω - 1 - t : ℕ) : ℝ)) := rfl
    rw [hc2, hc3, div_pow, div_mul_eq_mul_div, div_div]
    linarith [hterm]
  -- телескоп: сумма парных разностей = C·(g k − g 0)
  have hsumtelesc :
      ∑ t ∈ Finset.range k,
        (((Fintype.card Ω : ℝ) * wrPopVar f)
          * ((Fintype.card Ω - k : ℕ) : ℝ) ^ 2
          * ((((Fintype.card Ω - 1 - t : ℕ) : ℝ) ^ 2)⁻¹
            - (((Fintype.card Ω - t : ℕ) : ℝ) ^ 2)⁻¹))
      = ((Fintype.card Ω : ℝ) * wrPopVar f)
          * ((Fintype.card Ω - k : ℕ) : ℝ) ^ 2
          * ((((Fintype.card Ω - k : ℕ) : ℝ)⁻¹ ^ 2)
            - (((Fintype.card Ω : ℝ))⁻¹ ^ 2)) := by
    have h1 : ∀ t ∈ Finset.range k,
        (((Fintype.card Ω - 1 - t : ℕ) : ℝ) ^ 2)⁻¹
          - (((Fintype.card Ω - t : ℕ) : ℝ) ^ 2)⁻¹
        = ((fun t => (((Fintype.card Ω - t : ℕ) : ℝ))⁻¹ ^ 2) (t + 1)
          - (fun t => (((Fintype.card Ω - t : ℕ) : ℝ))⁻¹ ^ 2) t) := by
      intro t ht
      have hn : (Fintype.card Ω - (t + 1) : ℕ) = Fintype.card Ω - 1 - t := by omega
      simp only [hn, inv_pow]
    have h2 : ∀ t ∈ Finset.range k,
        ((Fintype.card Ω : ℝ) * wrPopVar f) * ((Fintype.card Ω - k : ℕ) : ℝ) ^ 2
          * ((((Fintype.card Ω - 1 - t : ℕ) : ℝ) ^ 2)⁻¹
            - (((Fintype.card Ω - t : ℕ) : ℝ) ^ 2)⁻¹)
        = ((Fintype.card Ω : ℝ) * wrPopVar f) * ((Fintype.card Ω - k : ℕ) : ℝ) ^ 2
          * (((fun t => (((Fintype.card Ω - t : ℕ) : ℝ))⁻¹ ^ 2) (t + 1)
            - (fun t => (((Fintype.card Ω - t : ℕ) : ℝ))⁻¹ ^ 2) t) : ℝ) := by
      intro t ht
      rw [h1 t ht]
    rw [Finset.sum_congr rfl (fun t ht => h2 t ht)]
    simp only []
    rw [← Finset.mul_sum]
    have hte := Finset.sum_range_sub
      (fun t => (((Fintype.card Ω - t : ℕ) : ℝ))⁻¹ ^ 2) k
    simp only [Nat.sub_zero] at hte
    rw [← hte]
  -- замыкающая алгебра: C·(1/(N−k)² − 1/N²) = σ̂·k·(2N−k)/N
  have hA0 : ((Fintype.card Ω - k : ℕ) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card Ω - k := by omega
    exact_mod_cast Nat.ne_of_gt this
  have hAc : ((Fintype.card Ω - k : ℕ) : ℝ)
      = (Fintype.card Ω : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ Fintype.card Ω)]
  have h2c : ((2 * Fintype.card Ω - k : ℕ) : ℝ)
      = 2 * (Fintype.card Ω : ℝ) - (k : ℝ) := by
    have h : (2 * Fintype.card Ω - k : ℕ)
        = Fintype.card Ω + (Fintype.card Ω - k) := by omega
    rw [h, Nat.cast_add, Nat.cast_sub (by omega : k ≤ Fintype.card Ω)]
    push_cast
    ring
  have hfinal : ((Fintype.card Ω : ℝ) * wrPopVar f)
      * ((Fintype.card Ω - k : ℕ) : ℝ) ^ 2
      * ((((Fintype.card Ω - k : ℕ) : ℝ)⁻¹ ^ 2)
        - (((Fintype.card Ω : ℝ))⁻¹ ^ 2))
      = wrPopVar f * (k : ℝ) * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
        / (Fintype.card Ω : ℝ) := by
    have hkN2 : (k : ℝ) ≠ (Fintype.card Ω : ℝ) := by
      exact_mod_cast (ne_of_lt (by omega : k < Fintype.card Ω))
    rw [hAc, h2c, inv_pow, inv_pow]
    field_simp
    ring
  calc ∑ t ∈ Finset.range k, (cSc (Fintype.card Ω) k t) ^ 2
        * ((Fintype.card Ω : ℝ) * wrPopVar f)
          / ((Fintype.card Ω : ℝ) - (t : ℝ))
      ≤ ∑ t ∈ Finset.range k,
          ((Fintype.card Ω : ℝ) * wrPopVar f)
            * ((Fintype.card Ω - k : ℕ) : ℝ) ^ 2
            * ((((Fintype.card Ω - 1 - t : ℕ) : ℝ) ^ 2)⁻¹
              - (((Fintype.card Ω - t : ℕ) : ℝ) ^ 2)⁻¹) :=
        Finset.sum_le_sum hpair
    _ = wrPopVar f * (k : ℝ) * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) := by
          rw [hsumtelesc, hfinal]

/-- Полный потраекторный дисперсионный бюджет машины. -/
theorem varComp_le_total [Nonempty Ω] (f : Ω → ℝ) (k : ℕ) (hk : 0 < k)
    (hkN : k + 1 ≤ Fintype.card Ω) (ω : Fin k → Ω) :
    varComp (sigWR f k) (n := k) ω
      ≤ wrPopVar f * (k : ℝ) * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
        / (Fintype.card Ω : ℝ) :=
  (varComp_le_sum f k hkN k (le_refl k) ω).trans (telescope_budget f k hk hkN)

/-! ## Главный результат: концентрация holdout без возвращения -/

/-- Диапазон приращений при любом индексе (посылка hbnd машины):
`|wrX t pref| ≤ 1` — при `t < k` шаговое приращение (масштаб
`c_t ≤ 1`, центрирование в [0,1]), иначе 0. -/
theorem wrX_le_one [Nonempty Ω] (f : Ω → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    {k : ℕ} (hkN : k + 1 ≤ Fintype.card Ω) :
    ∀ (t : ℕ) (pref : Fin t → Ω), |wrX f k t pref| ≤ 1 := by
  intro t pref
  match t, pref with
  | 0, _ => simp [wrX]
  | t + 1, p =>
      by_cases ht : t < k
      · have h1 : wrX f k (t + 1) p
            = wrX f k (t + 1)
              (Fin.snoc (α := fun _ => Ω) (Fin.init p) (p (Fin.last t))) := by
          rw [Fin.snoc_init_self]
        rw [h1]
        exact wr_cond_range hf ht hkN (Fin.init p) (p (Fin.last t))
      · simp only [wrX, if_neg ht]
        norm_num

/-- Тождество «оценка − μ = мартингальная сумма / k» на
инъективных траекториях. -/
theorem wrMean_sub_eq [Nonempty Ω] (f : Ω → ℝ) {k : ℕ} (hk : 0 < k)
    (hkN : k + 1 ≤ Fintype.card Ω) (ω : Fin k → Ω)
    (hinj : Function.Injective ω) :
    wrMean f ω - wrPopMean f = azumaSum (wrX f k) k ω / (k : ℝ) := by
  have hid := wr_azuma_identity f hkN ω hinj
  rw [wrMean, hid]
  field_simp

/-- Нижнее отклонение оценки влечёт нижнее отклонение суммы. -/
theorem wrMean_dev_lower [Nonempty Ω] (f : Ω → ℝ) {k : ℕ} (hk : 0 < k)
    (hkN : k + 1 ≤ Fintype.card Ω) (ω : Fin k → Ω)
    (hinj : Function.Injective ω) (r : ℝ)
    (hr : wrMean f ω - wrPopMean f ≤ -r) :
    azumaSum (wrX f k) k ω ≤ -((k : ℝ) * r) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [wrMean_sub_eq f hk hkN ω hinj] at hr
  rw [div_le_iff₀ hk0] at hr
  linarith

/-- Верхнее отклонение оценки влечёт верхнее отклонение суммы. -/
theorem wrMean_dev_upper [Nonempty Ω] (f : Ω → ℝ) {k : ℕ} (hk : 0 < k)
    (hkN : k + 1 ≤ Fintype.card Ω) (ω : Fin k → Ω)
    (hinj : Function.Injective ω) (r : ℝ)
    (hr : r ≤ wrMean f ω - wrPopMean f) :
    (k : ℝ) * r ≤ azumaSum (wrX f k) k ω := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [wrMean_sub_eq f hk hkN ω hinj] at hr
  rw [le_div_iff₀ hk0] at hr
  rw [mul_comm] at hr
  exact hr

set_option maxHeartbeats 1000000 in
/-- Нижний хвост через машину Freedman (C438): junk-траектории
отрезаются нулевой плотностью, на инъективных — тождество Дуба. -/
theorem holdout_wr_lower [Nonempty Ω] {f : Ω → ℝ} (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    {k : ℕ} (hk : 0 < k) (hkN : k + 1 ≤ Fintype.card Ω)
    (hσ : 0 < wrPopVar f) (ε : ℝ) (hε : 0 < ε) :
    probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => wrMean f ω - wrPopMean f ≤ -ε)
      ≤ Real.exp (- (k : ℝ) * ε ^ 2
        / (2 * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) + ε))) := by
  classical
  have hNpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    have h0 : 0 < Fintype.card Ω :=
      Nat.pos_of_ne_zero (Fintype.card_ne_zero)
    exact_mod_cast h0
  have h2k : (0 : ℝ) < ((2 * Fintype.card Ω - k : ℕ) : ℝ) := by
    have : 0 < 2 * Fintype.card Ω - k := by omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hVpos : (0 : ℝ) < wrPopVar f * (k : ℝ)
      * ((2 * Fintype.card Ω - k : ℕ) : ℝ) / (Fintype.card Ω : ℝ) :=
    div_pos (mul_pos (mul_pos hσ hk0) h2k) hNpos
  have hmono := probD_mono (qdWR (Ω := Ω)) wrIsProbSysD
    (fun ω => wrMean f ω - wrPopMean f ≤ -ε)
    (fun ω => azumaSum (wrX f k) k ω ≤ -((k : ℝ) * ε)
      ∨ ¬ Function.Injective ω)
    (fun ω hω => by
      by_cases hinj : Function.Injective ω
      · exact Or.inl (wrMean_dev_lower f hk hkN ω hinj ε hω)
      · exact Or.inr hinj)
  have hjunk : probD (qdWR (Ω := Ω))
      (fun ω : Fin k → Ω => ¬ Function.Injective ω) = 0 :=
    probD_noninj_eq_zero (by omega)
  have hmach := freedmanD_tail_low (qdWR (Ω := Ω)) wrIsProbSysD
    (wrX f k) 1 zero_le_one (wrX_le_one f hf hkN)
    (sigWR f k) (sigWR_nonneg f k)
    (fun t pref => wr_mean_machine f pref)
    (fun t pref => wr_var_machine f k pref)
    k _ hVpos (fun ω => varComp_le_total f k hk hkN ω)
    ((k : ℝ) * ε) (mul_pos hk0 hε)
  have hexpEq : -((k : ℝ) * ε) ^ 2
      / (2 * (wrPopVar f * (k : ℝ)
        * ((2 * Fintype.card Ω - k : ℕ) : ℝ) / (Fintype.card Ω : ℝ)
        + 1 * ((k : ℝ) * ε)))
      = -(k : ℝ) * ε ^ 2
        / (2 * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) + ε)) := by
    have hN0 : ((Fintype.card Ω : ℝ)) ≠ 0 := ne_of_gt hNpos
    have e1 : ((k : ℝ) * ε) ^ 2 = (k : ℝ) * ((k : ℝ) * ε ^ 2) := by ring
    have e2 : wrPopVar f * (k : ℝ)
        * ((2 * Fintype.card Ω - k : ℕ) : ℝ) / (Fintype.card Ω : ℝ)
        + 1 * ((k : ℝ) * ε)
        = (k : ℝ) * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) + ε) := by
      rw [one_mul, mul_add, ← mul_div_assoc]
      have hxy : wrPopVar f * (k : ℝ)
          * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          = (k : ℝ) * (wrPopVar f
            * ((2 * Fintype.card Ω - k : ℕ) : ℝ)) := by ring
      rw [hxy]
    rw [e1, e2,
      show 2 * ((k : ℝ) * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
        / (Fintype.card Ω : ℝ) + ε))
        = (k : ℝ) * (2 * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) + ε)) from by ring,
      neg_div, mul_div_mul_left _ _ (ne_of_gt hk0), ← neg_div,
      neg_mul_eq_neg_mul]
  rw [hexpEq] at hmach
  have hu1 := probD_union_le
    (fun ω : Fin k → Ω => azumaSum (wrX f k) k ω ≤ -((k : ℝ) * ε))
    (fun ω : Fin k → Ω => ¬ Function.Injective ω)
  have hu2 : probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => azumaSum (wrX f k) k ω ≤ -((k : ℝ) * ε))
      + probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => ¬ Function.Injective ω)
      = probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => azumaSum (wrX f k) k ω ≤ -((k : ℝ) * ε)) := by
    rw [hjunk, add_zero]
  exact hmono.trans (hu1.trans (by rw [hu2]; exact hmach))

set_option maxHeartbeats 1000000 in
/-- Верхний хвост: машина на отрицательных приращениях. -/
theorem holdout_wr_upper [Nonempty Ω] {f : Ω → ℝ} (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    {k : ℕ} (hk : 0 < k) (hkN : k + 1 ≤ Fintype.card Ω)
    (hσ : 0 < wrPopVar f) (ε : ℝ) (hε : 0 < ε) :
    probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => ε ≤ wrMean f ω - wrPopMean f)
      ≤ Real.exp (- (k : ℝ) * ε ^ 2
        / (2 * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) + ε))) := by
  classical
  have hNpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by
    have h0 : 0 < Fintype.card Ω :=
      Nat.pos_of_ne_zero (Fintype.card_ne_zero)
    exact_mod_cast h0
  have h2k : (0 : ℝ) < ((2 * Fintype.card Ω - k : ℕ) : ℝ) := by
    have : 0 < 2 * Fintype.card Ω - k := by omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hVpos : (0 : ℝ) < wrPopVar f * (k : ℝ)
      * ((2 * Fintype.card Ω - k : ℕ) : ℝ) / (Fintype.card Ω : ℝ) :=
    div_pos (mul_pos (mul_pos hσ hk0) h2k) hNpos
  have hX' : (fun (t : ℕ) (w : Fin t → Ω) => - wrX f k t w)
      = fun (t : ℕ) (w : Fin t → Ω) => - wrX f k t w := rfl
  have hAz : ∀ ω : Fin k → Ω,
      azumaSum (fun (t : ℕ) (w : Fin t → Ω) => - wrX f k t w) k ω
        = - azumaSum (wrX f k) k ω :=
    fun ω => Hagi.Probability.azumaSum_neg (wrX f k) k ω
  have hmono := probD_mono (qdWR (Ω := Ω)) wrIsProbSysD
    (fun ω => ε ≤ wrMean f ω - wrPopMean f)
    (fun ω => azumaSum (fun (t : ℕ) (w : Fin t → Ω) => - wrX f k t w) k ω
        ≤ -((k : ℝ) * ε)
      ∨ ¬ Function.Injective ω)
    (fun ω hω => by
      by_cases hinj : Function.Injective ω
      · refine Or.inl ?_
        rw [hAz ω]
        have h1 := wrMean_dev_upper f hk hkN ω hinj ε hω
        linarith
      · exact Or.inr hinj)
  have hjunk : probD (qdWR (Ω := Ω))
      (fun ω : Fin k → Ω => ¬ Function.Injective ω) = 0 :=
    probD_noninj_eq_zero (by omega)
  have hmach := freedmanD_tail_low (qdWR (Ω := Ω)) wrIsProbSysD
    (fun (t : ℕ) (w : Fin t → Ω) => - wrX f k t w) 1 zero_le_one
    (fun t pref => by rw [abs_neg]; exact wrX_le_one f hf hkN t pref)
    (sigWR f k) (sigWR_nonneg f k)
    (fun t pref => by
      simp only [mul_neg, Finset.sum_neg_distrib]
      rw [wr_mean_machine f pref]
      ring)
    (fun t pref => by
      simp only [neg_sq]
      exact wr_var_machine f k pref)
    k _ hVpos (fun ω => varComp_le_total f k hk hkN ω)
    ((k : ℝ) * ε) (mul_pos hk0 hε)
  have hexpEq : -((k : ℝ) * ε) ^ 2
      / (2 * (wrPopVar f * (k : ℝ)
        * ((2 * Fintype.card Ω - k : ℕ) : ℝ) / (Fintype.card Ω : ℝ)
        + 1 * ((k : ℝ) * ε)))
      = -(k : ℝ) * ε ^ 2
        / (2 * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) + ε)) := by
    have hN0 : ((Fintype.card Ω : ℝ)) ≠ 0 := ne_of_gt hNpos
    have e1 : ((k : ℝ) * ε) ^ 2 = (k : ℝ) * ((k : ℝ) * ε ^ 2) := by ring
    have e2 : wrPopVar f * (k : ℝ)
        * ((2 * Fintype.card Ω - k : ℕ) : ℝ) / (Fintype.card Ω : ℝ)
        + 1 * ((k : ℝ) * ε)
        = (k : ℝ) * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) + ε) := by
      rw [one_mul, mul_add, ← mul_div_assoc]
      have hxy : wrPopVar f * (k : ℝ)
          * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          = (k : ℝ) * (wrPopVar f
            * ((2 * Fintype.card Ω - k : ℕ) : ℝ)) := by ring
      rw [hxy]
    rw [e1, e2,
      show 2 * ((k : ℝ) * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
        / (Fintype.card Ω : ℝ) + ε))
        = (k : ℝ) * (2 * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) + ε)) from by ring,
      neg_div, mul_div_mul_left _ _ (ne_of_gt hk0), ← neg_div,
      neg_mul_eq_neg_mul]
  rw [hexpEq] at hmach
  have hu1 := probD_union_le
    (fun ω : Fin k → Ω => azumaSum
        (fun (t : ℕ) (w : Fin t → Ω) => - wrX f k t w) k ω
        ≤ -((k : ℝ) * ε))
    (fun ω : Fin k → Ω => ¬ Function.Injective ω)
  have hu2 : probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => azumaSum
            (fun (t : ℕ) (w : Fin t → Ω) => - wrX f k t w) k ω
            ≤ -((k : ℝ) * ε))
      + probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => ¬ Function.Injective ω)
      = probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => azumaSum
            (fun (t : ℕ) (w : Fin t → Ω) => - wrX f k t w) k ω
            ≤ -((k : ℝ) * ε)) := by
    rw [hjunk, add_zero]
  exact hmono.trans (hu1.trans (by rw [hu2]; exact hmach))

/-- **(c) Главный результат: без-возвратная holdout-концентрация**
(Freedman-адаптированная форма с частичным fpc-кредитом):
`P[|wrMean − μ| ≥ ε] ≤ 2·exp(−kε²/(2(σ̂²(2N−k)/N + ε)))`.
Посылки: `0 < k`; `k + 1 ≤ N` (при k = N оценка детерминирована —
PIN); `σ̂² > 0` (при σ̂² = 0 f константна, событие пусто — PIN). -/
theorem holdout_wr_concentration [Nonempty Ω] {f : Ω → ℝ}
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    {k : ℕ} (hk : 0 < k) (hkN : k + 1 ≤ Fintype.card Ω)
    (hσ : 0 < wrPopVar f) (ε : ℝ) (hε : 0 < ε) :
    probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => ε ≤ |wrMean f ω - wrPopMean f|)
      ≤ 2 * Real.exp (- (k : ℝ) * ε ^ 2
        / (2 * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
          / (Fintype.card Ω : ℝ) + ε))) := by
  classical
  have hlow := holdout_wr_lower hf hk hkN hσ ε hε
  have hup := holdout_wr_upper hf hk hkN hσ ε hε
  have hmono := probD_mono (qdWR (Ω := Ω)) wrIsProbSysD
    (fun ω : Fin k → Ω => ε ≤ |wrMean f ω - wrPopMean f|)
    (fun ω : Fin k → Ω => wrMean f ω - wrPopMean f ≤ -ε
      ∨ ε ≤ wrMean f ω - wrPopMean f)
    (fun ω hω => by
      by_cases h0 : wrMean f ω - wrPopMean f < 0
      · refine Or.inl ?_
        have habse := abs_of_neg h0
        rw [habse] at hω
        linarith
      · refine Or.inr ?_
        push_neg at h0
        have habse := abs_of_nonneg h0
        rw [habse] at hω
        linarith)
  have hu := probD_union_le
    (fun ω : Fin k → Ω => wrMean f ω - wrPopMean f ≤ -ε)
    (fun ω : Fin k → Ω => ε ≤ wrMean f ω - wrPopMean f)
  linarith [hmono, hu, hlow, hup]

/-- **(d) Сравнение с with-replacement Hoeffding (C435)**: при
проверяемом условии `σ̂²(2N−k)/N + ε ≤ 1/4` без-возвратная граница
не хуже `2·exp(−2kε²)` — variance-adaptivity окупается при малой
дисперсии популяции (bench C484: σ̂² ≈ 0.01 ≪ 1/4). -/
theorem wr_bound_le_with_replacement [Nonempty Ω] {f : Ω → ℝ}
    (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    {k : ℕ} (hk : 0 < k) (hkN : k + 1 ≤ Fintype.card Ω)
    (hσ : 0 < wrPopVar f) (ε : ℝ) (hε : 0 < ε)
    (hcond : wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
        / (Fintype.card Ω : ℝ) + ε ≤ 1 / 4) :
    probD (qdWR (Ω := Ω))
        (fun ω : Fin k → Ω => ε ≤ |wrMean f ω - wrPopMean f|)
      ≤ 2 * Real.exp (-2 * (k : ℝ) * ε ^ 2) := by
  have h1 := holdout_wr_concentration hf hk hkN hσ ε hε
  have hke : (0 : ℝ) < (k : ℝ) * ε ^ 2 :=
    mul_pos (by exact_mod_cast hk) (sq_pos_of_pos hε)
  have hV : (0 : ℝ) ≤ wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
      / (Fintype.card Ω : ℝ) :=
    div_nonneg (mul_nonneg hσ.le (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hpos2 : (0 : ℝ) < 2 * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
      / (Fintype.card Ω : ℝ) + ε) := by positivity
  have hexp : Real.exp (- (k : ℝ) * ε ^ 2
      / (2 * (wrPopVar f * ((2 * Fintype.card Ω - k : ℕ) : ℝ)
        / (Fintype.card Ω : ℝ) + ε)))
      ≤ Real.exp (-2 * (k : ℝ) * ε ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_iff₀ hpos2]
    nlinarith [hcond, hke, hV, hε]
  linarith [h1, hexp]

end Hagi.Theory.HoldoutWithoutReplacement
