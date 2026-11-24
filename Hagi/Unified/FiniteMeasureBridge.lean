/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.Freedman
import Hagi.Unified.AnytimeMartingale

/-!
# Finite-PMF ↔ MeasureTheory bridge

The library spoke in two unconnected probabilistic
languages. Tower 1: finite sums — the `pmfMean` machine
(`Hagi.Probability.FreedmanTwoSided`, Freedman/Azuma-style
concentration over finite PMF laws). Tower 2: measure
theory — `Mathlib.Supermartingale`, Ville inequalities and
e-process budgets (`Hagi.Unified.AnytimeMartingale`,
`Hagi.Contracts.VilleMonitor`). This module is the one-way
glue between them.

Layer note: the module lives in `Hagi/Unified` (layer 6, the
merge layer) because the bridge consumes the Ville engine of
`Hagi.Unified.AnytimeMartingale`; `Hagi/Probability` (layer 2)
may not import upward.

Contents (in bridge order):

* `Hagi.Probability.pmfMean_eq_integral` — the embedding glue:
  a `pmfMean` (finite weighted sum) is exactly the Bochner
  integral against the canonical measure `PMF.toMeasure`
  (via `PMF.integral_eq_sum`).
* `Hagi.Probability.integrable_toMeasure_of_fintype` — every
  real function on a finite type is integrable against a PMF
  measure (boundedness by a finite sum).
* `Hagi.Unified.supermartingale_of_pmfMean_nonincreasing` —
  a process with `pmfMean`-monotone conditional expectations
  (stated as indicator sums over measurable sets, tower-1
  vocabulary) is a `Mathlib.Supermartingale` after embedding.
* `Hagi.Unified.pmfMean_anytime_false_alarm` — the consumed
  bridge: Ville's anytime false-alarm bound of tower 2
  (`ville_anytime_false_alarm`) applied to a pure tower-1
  `pmfMean` process. Concentration facts proved with
  `pmfMean` acquire an anytime-valid form through this gate.

Pins: only finite measures (`PMF` over a `Fintype`);
no densities, no continuous time, no `condExp`-level
conditional-expectation API on the tower-1 side.
-/

open MeasureTheory PMF ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Hagi.Probability

section Glue

variable {α : Type*} [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- Bridge glue: the finite-sum expectation `pmfMean` of tower 1
is the integral against the canonical `PMF.toMeasure` of
tower 2. Specialized transport of `PMF.integral_eq_sum`. -/
theorem pmfMean_eq_integral (p : PMF α) (f : α → ℝ) :
    pmfMean p f = ∫ a, f a ∂(p.toMeasure) := by
  simp only [pmfMean, PMF.integral_eq_sum, smul_eq_mul]

omit [MeasurableSingletonClass α] in
/-- Every real function on a finite type is integrable against a
PMF measure: `‖f‖₊` is dominated by the finite sum
`∑ b, ‖f b‖₊ < ⊤`, and the measure is a probability. -/
theorem integrable_toMeasure_of_fintype (p : PMF α) (f : α → ℝ)
    (hf : Measurable f) : Integrable f p.toMeasure := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hle : ∀ᵐ a ∂p.toMeasure, ‖f a‖₊ ≤ (∑ b, (‖f b‖₊ : ℝ≥0∞)) :=
    ae_of_all _ fun a =>
      Finset.single_le_sum_of_canonicallyOrdered
        (f := fun b => ((‖f b‖₊ : ℝ≥0) : ℝ≥0∞)) (Finset.mem_univ a)
  have h1 : ∫⁻ a, ‖f a‖₊ ∂p.toMeasure
      ≤ (∑ b, (‖f b‖₊ : ℝ≥0∞)) * p.toMeasure Set.univ :=
    calc ∫⁻ a, ‖f a‖₊ ∂p.toMeasure
        ≤ ∫⁻ a, (∑ b, (‖f b‖₊ : ℝ≥0∞)) ∂p.toMeasure := lintegral_mono_ae hle
      _ = (∑ b, (‖f b‖₊ : ℝ≥0∞)) * p.toMeasure Set.univ :=
          lintegral_const _
  refine lt_of_le_of_lt h1 ?_
  rw [measure_univ, mul_one]
  simp

end Glue

end Hagi.Probability

namespace Hagi.Unified

/-! ## Tower-1 processes as tower-2 supermartingales -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω} [Fintype Ω]
  [MeasurableSingletonClass Ω] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- The bridge proper: a process whose *conditional expectations are
pmfMean-monotone* — tower-1 style, expressed as indicator sums over
measurable sets, no `condExp` — is a Mathlib `Supermartingale` after
the embedding `p.toMeasure`. Adaptedness supplies integrability on
the finite type. -/
theorem supermartingale_of_pmfMean_nonincreasing (p : PMF Ω)
    (hadp : StronglyAdapted 𝒢 f)
    (hmono : ∀ i (s : Set Ω), MeasurableSet[𝒢 i] s →
      Hagi.Probability.pmfMean p (fun ω => s.indicator (f (i + 1)) ω) ≤
      Hagi.Probability.pmfMean p (fun ω => s.indicator (f i) ω)) :
    Supermartingale f 𝒢 p.toMeasure := by
  refine supermartingale_of_setIntegral_succ_le hadp ?_ ?_
  · intro i
    exact Hagi.Probability.integrable_toMeasure_of_fintype p (f i)
      ((hadp i).mono (𝒢.le i)).measurable
  · intro i s hs
    have hs0 : @MeasurableSet Ω m0 s := (𝒢.le' i) s hs
    have hA : ∫ ω in s, f (i + 1) ω ∂(p.toMeasure)
        = ∫ ω, s.indicator (f (i + 1)) ω ∂(p.toMeasure) :=
      (integral_indicator hs0).symm
    have hB : ∫ ω in s, f i ω ∂(p.toMeasure)
        = ∫ ω, s.indicator (f i) ω ∂(p.toMeasure) :=
      (integral_indicator hs0).symm
    have hC : ∫ ω, s.indicator (f (i + 1)) ω ∂(p.toMeasure)
        = Hagi.Probability.pmfMean p (fun ω => s.indicator (f (i + 1)) ω) := by
      rw [Hagi.Probability.pmfMean_eq_integral]
    have hD : ∫ ω, s.indicator (f i) ω ∂(p.toMeasure)
        = Hagi.Probability.pmfMean p (fun ω => s.indicator (f i) ω) := by
      rw [Hagi.Probability.pmfMean_eq_integral]
    rw [hA, hB, hC, hD]
    exact hmono i s hs

/-- Consumed bridge: Ville's anytime false-alarm bound (tower 2,
`ville_anytime_false_alarm`) instantiated for a tower-1 `pmfMean`
process. Every hypothesis is a `pmfMean` statement: nonnegativity,
indicator-conditional monotonicity, and the budget
`pmfMean p (f 0) ≤ 1`; the conclusion bounds the crossing
probability of the embedded measure. A `pmfMean`-proved e-process
therefore gets an anytime-valid false-alarm guarantee. -/
theorem pmfMean_anytime_false_alarm (p : PMF Ω) {δ : ℝ} (hδ : 0 < δ)
    (hadp : StronglyAdapted 𝒢 f) (hnn : ∀ i, 0 ≤ f i)
    (hmono : ∀ i (s : Set Ω), MeasurableSet[𝒢 i] s →
      Hagi.Probability.pmfMean p (fun ω => s.indicator (f (i + 1)) ω) ≤
      Hagi.Probability.pmfMean p (fun ω => s.indicator (f i) ω))
    (h0 : Hagi.Probability.pmfMean p (f 0) ≤ 1) (n : ℕ) :
    p.toMeasure.real {ω | ∃ t ∈ Finset.range (n + 1), δ⁻¹ ≤ f t ω} ≤ δ :=
  Hagi.Unified.ville_anytime_false_alarm
    (supermartingale_of_pmfMean_nonincreasing p hadp hmono)
    hnn (by rw [← Hagi.Probability.pmfMean_eq_integral p (f 0)]; exact h0) n hδ

end Hagi.Unified
