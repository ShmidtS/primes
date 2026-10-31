import Mathlib
import Hagi.Unified.AnytimeMartingale

/-!
# Anytime PAC-Bayes (источник №71: направление FormalSLT,
# time-uniform bounds; композиция Catoni × Ville)

Лакуна из обзора конкурирующих проектов (FormalSLT):
time-uniform (anytime) гарантии — контроль ошибки при
АДАПТИВНО выбираемом времени остановки, а не только в
фиксированный момент.

Формализуем anytime-обёртку Катони: если экспоненциальный
процесс L_t = exp(λ·S_t − ψ(λ)·t) — неотрицательный
супермартингал (контракт h_super; для сумм независимых
ограниченных слагаемых это Hoeffding-лемма, задел есть в
CertifiedEstimator/Azuma), то по Виллю с вероятностью ≥ 1−δ
НИ В КАКОЙ момент t ≤ n взвешенный зазор S_t не превышает
порог (ψ(λ)·t + log(1/δ))/λ — равномерно по времени.

Честность: конструкция супермартингала — гипотеза контракта
(она доказуема в частных случаях); сама anytime-гарантия
(Ville-часть) доказана безусловно.
-/

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
