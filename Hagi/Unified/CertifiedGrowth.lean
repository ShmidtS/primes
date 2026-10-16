/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.CertifiedGains
import Hagi.Foundations.GrowthDynamics

/-!
# CertifiedGrowth — сертифицированная гарантия роста (R561 ч.2)

Смык certification-каскада (R554/555/558) с рост-дугой (R560/
R561 ч.1): нижняя полоса на горизонте сертифицируется парой
измерений на каждом шаге (prob ladder R555); на хорошем событии
`band_guaranteed_growth_range` даёт гарантированный рост. Итог:
«измеренные margins → гарантированный capability-рост» с
уровнем 1 − 2T·e^{−2nε²}.
-/

open scoped BigOperators

namespace Hagi.Unified

variable {n : ℕ} {V : Type} [Fintype V] [Nonempty V]

/-- **Certified нижняя полоса (R561 ч.2)**: с вероятностью
≥ 1 − 2T·e^{−2nε²} — импликация «все margins сертифицированы →
гарантированный рост C T ≥ C 0 + (b/σ)(1−(1−σ)^T)». -/
theorem certified_band_growth (p : Fin n → V → ℝ)
    (hp : IsProbSys p)
    (X Y : ℕ → Fin n → V → ℝ)
    (hX : ∀ t i v, 0 ≤ X t i v ∧ X t i v ≤ 1)
    (hY : ∀ t i v, 0 ≤ Y t i v ∧ Y t i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (C G : ℕ → ℝ) (b σ : ℝ)
    (T : ℕ)
    -- мост: μ-неравенство на шаге t → нижняя полоса на t
    (hbridge : ∀ t < T, ∑ i, coordMean p (Y t) i
        ≤ ∑ i, coordMean p (X t) i
      → b * (1 - σ) ^ t ≤ G t)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    1 - 2 * (T:ℝ) * Real.exp (- 2 * (n:ℝ) * eps ^ 2)
      ≤ prodPq p (fun ω =>
        (∀ t < T,
          ∑ i, Y t i (ω i) + 2 * (n:ℝ) * eps
            ≤ ∑ i, X t i (ω i))
        → C T ≥ C 0 + b * (1 - (1 - σ) ^ T) / σ) := by
  classical
  set M : ℝ := 2 * Real.exp (- 2 * (n:ℝ) * eps ^ 2) with hMdef
  set q : (Fin n → V) → Prop := fun ω =>
    (∀ t < T, ∑ i, Y t i (ω i) + 2 * (n:ℝ) * eps
      ≤ ∑ i, X t i (ω i))
    → C T ≥ C 0 + b * (1 - (1 - σ) ^ T) / σ with hqdef
  set S : ℕ → (Fin n → V) → Prop := fun t ω =>
    (∑ i, Y t i (ω i) + 2 * (n:ℝ) * eps ≤ ∑ i, X t i (ω i))
    ∧ ¬ (∑ i, coordMean p (Y t) i ≤ ∑ i, coordMean p (X t) i)
    with hSdef
  -- детерминированный рост при полной (range) нижней полосе
  have hgrowth : (∀ t < T, b * (1 - σ) ^ t ≤ G t) →
      C T ≥ C 0 + b * (1 - (1 - σ) ^ T) / σ :=
    fun hband => Hagi.Foundations.band_guaranteed_growth_range C G b σ T
      hstep hband hσ hσ1
  -- (1) шаговые bad-события: margin верен, μ нарушен
  have hA : ∀ t, prodPq p (S t) ≤ M := by
    intro t
    have hcert := certified_premise p hp (Y t) (X t) (hY t)
      (hX t) hn eps heps
    have hmono := prodPq_mono p hp
      (fun ω => (∑ i, Y t i (ω i) + 2 * (n:ℝ) * eps
        ≤ ∑ i, X t i (ω i))
      → ∑ i, coordMean p (Y t) i ≤ ∑ i, coordMean p (X t) i)
      (fun ω => ¬ ((∑ i, Y t i (ω i) + 2 * (n:ℝ) * eps
        ≤ ∑ i, X t i (ω i))
      ∧ ¬ (∑ i, coordMean p (Y t) i
        ≤ ∑ i, coordMean p (X t) i)))
      (fun ω h hA => absurd (h hA.1) hA.2)
    rw [prodPq_compl p hp] at hmono
    linarith [hmono]
  -- (2) точечное покрытие: нарушение цели → ∃ t < T, S t ω
  have hcover : ∀ ω : Fin n → V, ¬ q ω → ∃ t < T, S t ω := by
    intro ω hcon
    rw [not_imp] at hcon
    obtain ⟨hmargin, hnotake⟩ := hcon
    rw [not_le] at hnotake
    -- нарушенная полоса: ∃ t < T, ¬(b(1−σ)^t ≤ G t)
    have hex : ∃ t < T, ¬ (b * (1 - σ) ^ t ≤ G t) := by
      by_contra hcon2
      push Not at hcon2
      exact absurd (hgrowth hcon2) (not_le.mpr hnotake)
    obtain ⟨t, ht, hviol⟩ := hex
    refine ⟨t, ht, hmargin t ht, fun hmu => ?_⟩
    exact hviol (hbridge t ht hmu)
  -- (3) лестница
  have hL := prob_ladder_lower p hp q S T M hA hcover
  have hMrw : M = 2 * Real.exp (- 2 * (n:ℝ) * eps ^ 2) := hMdef
  rw [hMrw] at hL
  linarith

end Hagi.Unified
