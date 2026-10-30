import Mathlib

/-!
# SourceMixture — единый objective (источник №58: Song et
# al., "Training Foundation Models with a Single Algorithm",
# arXiv 2610.40564)

Ядро идеи: pretraining/SFT/RL — обучение на СМЕСИ целевых
распределений q_t = ∑_s λ_{s,t} (ρ_s ∘ μ_s) с единым
token-level likelihood. Уровень 1: смесь КОНЕЧНЫХ
распределений нормирована — суммы вероятностей источников
переносятся на смесь (линейность + ∑λ = 1). Это фундамент
корректности единого objective: смесь — вероятностное
распределение.
-/

namespace Hagi.Model.SourceMixture

open Finset

variable {S M : Type*} [Fintype S] [Fintype M]

/-- Смесь распределений: q(x) = ∑_s λ_s · p_s(x). -/
def mixture (lam : S → ℝ) (p : S → M → ℝ) (x : M) : ℝ :=
  ∑ s, lam s * p s x

/-- НОРМИРОВКА СМЕСИ: если каждый источник — вероятностное
распределение на M, а веса λ образуют вероятностное
распределение на S, то смесь — вероятностное распределение
на M. Смесь корректна как распределение для единого
likelihood-обучения (источник №58, ядро). -/
theorem mixture_sum_one (lam : S → ℝ) (p : S → M → ℝ)
    (hlamsum : ∑ s, lam s = 1)
    (hp : ∀ s, ∑ x, p s x = 1) :
    ∑ x, mixture lam p x = 1 := by
  unfold mixture
  rw [Finset.sum_comm]
  have hinner : ∀ s ∈ Finset.univ,
      ∑ x, lam s * p s x = lam s := by
    intro s _
    rw [← Finset.mul_sum, hp s, mul_one]
  rw [Finset.sum_congr rfl hinner, hlamsum]

/-- НЕОТРИЦАТЕЛЬНОСТЬ СМЕСИ: при неотрицательных весах и
неотрицательных источниках смесь неотрицательна (смесь —
корректная основа взвешенного likelihood). -/
theorem mixture_nonneg (lam : S → ℝ) (p : S → M → ℝ)
    (hlam : ∀ s, 0 ≤ lam s) (hp : ∀ s x, 0 ≤ p s x)
    (x : M) : 0 ≤ mixture lam p x := by
  unfold mixture
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (hlam s) (hp s x)

end Hagi.Model.SourceMixture
