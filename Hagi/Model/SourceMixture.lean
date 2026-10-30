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

/-! ### MaxRL-ядро (источник №58 §5.2): распределение
успешных ответов π⁺(y) = π(y)·r(y)/p нормировано — RL-цель
корректно переформулируется как likelihood-обучение на
π⁺ (мост генерация → верификация → MLE). -/

/-- Вероятность успеха p = ∑ π·r. -/
def successProb (pi : M → ℝ) (r : M → ℝ) : ℝ := ∑ y, pi y * r y

/-- Распределение успешных ответов (MaxRL-цель). -/
noncomputable def successDist (pi : M → ℝ) (r : M → ℝ) (y : M) : ℝ :=
  pi y * r y / successProb pi r

/-- НОРМИРОВКА π⁺: если π — распределение, r ∈ [0,1], и
вероятность успеха строго положительна, то π⁺ —
вероятностное распределение (корректность MaxRL-цели как
likelihood-обучения на успешных ответах; источник №58). -/
theorem successDist_norm (pi : M → ℝ) (r : M → ℝ)
    (hpisum : ∑ y, pi y = 1)
    (hr : ∀ y, 0 ≤ r y ∧ r y ≤ 1)
    (hpos : 0 < successProb pi r) :
    ∑ y, successDist pi r y = 1 := by
  unfold successDist
  have hterm : ∀ y, pi y * r y / successProb pi r
      = (successProb pi r)⁻¹ * (pi y * r y) := fun y => by
    rw [div_eq_mul_inv, mul_comm]
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  calc ∑ y, (successProb pi r)⁻¹ * (pi y * r y)
      = (successProb pi r)⁻¹ * ∑ y, pi y * r y :=
        (Finset.mul_sum Finset.univ (fun y => pi y * r y)
          ((successProb pi r)⁻¹)).symm
    _ = (successProb pi r)⁻¹ * successProb pi r := by
        rw [show ∑ y, pi y * r y = successProb pi r from rfl]
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)

/-- π⁺ НЕОТРИЦАТЕЛЬНА. -/
theorem successDist_nonneg (pi : M → ℝ) (r : M → ℝ)
    (hpi : ∀ y, 0 ≤ pi y) (hr : ∀ y, 0 ≤ r y)
    (hpos : 0 < successProb pi r) (y : M) :
    0 ≤ successDist pi r y := by
  unfold successDist
  apply div_nonneg _ (le_of_lt hpos)
  exact mul_nonneg (hpi y) (hr y)

end Hagi.Model.SourceMixture

