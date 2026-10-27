import Hagi.Core.Concat

/-!
# NeuronAlloc — оптимальное распределение нейронов по подтаскам

Источник: resource model of neural scaling (потеря подтаска
обратно пропорциональна выделенным нейронам, arXiv-класс
2023–2025). Ядро: суммарная потеря Σ cᵢ/nᵢ при бюджете
Σ nᵢ = N минимизируется аллокацией nᵢ ∝ √cᵢ, минимум
(Σ √cᵢ)²/N — структура Энгеля (тот же экстремаль, что
compute_scaling_lower_bound для времени).
-/

namespace Hagi.Optimization

open Finset

/-- НИЖНЯЯ ГРАНИЦА: для любых положительных аллокаций с
бюджетом N суммарная обратная потеря ≥ (Σ √cᵢ)²/N
(Коши–Шварц: (Σ √cᵢ)² ≤ (Σ cᵢ/nᵢ)·(Σ nᵢ)). -/
theorem neuron_alloc_lower_bound {ι : Type*} [Fintype ι]
    (c n : ι → ℝ) (hc : ∀ i, 0 < c i) (hn : ∀ i, 0 < n i)
    (N : ℝ) (hsum : ∑ i, n i = N) (hN : 0 < N) :
    (∑ i, Real.sqrt (c i)) ^ 2 / N ≤ ∑ i, c i / n i := by
  -- КШ: (Σ √(cᵢ/nᵢ)·√nᵢ)² ≤ (Σ cᵢ/nᵢ)(Σ nᵢ)
  have hcs : (∑ i, Real.sqrt (c i)) ^ 2
      ≤ (∑ i, c i / n i) * N := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => Real.sqrt (c i / n i)) (fun i => Real.sqrt (n i))
    have hterm : ∀ i,
        Real.sqrt (c i / n i) * Real.sqrt (n i) = Real.sqrt (c i) := by
      intro i
      rw [← Real.sqrt_mul (div_nonneg (hc i).le (hn i).le) (n i)]
      congr 1
      exact div_mul_cancel₀ (c i) (ne_of_gt (hn i))
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_congr rfl fun i _ => Real.sq_sqrt
        (div_nonneg (hc i).le (hn i).le),
      Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hn i).le,
      show ∑ i, n i = N from hsum] at h
    exact h
  rw [div_le_iff₀ hN]
  have hnn : (0:ℝ) ≤ ∑ i, c i / n i :=
    Finset.sum_nonneg fun i _ => div_nonneg (hc i).le (hn i).le
  nlinarith [hcs, hN.le, sq_nonneg (∑ i, Real.sqrt (c i))]


end Hagi.Optimization

