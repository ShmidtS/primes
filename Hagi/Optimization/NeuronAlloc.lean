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


theorem neuron_alloc_opt_attained {ι : Type*} [Fintype ι]
    [Nonempty ι] (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (N : ℝ) (hN : 0 < N) :
    ∑ i, c i / (Real.sqrt (c i) * N / ∑ j, Real.sqrt (c j))
      = (∑ i, Real.sqrt (c i)) ^ 2 / N := by
  have hSpos : 0 < ∑ j, Real.sqrt (c j) :=
    Finset.sum_pos' (fun i _ => Real.sqrt_nonneg _)
      (let i0 := Classical.arbitrary ι
       ⟨i0, Finset.mem_univ i0, Real.sqrt_pos.mpr (hc i0)⟩)
  have key : ∀ r S : ℝ, 0 < r → 0 < S → 0 < N →
      r * r * S / (r * N) = r * S / N := by
    intro r S hr hS' hN'
    field_simp
  have hterm : ∀ i, c i / (Real.sqrt (c i) * N
      / ∑ j, Real.sqrt (c j))
      = Real.sqrt (c i) * (∑ j, Real.sqrt (c j)) / N := by
    intro i
    have hpos : 0 < Real.sqrt (c i) := Real.sqrt_pos.mpr (hc i)
    have hsq : c i = Real.sqrt (c i) * Real.sqrt (c i) := by
      have h2 := Real.sq_sqrt (hc i).le
      rw [sq] at h2
      exact h2.symm
    rw [div_div_eq_mul_div]
    nth_rewrite 1 [hsq]
    exact key _ _ hpos hSpos hN
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [← Finset.sum_div]
  rw [← Finset.sum_mul]
  ring

end Hagi.Optimization
