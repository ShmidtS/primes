import Mathlib

/-!
# AdaptiveChunking (приоритет 3 «HAGI Neural Computer»,
# такт №249): динамический чанкинг H-Net — M зависит от
# ВХОДА и параметров, а не фиксирован.

Статическая теория (HNet.lean) оценивает cost при
константном коэффициенте r. Реальное преимущество H-Net —
обучаемые границы: M_φ(x) = ChunkCount(H_φ(x)).

Формализуем честное сравнение:
1. `adaptive_cost`: C(x) = Σ_ℓ c_ℓ·M_ℓ(x)² — суммарная
   стоимость иерархии как функция входа;
2. `adaptive_le_static`: при ПОТОЧЕЧНОМ доминировании
   (∀ℓ, M_ℓ(x) ≤ L/r) динамическая стоимость ≤ статической
   (Σ c_ℓ (L/r)²) — адаптивность не хуже статического
   сжатия, если чанкер не проигрывает ни на одном уровне;
3. `adaptive_lt_of_strict`: строгое превосходство на одном
   уровне при неотрицательных ценах даёт строгую экономию.
-/

namespace Hagi.Model.AdaptiveChunking

variable {k : Type*} [Fintype k]

/-- Иерархическая стоимость: сумма по уровням c_ℓ·M_ℓ(x)². -/
noncomputable def adaptiveCost (c : k → ℝ) (M : k → ℝ) : ℝ :=
  ∑ l, c l * M l ^ 2

/-- АДАПТИВНОСТЬ НЕ ХУЖЕ СТАТИКИ: если динамический чанкер
на каждом уровне укладывается в статический размер
(M_ℓ(x) ≤ L/r ∀ℓ), то полная иерархическая стоимость не
превосходит статической. -/
theorem adaptive_le_static (c : k → ℝ) (hc : ∀ l, 0 ≤ c l)
    (M : k → ℝ) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    (hM : ∀ l, 0 ≤ M l)
    (hdom : ∀ l, M l ≤ L / r) :
    adaptiveCost c M ≤ ∑ l, c l * (L / r) ^ 2 := by
  have h1 : ∀ l : k, c l * M l ^ 2 ≤ c l * (L / r) ^ 2 := by
    intro l
    exact mul_le_mul_of_nonneg_left
      (by rw [sq, sq]; exact mul_self_le_mul_self (hM l) (hdom l)) (hc l)
  exact Finset.sum_le_sum (fun l _ => h1 l)

/-- СТРОГОЕ ПРЕИМУЩЕСТВО: положительная цена на уровне
l₀ и строгое доминирование M_{l₀}(x) < L/r дают строгую
экономию полной стоимости. -/
theorem adaptive_lt_of_strict (c : k → ℝ) (hc : ∀ l, 0 ≤ c l)
    (M : k → ℝ) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 < r)
    (hM : ∀ l, 0 ≤ M l)
    (hdom : ∀ l, M l ≤ L / r)
    (l₀ : k) (hc₀ : 0 < c l₀) (hstrict : M l₀ < L / r) :
    adaptiveCost c M < ∑ l, c l * (L / r) ^ 2 := by
  have h1 : ∀ l : k, c l * M l ^ 2 ≤ c l * (L / r) ^ 2 := by
    intro l
    exact mul_le_mul_of_nonneg_left
      (by rw [sq, sq]; exact mul_self_le_mul_self (hM l) (hdom l)) (hc l)
  have hstrictl : c l₀ * M l₀ ^ 2 < c l₀ * (L / r) ^ 2 := by
    have hkey : M l₀ ^ 2 < (L / r) ^ 2 := by
      rw [sq, sq]
      exact mul_self_lt_mul_self (hM l₀) hstrict
    exact mul_lt_mul_of_pos_left hkey hc₀
  exact Finset.sum_lt_sum (fun l _ => h1 l)
    ⟨l₀, Finset.mem_univ l₀, hstrictl⟩

end Hagi.Model.AdaptiveChunking
