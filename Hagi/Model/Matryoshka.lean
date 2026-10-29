import Mathlib

/-!
# Matryoshka Representation Learning (источник №44)

Источник №44: Kusupati et al., "Matryoshka Representation
Learning" (arXiv 2205.13147). Вложенные представления: первые
m координат эмбеддинга — сами по себе полноценное
представление (масштабируемая гранулярность: одно кодирование
обслуживает любой бюджет размерности).

Формализованное ядро (строгое):
- `matryoshka_norm_le`: норма (сумма квадратов) усечения
  m ≤ n НЕ превосходит полной нормы — иерархическая
  вложенность: усечение теряет не более чем «хвост»;
- `matryoshka_dist_le`: расстояние усечений ≤ расстояния
  полных векторов (усечение никогда не усиливает
  расстояние).
-/

namespace Hagi.Model.Matryoshka

open Finset

/-- Норма усечения не превосходит полной. -/
theorem matryoshka_norm_le (x : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ∑ i ∈ Finset.range m, (x i) ^ 2
      ≤ ∑ i ∈ Finset.range n, (x i) ^ 2 := by
  induction n with
  | zero =>
    have hm0 : m = 0 := Nat.le_zero.mp hmn
    rw [hm0]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hmn with h | h
    · have h2 : m ≤ n := Nat.le_of_lt_succ h
      have hstep := ih h2
      rw [Finset.sum_range_succ]
      have hnn : 0 ≤ (x n) ^ 2 := sq_nonneg _
      linarith
    · rw [h]

/-- Расстояние усечений не превосходит расстояния полных
векторов. -/
theorem matryoshka_dist_le (x y : ℕ → ℝ) (m n : ℕ)
    (hmn : m ≤ n) :
    ∑ i ∈ Finset.range m, ((x i - y i)) ^ 2
      ≤ ∑ i ∈ Finset.range n, ((x i - y i)) ^ 2 :=
  matryoshka_norm_le (fun i => x i - y i) m n hmn

end Hagi.Model.Matryoshka
