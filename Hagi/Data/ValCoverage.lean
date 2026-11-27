/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# ValCoverage — покрытие хвоста контрольными окнами

train_optimal (optimal_lm.py, bfc2a19): контроль обучения — до 256 окон
равномерно по всему хвосту вместо первых 32 (сертификат лучше согласован с
реальным хвостом: 0.83 → 0.60). Первые `m` окон — смещение к началу хвоста.

* `grid_gap` — шаг равномерной сетки: пробел между соседними началами равен
  `step`;
* `prefix_uncovered` — первые `m` окон длины `k` покрывают `[0, m·k)`:
  при `m·k < n` хвост `[m·k, n)` не покрыт;
* `grid_covers_tail` — равномерная сетка с шагом `step = n/m` оставляет за
  последним началом не более `2·step`.
-/

namespace Hagi.Data.ValCoverage

/-- Шаг равномерной сетки: пробел между соседними началами равен `step`. -/
theorem grid_gap (step i : ℕ) : (i + 1) * step - i * step = step := by
  rw [Nat.succ_mul]; omega

/-- Первые `m` окон длины `k` покрывают `[0, m·k)`: при `m·k < n` хвост
`[m·k, n)` не покрыт (смещение выбора к началу). -/
theorem prefix_uncovered (n m k : ℕ) (h : m * k ≤ n) :
    0 < n - m * k ∨ m * k = n := by omega

/-- Равномерная сетка из `m` начал с шагом `step` (`m·step ≤ n < (m+1)·step`,
т.е. `step = n/m`): непокрытый кусок хвоста за последним началом не длиннее
`2·step`. -/
theorem grid_covers_tail (n m step : ℕ) (hlo : m * step ≤ n)
    (hhi : n < (m + 1) * step) : n - (m - 1) * step ≤ 2 * step := by
  by_cases hm : m = 0
  · subst hm; simp only [Nat.zero_mul, Nat.sub_zero, Nat.zero_sub] at *; omega
  · have hlast : (m - 1) * step = m * step - step := by
      rw [Nat.sub_mul, mul_comm, one_mul]
    rw [hlast]
    have hms : step ≤ m * step := by
      rw [mul_comm]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm)
    rw [Nat.add_mul, one_mul] at hhi
    omega

end Hagi.Data.ValCoverage
