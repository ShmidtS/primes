/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# TrainBudget — заявленный бюджет обучения равен фактическому

Баг `train_certified` (optimal_lm.py до d90720a): `epochs // 10` вместо
`epochs` — сертифицированный путь обучал 10× меньше заявленного; все
прежние замеры CE относились к короткому обучению.

* `declaredSteps epochs N b = epochs·⌈N/b⌉` — заявленный бюджет;
* `buggySteps = max 1 (epochs/10)·⌈N/b⌉` — фактический до фикса;
* `buggySteps_le_tenth` — при `epochs ≥ 20` фактический ≤ 1/10 заявленного;
* `buggySteps_lt` — строго меньше.

Инвариант для CI кода: `steps_done = declaredSteps` после `train_certified`.
-/

namespace Hagi.Unified.TrainBudget

/-- Число батчей в одной эпохе: `⌈N/b⌉ = (N + b − 1) / b`, `b > 0`. -/
def batchesPerEpoch (N b : ℕ) : ℕ := (N + b - 1) / b
/-- Заявленный бюджет: `epochs` проходов по `N` примерам батчами `b`. -/
def declaredSteps (epochs N b : ℕ) : ℕ := epochs * batchesPerEpoch N b
/-- Баг `epochs // 10` (optimal_lm.py до d90720a): фактический бюджет. -/
def buggySteps (epochs N b : ℕ) : ℕ := max 1 (epochs / 10) * batchesPerEpoch N b
theorem batchesPerEpoch_pos (N b : ℕ) (hN : 0 < N) (hb : 0 < b) : 0 < batchesPerEpoch N b := by
  unfold batchesPerEpoch
  apply Nat.div_pos _ hb
  omega
theorem declaredSteps_pos (epochs N b : ℕ) (he : 0 < epochs) (hN : 0 < N) (hb : 0 < b) :
    0 < declaredSteps epochs N b := by
  unfold declaredSteps
  exact mul_pos he (batchesPerEpoch_pos N b hN hb)
/-- При `epochs ≥ 20` баг даёт не более `1/10` заявленного бюджета. -/
theorem buggySteps_le_tenth (epochs N b : ℕ) (hN : 0 < N) (hb : 0 < b) (h : 20 ≤ epochs) :
    10 * buggySteps epochs N b ≤ declaredSteps epochs N b := by
  unfold buggySteps declaredSteps
  have hmax : max 1 (epochs / 10) = epochs / 10 :=
    max_eq_right ((Nat.le_div_iff_mul_le (k := 10) (by omega)).2 (by omega))
  rw [hmax]
  calc 10 * (epochs / 10 * batchesPerEpoch N b) = (10 * (epochs / 10)) * batchesPerEpoch N b := by ring
    _ ≤ epochs * batchesPerEpoch N b := Nat.mul_le_mul_right _ (by rw [mul_comm]; exact Nat.div_mul_le_self epochs 10)
theorem buggySteps_lt (epochs N b : ℕ) (hN : 0 < N) (hb : 0 < b) (h : 20 ≤ epochs) :
    buggySteps epochs N b < declaredSteps epochs N b := by
  have hle := buggySteps_le_tenth epochs N b hN hb h
  have hpos := declaredSteps_pos epochs N b (by omega) hN hb
  omega

end Hagi.Unified.TrainBudget
