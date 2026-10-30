import Mathlib

/-!
# Gradient Checkpointing: sqrt-трейдофф память/пересчёт
(источник №48)

Источник №48: Chen et al., "Training Deep Nets with Sublinear
Memory Cost" (arXiv 1604.06174). Хранить k контрольных точек
слоёв из n: память k + n/k (точки + пересчитываемые
сегменты), пересчёт ≈ n/k слоёв: оптимум k = √n даёт
O(√n) память вместо O(n) — квадратичная экономия памяти за
линейный пересчёт.

Формализованное ядро (строгое):
- `ckpt_mem_floor`: k + n/k ≥ 2·√n при k,n > 0 — нижняя
  граница памяти (AM-GM-2, разложение квадрата);
- `ckpt_sqrt_opt`: k = √n доставляет минимум (равенство в
  AM-GM): O(√n) — оптимальный выбор числа чекпоинтов.
-/

namespace Hagi.Optimization.Checkpoint

/-- Нижняя граница памяти чекпойнтинга: k + n/k ≥ 2√n. -/
theorem ckpt_mem_floor (k n : ℝ) (hk : 0 < k) (hn : 0 < n) :
    2 * Real.sqrt n ≤ k + n / k := by
  have h2 : 0 ≤ (k - Real.sqrt n) ^ 2 := sq_nonneg _
  have hexp : (k - Real.sqrt n) ^ 2
      = k ^ 2 - 2 * k * Real.sqrt n + n := by
    have h0 : (k - Real.sqrt n) ^ 2
        = k * k - 2 * k * Real.sqrt n
          + Real.sqrt n * Real.sqrt n := by ring
    rw [Real.mul_self_sqrt hn.le] at h0
    linarith [h0]
  rw [hexp] at h2
  have hkk : 0 < k ^ 2 := by positivity
  have hdiv : 0 < n / k := div_pos hn hk
  field_simp
  linarith [h2]

/-- k = √n доставляет равенство (оптимум). -/
theorem ckpt_sqrt_opt (n : ℝ) (hn : 0 < n) :
    Real.sqrt n + n / Real.sqrt n = 2 * Real.sqrt n := by
  have hpos : 0 < Real.sqrt n := Real.sqrt_pos_of_pos hn
  have hdivn : n / Real.sqrt n = Real.sqrt n := by
    rw [div_eq_iff hpos.ne', Real.mul_self_sqrt hn.le]
  rw [hdivn]
  linarith

end Hagi.Optimization.Checkpoint
