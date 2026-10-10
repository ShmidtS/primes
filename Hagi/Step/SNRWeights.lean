/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# SNRWeights — равномерная ортогонализация перевешивает шум

* `uniform_is_mean`: при равных весах `1/r` взвешенная сумма
  квадратов отклонений равна среднему;
* `focused_beats_uniform`: если у какого-то направления j
  отклонение строго ниже среднего, существует распределение
  веса `v` (неотрицательное, суммирующееся в 1) с
  `Σ v i·(dev i)² < Σ (dev i)²/r` — целевой SNR-вес строго
  лучше равномерного. Реализуемость такого веса конкретным
  преобразованием (полиномиальный дизайн) — не доказана.
-/

namespace Hagi.Step

open Finset

variable {r : ℕ} [NeZero r]

/-- `Σ_i (1/r)·(dev i)² = (Σ_i (dev i)²)/r` — равномерный вес
даёт точно среднее. -/
theorem uniform_is_mean (dev : Fin r → ℝ) :
    ∑ i, (1 / (r : ℝ)) * (dev i)^2
      = (∑ i, (dev i)^2) / r := by
  rw [← Finset.mul_sum]
  field_simp

/-- Если `(dev j)² < mean = (Σ (dev i)²)/r`, то существует
`v : Fin r → ℝ` с `0 ≤ v i`, `Σ v i = 1` и
`Σ v i·(dev i)² < (Σ (dev i)²)/r`. -/
theorem focused_beats_uniform (dev : Fin r → ℝ)
    (hdev : ∀ i, 0 ≤ (dev i)^2)
    (mean : ℝ) (hmean : mean = (∑ i, (dev i)^2) / r)
    (j : Fin r) (hj : (dev j)^2 < mean) :
    ∃ v : Fin r → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)
      ∧ ∑ i, v i * (dev i)^2 < (∑ i, (dev i)^2) / r := by
  refine ⟨fun i => if i = j then (1:ℝ) else 0, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = j
    · simp [h]
    · simp [h]
  · simp
  · have hsingle : ∑ i, (if i = j then (1:ℝ) else 0) * (dev i)^2
        = (dev j)^2 := by
      simp
    rw [hsingle, ← hmean]
    exact hj

end Hagi.Step

namespace Hagi
export Hagi.Step (uniform_is_mean focused_beats_uniform)
end Hagi
