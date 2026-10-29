import Mathlib

/-!
# Flow Matching: линейный путь (источник №41)

Источник №41: Lipman et al., "Flow Matching for
Generative Modeling" (arXiv 2210.02747). Обучение генерации
через векторные поля: путь x_t = (1−t)·x₀ + t·x₁ —
прямолинейная интерполяция шум→данные с ПОСТОЯННОЙ
скоростью x₁−x₀ (против стохастических SDE-путей DDPM).

Формализованное ядро (строгое):
- `flow_path`: x_t = (1−t)·x₀ + t·x₁;
- `flow_start/flow_end`: endpoints — t=0 даёт x₀, t=1
  даёт x₁ (точная доставка);
- `flow_convex`: при t ∈ [0,1] точка пути лежит МЕЖДУ x₀ и
  x₁ (по каждой координате) — путь не выходит за отрезок;
- `flow_mid`: средняя точка — середина отрезка.
-/

namespace Hagi.Model.FlowMatching

/-- Линейный путь потока. -/
noncomputable def flowPath (x0 x1 t : ℝ) : ℝ :=
  (1 - t) * x0 + t * x1

theorem flow_start (x0 x1 : ℝ) : flowPath x0 x1 0 = x0 := by
  norm_num [flowPath]

theorem flow_end (x0 x1 : ℝ) : flowPath x0 x1 1 = x1 := by
  norm_num [flowPath]

/-- При t ∈ [0,1] путь между endpoints. -/
theorem flow_convex (x0 x1 t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hle : x0 ≤ x1) :
    x0 ≤ flowPath x0 x1 t ∧ flowPath x0 x1 t ≤ x1 := by
  have hdiff : 0 ≤ x1 - x0 := by linarith
  have h1 : flowPath x0 x1 t = x0 + t * (x1 - x0) := by
    unfold flowPath
    ring
  rw [h1]
  have hnn : t * (x1 - x0) ≤ x1 - x0 := by
    rw [mul_comm]
    exact mul_le_of_le_one_right hdiff ht1
  have hpos : 0 ≤ t * (x1 - x0) := mul_nonneg ht0 hdiff
  constructor <;> linarith

theorem flow_mid (x0 x1 : ℝ) :
    flowPath x0 x1 (1 / 2) = (x0 + x1) / 2 := by
  norm_num [flowPath]
  linarith

end Hagi.Model.FlowMatching
