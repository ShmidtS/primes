import Mathlib

/-!
# Classifier-Free Guidance (источник №40)

Источник №40: Ho & Salimans, "Classifier-Free Diffusion
Guidance" (arXiv 2207.12598). Направленный диффузионный шаг
БЕЗ классификатора: ε̃ = ε_u + w·(ε_c − ε_u) — комбинация
условного и безусловного предсказаний шума.

Формализованное ядро (строгое):
- `cfg_interp`: ε̃ = (1−w)·ε_u + w·ε_c — линейная
  интерполяция;
- `cfg_convex`: при w ∈ [0,1] предсказание лежит МЕЖДУ
  условным и безусловным (выпуклая комбинация);
- `cfg_boost`: при w > 1 вектор ОТКЛОНЕНИЯ от условного
  предсказания пропорционален (w−1) и направлен от
  безусловного — экстраполяция УСИЛИВАЕТ условность.
-/

namespace Hagi.Model.CFG

/-- Интерполяционная форма guidance. -/
theorem cfg_interp (w eu ec : ℝ) :
    eu + w * (ec - eu) = (1 - w) * eu + w * ec := by
  ring

/-- При w ∈ [0,1] предсказание между безусловным и
условным. -/
theorem cfg_convex (w eu ec : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hle : eu ≤ ec) :
    eu ≤ eu + w * (ec - eu) ∧ eu + w * (ec - eu) ≤ ec := by
  have hdiff : 0 ≤ ec - eu := by linarith
  have hprod : 0 ≤ w * (ec - eu) := mul_nonneg hw0 hdiff
  have h2 : w * (ec - eu) ≤ ec - eu := by
    rw [mul_comm]
    exact mul_le_of_le_one_right hdiff hw1
  constructor <;> linarith

/-- При w > 1 отклонение от условного пропорционально (w−1)
и направлено от безусловного. -/
theorem cfg_boost (w eu ec : ℝ) (_hw : 1 < w)
    : eu + w * (ec - eu) - ec = (w - 1) * (ec - eu) := by
  ring

end Hagi.Model.CFG
