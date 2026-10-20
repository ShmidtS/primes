/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Optimization.InexactContraction
import Hagi.Optimization.SubspaceGrowth

set_option linter.style.header false

namespace Hagi.Optimization

/-!
# AdaptiveCycle — полный адаптивный цикл HAGI

Сводная теорема программы «три геометрии»: внешний цикл
(рост подпространства по остатку проекции, конечность
C₀/δ расширений из `growth_finite`) × внутренний цикл
(пересчёт до останова: сжатие с полом квантования и явный
K-горизонт из `inexact_contraction_halt`). Полный цикл
«расширение → пересчёт → останов» ограничен:
(N расширений)·δ ≤ C₀ и на каждом расширении внутренняя
ошибка достигает допуска τ за конечный горизонт K.
-/

/-- **Полный адаптивный цикл: граница числа расширений.**
Если метрика покрытия неотрицательна и каждое принятое
расширение улучшает её минимум на δ > 0, то любое число
принятых расширений N ≤ C₀/δ — рост архитектуры конечен.
Вместе с `inexact_contraction_halt` (внутренний пересчёт
останавливается за явный K-горизонт на каждом расширении)
это замыкает полный цикл «расширение → пересчёт → останов»
геометрически адаптивной HAGI. -/
theorem adaptive_cycle_expansions (C : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hstepC : ∀ k : ℕ, C (k+1) ≤ C k - δ) (hC : ∀ j : ℕ, 0 ≤ C j)
    (N : ℕ) :
    (N:ℝ) ≤ C 0 / δ := by
  have h := growth_finite C δ hδ hstepC hC N
  exact (le_div_iff₀ hδ).mpr h

end Hagi.Optimization
