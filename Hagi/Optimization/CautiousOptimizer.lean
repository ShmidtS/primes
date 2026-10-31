import Mathlib

/-!
# CautiousOptimizer (источник №78: "The Cautious Optimizer",
# arXiv 2411.16085)

Идея: маскировать компоненты обновления, ЗНАК которых
расходится со знаком градиента (u_i·g_i ≤ 0 → отбросить):
u'_i = u_i, если 0 < u_i·g_i; иначе 0.

Формализуем честные свойства:
1. `cautiousNorm_le`: маскирование НЕ увеличивает норму
   (‖u'‖ ≤ ‖u‖ — отбрасывание компонент сжимает);
2. `cautiousAligned`: выжившие компоненты согласованы со
   знаком градиента (u'_i·g_i ≥ 0);
3. `cautiousId`: при полной согласованности маска —
   тождество (не портит хороший update);
4. `cautiousZero`: полностью несогласованный update
   обнуляется (осторожность = отказ от вредного шага).
-/

namespace Hagi.Optimization.CautiousOptimizer

open Classical

/-- Осторожная маска: сохранить только компоненты,
согласованные со знаком градиента. -/
noncomputable def cautiousMask (u g : ℝ) : ℝ := if 0 < u * g then u else 0

/-- НОРМА НЕ РАСТЁТ: маскированная компонента не превосходит
исходной по модулю. -/
theorem cautiousMask_abs_le (u g : ℝ) :
    |cautiousMask u g| ≤ |u| := by
  unfold cautiousMask
  by_cases h : 0 < u * g
  · rw [if_pos h]
  · rw [if_neg h]
    simp

/-- СОГЛАСОВАННОСТЬ: выжившая компонента имеет
u'·g ≥ 0 — маска убирает только знаковые конфликты. -/
theorem cautiousAligned (u g : ℝ) :
    0 ≤ cautiousMask u g * g := by
  unfold cautiousMask
  by_cases h : 0 < u * g
  · rw [if_pos h]; exact h.le
  · rw [if_neg h]; simp

/-- ТОЖДЕСТВО ПРИ СОГЛАСОВАННОСТИ: если u·g > 0, маска
сохраняет u (хороший update не портится). -/
theorem cautiousId (u g : ℝ) (h : 0 < u * g) :
    cautiousMask u g = u := by
    unfold cautiousMask
    rw [if_pos h]

/-- ПОЛНЫЙ ОТКАЗ ПРИ КОНФЛИКТЕ: если u·g ≤ 0, шаг
обнуляется (осторожность = не вредить). -/
theorem cautiousZero (u g : ℝ) (h : u * g ≤ 0) :
    cautiousMask u g = 0 := by
    unfold cautiousMask
    rw [if_neg (by linarith)]

end Hagi.Optimization.CautiousOptimizer
