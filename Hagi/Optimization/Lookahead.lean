import Mathlib

/-!
# Lookahead optimizer (источник №75: Zhang et al.,
# "Lookahead Optimizer: k steps forward, 1 step back",
# arXiv 1907.08610)

Двухмасштабная схема: k внутренних (fast) шагов от якоря w,
затем медленный шаг якоря к последнему быстрому итерату:
w' = w + α·(x_k − w), α ∈ (0,1].

Формализуем честные свойства:
1. `lookahead_mem`: новый якорь лежит МЕЖДУ старым якорем и
   быстрым итератом (выпуклая комбинация — шаг назад не
   проскакивает цель);
2. `lookahead_gap`: |w' − w| = α·|x_k − w| — смещение якоря
   строго контролируется (α — ручка скорости дрейфа);
3. `lookahead_range`: если якорь и быстрый итерат в [lo,hi],
   новый якорь тоже в [lo,hi] (инвариант диапазона).
-/

namespace Hagi.Optimization.Lookahead

/-- Медленный шаг якоря к быстрому итерату. -/
def slowStep (w x α : ℝ) : ℝ := w + α * (x - w)

/-- ЯКОРЬ МЕЖДУ: новый якорь — выпуклая комбинация старого
якоря и быстрого итерата (α ∈ [0,1]): лежит в их выпуклой
оболочке — «шаг назад» не проскакивает цель. -/
theorem lookahead_mem (w x α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    min w x ≤ slowStep w x α ∧ slowStep w x α ≤ max w x := by
  have hcvx : slowStep w x α = (1 - α) * w + α * x := by
    unfold slowStep; ring
  rcases le_total w x with hwx | hxw
  · rw [min_eq_left hwx, max_eq_right hwx]
    constructor
    · -- (1−α)w + αx ≥ w ⟺ αx ≥ αw
      rw [hcvx]; nlinarith [hwx, hα]
    · rw [hcvx]; nlinarith [hwx, hα, hα1]
  · rw [min_eq_right hxw, max_eq_left hxw]
    constructor
    · rw [hcvx]; nlinarith [hxw, hα]
    · rw [hcvx]; nlinarith [hxw, hα, hα1]

/-- КОНТРОЛЬ СМЕЩЕНИЯ: |w' − w| = α·|x − w| — дрейф якоря
пропорционален α (α ∈ [0,1] — ручка скорости якоря). -/
theorem lookahead_gap (w x α : ℝ) (hα : 0 ≤ α) :
    |slowStep w x α - w| = α * |x - w| := by
  unfold slowStep
  rw [show w + α * (x - w) - w = α * (x - w) from by ring, abs_mul,
    abs_of_nonneg hα]

/-- ИНВАРИАНТ ДИАПАЗОНА: якорь и быстрый итерат в [lo,hi]
⟹ новый якорь в [lo,hi] (lookahead не покидает оболочку
ингредиентов). -/
theorem lookahead_range (w x α lo hi : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hw : lo ≤ w ∧ w ≤ hi) (hx : lo ≤ x ∧ x ≤ hi) :
    lo ≤ slowStep w x α ∧ slowStep w x α ≤ hi := by
  have h := lookahead_mem w x α hα hα1
  constructor
  · exact le_trans (le_min hw.1 hx.1) h.1
  · exact le_trans h.2 (max_le hw.2 hx.2)

end Hagi.Optimization.Lookahead
