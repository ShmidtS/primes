import Hagi.Unified.DescentCore

/-!
# Error feedback: сжатая траектория точно отражает идеальную

Механизм компенсации сжатия: резидуал накапливает
несланданные координаты, и сжатая траектория отклоняется
от идеальной РОВНО на изменение резидуала — точная
идентичность, не оценка. Это фундамент возврата
PL-скорости для сжатых шагов после отрицательного
результата об отсутствии равномерной drop-грани.
-/

namespace Hagi.Unified.ErrorFeedback

open Hagi.Unified.DescentCore

variable {k : Type*} [Fintype k]

/-- ТЕЛЕСКОП EF: сумма сжатых векторов равна сумме
точных плюс изменение резидуала. -/
theorem ef_telescope (d e : ℕ → k → ℝ)
    (comp : (k → ℝ) → (k → ℝ))
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (n : ℕ) :
    ∑ t ∈ Finset.range n, comp (d t + e t)
      = (∑ t ∈ Finset.range n, d t) + e 0 - e n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hcomp : comp (d n + e n)
        = d n + e n - e (n + 1) := by
      rw [hEF n]
      abel
    rw [hcomp, ih]
    abel

/-- ТОЧНОЕ ОТКЛОНЕНИЕ СУММ: разность сжатой и точной
сумм равна изменению резидуала. -/
theorem ef_shadow_sum (d e : ℕ → k → ℝ)
    (comp : (k → ℝ) → (k → ℝ))
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (n : ℕ) :
    (∑ t ∈ Finset.range n, comp (d t + e t))
      - (∑ t ∈ Finset.range n, d t) = e 0 - e n := by
  rw [ef_telescope d e comp hEF n]
  abel

/-- ГЛАВНАЯ ТЕОРЕМА: EF-траектория точно отражает
идеальную. Итераты сжатого цикла против точного
отклоняются РОВНО на масштабированное изменение
резидуала. -/
theorem ef_iterate_shadow (d e : ℕ → k → ℝ)
    (comp : (k → ℝ) → (k → ℝ)) (eta : ℝ)
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (xC xF : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1) = xC t - eta • comp (d t + e t))
    (hxF : ∀ t, xF (t + 1) = xF t - eta • d t)
    (hx0 : xC 0 = xF 0) (n : ℕ) :
    xC n - xF n = eta • (e n - e 0) := by
  induction n with
  | zero => rw [hx0]; simp
  | succ n ih =>
    have hcomp : comp (d n + e n)
        = d n + e n - e (n + 1) := by
      rw [hEF n]
      abel
    have hstep : xC (n + 1) - xF (n + 1)
        = (xC n - xF n) - eta • (e n - e (n + 1)) := by
      rw [hxC n, hxF n, hcomp]
      module
    rw [hstep, ih]
    module

end Hagi.Unified.ErrorFeedback
