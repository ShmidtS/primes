import Hagi.Unified.ErrorFeedback
import Hagi.Unified.QuadGDRate

/-!
# EF-сжатие теняет градиентный спуск на эталоне

Мост миров: сжатая траектория (worker шлёт сжатые
направления идеальных вычислений, резидуал копит
несланданное) отклоняется от точного градиентного
спуска `quadGD` РОВНО на масштабированное изменение
резидуала. Компрессия обучения без потери траектории.
-/

namespace Hagi.Unified.SignEFQuad

open Hagi.Unified.ErrorFeedback
open Hagi.Unified.QuadGDRate
open Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad

variable {k : Type*} [Fintype k]

/-- ГЛАВНАЯ ТЕОРЕМА: EF-сжатая траектория теняет точный
градиентный спуск на квадратичной машине — отклонение
РАВНО масштабированному изменению резидуала. -/
theorem quad_ef_shadow (a : k → ℝ) (eta : ℝ) (x0 : k → ℝ)
    (e : ℕ → k → ℝ) (comp : (k → ℝ) → (k → ℝ))
    (hEF : ∀ t, e (t + 1)
      = quadGrad a (quadGD a eta x0 t) + e t
        - comp (quadGrad a (quadGD a eta x0 t) + e t))
    (xC : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1)
      = xC t - eta • comp
        (quadGrad a (quadGD a eta x0 t) + e t))
    (hx0 : xC 0 = x0) (n : ℕ) :
    xC n - quadGD a eta x0 n = eta • (e n - e 0) := by
  have hxF : ∀ t, quadGD a eta x0 (t + 1)
      = quadGD a eta x0 t
        - eta • quadGrad a (quadGD a eta x0 t) := by
    intro t
    funext i
    simp [quadGD, Pi.sub_apply, Pi.smul_apply]
  exact ef_iterate_shadow
    (fun t => quadGrad a (quadGD a eta x0 t)) e comp eta hEF
    xC (quadGD a eta x0) hxC hxF hx0 n

/-- СЛЕДСТВИЕ: нулевой резидуал — сжатая траектория
СОВПАДАЕТ с точным градиентным спуском. -/
theorem quad_ef_exact (a : k → ℝ) (eta : ℝ) (x0 : k → ℝ)
    (e : ℕ → k → ℝ) (comp : (k → ℝ) → (k → ℝ))
    (he0 : e 0 = 0)
    (hEF : ∀ t, e (t + 1)
      = quadGrad a (quadGD a eta x0 t) + e t
        - comp (quadGrad a (quadGD a eta x0 t) + e t))
    (xC : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1)
      = xC t - eta • comp
        (quadGrad a (quadGD a eta x0 t) + e t))
    (hx0 : xC 0 = x0) (n : ℕ)
    (hzero : e n = e 0) :
    xC n = quadGD a eta x0 n := by
  have h := quad_ef_shadow a eta x0 e comp hEF xC hxC hx0 n
  rw [hzero] at h
  rw [sub_self, smul_zero] at h
  exact sub_eq_zero.mp h

end Hagi.Unified.SignEFQuad
