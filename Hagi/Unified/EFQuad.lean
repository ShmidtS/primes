import Hagi.Unified.ErrorFeedback
import Hagi.Unified.PLQuad

/-!
# Качество EF-цикла на квадратичной машине

Соединение точного отражения EF-траектории с
PL-скоростью идеальной: энергия сжатой траектории равна
энергии идеальной плюс ТОЧНЫЕ резидуальные члены, а
идеальная сжимается линейно. Скорость восстановлена с
точностью до контроля резидуала.
-/

namespace Hagi.Unified.EFQuad

open Hagi.Unified.ErrorFeedback
open Hagi.Unified.PLQuad
open Hagi.Unified.PLLoop
open Hagi.Unified.DescentCore
open Hagi.Unified.DescentCoreQuad

variable {k : Type*} [Fintype k]

/-- ТОЧНЫЙ ПЕРЕНОС: энергия EF-итерата равна энергии
идеального итерата плюс резидуальные члены — без
оценок, тождество. -/
theorem ef_quad_transfer (a : k → ℝ)
    (d e : ℕ → k → ℝ) (comp : (k → ℝ) → (k → ℝ))
    (eta : ℝ)
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (xC xF : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1) = xC t - eta • comp (d t + e t))
    (hxF : ∀ t, xF (t + 1) = xF t - eta • d t)
    (hx0 : xC 0 = xF 0) (n : ℕ) :
    quadE a (xC n)
      = quadE a (xF n)
        + inprod (quadGrad a (xF n)) (eta • (e n - e 0))
        + (1:ℝ) / 2 * nrm2 (eta • (e n - e 0)) := by
  have hdev := ef_iterate_shadow d e comp eta hEF xC xF hxC hxF hx0 n
  have hd : xC n = xF n + eta • (e n - e 0) := by
    rw [← hdev]
    abel
  rw [hd]
  exact quad_descent_eq a (xF n) (eta • (e n - e 0))

/-- ГЛАВНЫЙ ВЫВОД: скорость EF-цикла восстановлена.
Если идеальная траектория удовлетворяет drop-грани и
PL-связи, энергия сжатой не превосходит линейно
сжимающейся идеальной плюс ТОЧНЫЕ резидуальные члены. -/
theorem ef_quad_quality (a : k → ℝ)
    (d e : ℕ → k → ℝ) (comp : (k → ℝ) → (k → ℝ))
    (eta : ℝ)
    (hEF : ∀ t, e (t + 1) = d t + e t - comp (d t + e t))
    (xC xF : ℕ → k → ℝ)
    (hxC : ∀ t, xC (t + 1) = xC t - eta • comp (d t + e t))
    (hxF : ∀ t, xF (t + 1) = xF t - eta • d t)
    (hx0 : xC 0 = xF 0) (n : ℕ)
    (drops : ℕ → ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hκ2 : 2 * κ < 1)
    (hdrop : ∀ t < n, κ * nrm2 (quadGrad a (xF t)) ≤ drops t)
    (hcert : ∀ t < n,
      quadE a (xF (t + 1)) ≤ quadE a (xF t) - drops t) :
    quadE a (xC n)
      ≤ (1 - 2 * κ)^n * quadE a (xF 0)
        + inprod (quadGrad a (xF n)) (eta • (e n - e 0))
        + (1:ℝ) / 2 * nrm2 (eta • (e n - e 0)) := by
  have hrate := quad_pl_rate a xF drops n κ hκ hκ2 hdrop hcert
  have htransfer := ef_quad_transfer a d e comp eta hEF xC xF
    hxC hxF hx0 n
  linarith

end Hagi.Unified.EFQuad
