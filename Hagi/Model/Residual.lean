import Mathlib

/-!
# Residual-соединения: ограниченный дрейф (источник №22)

Источник №22: He et al., "Deep Residual Learning for Image
Recognition" (arXiv 1512.03385): residual-соединения
x_{t+1} = x_t + f(x_t) делают обучение глубоких сетей
возможным — градиент течёт по identity-пути, а приращения
остаются ограниченными.

Формализованное ядро (строгое):
- `resStep`: один residual-шаг x + f(x);
- `res_bounded_drift`: если каждый residual-блок вносит
  приращение нормы ≤ ε, то после T блоков суммарный дрейф
  от входа ≤ T·ε (индукция + неравенство треугольника) —
  глубина не разрушает сигнал: приращения аддитивны, не
  мультипликативны (контраст с plain-сетями, где
  мультипликативный каскад экспоненциален).
-/

namespace Hagi.Model.Residual

variable {X : Type*} [NormedAddCommGroup X]

/-- Один residual-шаг: x ↦ x + f x. -/
def resStep (f : X → X) (x : X) : X := x + f x

/-- Residual-поток: T последовательных шагов. -/
def resStream (f : ℕ → X → X) (x0 : X) : ℕ → X
  | 0 => x0
  | (t + 1) => resStep (f t) (resStream f x0 t)

/-- ОГРАНИЧЕННЫЙ ДРЕЙФ residual-потока: T шагов с
приращениями ≤ ε каждый — суммарное отклонение ≤ T·ε.
Приращения АДДИТИВНЫ: глубина T даёт линейный (не
экспоненциальный) рост дрейфа — ядро обучаемости глубоких
residual-сетей. -/
theorem res_bounded_drift (f : ℕ → X → X) (x0 : X) (eps : ℝ)
    (_heps : 0 ≤ eps)
    (hf : ∀ (t : ℕ) (x : X), ‖f t x‖ ≤ eps)
    (T : ℕ) :
    ‖resStream f x0 T - x0‖ ≤ (T:ℝ) * eps := by
  induction T with
  | zero =>
      rw [show resStream f x0 0 = x0 from rfl, sub_self, norm_zero]
      norm_num
  | succ t ih =>
      have hsplit : resStream f x0 (t + 1)
          = resStream f x0 t + f t (resStream f x0 t) := rfl
      have htri : ‖resStream f x0 t + f t (resStream f x0 t) - x0‖
          ≤ ‖resStream f x0 t - x0‖ + ‖f t (resStream f x0 t)‖ := by
        calc ‖resStream f x0 t + f t (resStream f x0 t) - x0‖
            = ‖(resStream f x0 t - x0) + f t (resStream f x0 t)‖ := by
              congr 1
              abel
          _ ≤ ‖resStream f x0 t - x0‖ + ‖f t (resStream f x0 t)‖ :=
              norm_add_le _ _
      have hf' := hf t (resStream f x0 t)
      rw [hsplit]
      have hcast : ((t + 1 : ℕ) : ℝ) = (t:ℝ) + 1 := Nat.cast_succ t
      rw [hcast]
      linarith

end Hagi.Model.Residual

