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

/-- Каскадный (plain) поток: T мультипликативных слоёв. -/
def cascade (g : ℕ → X → X) (x0 : X) : ℕ → X
  | 0 => x0
  | (t + 1) => g t (cascade g x0 t)

/-- ЭКСПОНЕНЦИАЛЬНАЯ ОЦЕНКА plain-каскада: T слоёв с
усилением ≤ (1+δ) дают ‖x_T‖ ≤ (1+δ)^T·‖x₀‖ — рост
экспоненциален по глубине (контраст с линейным
`res_bounded_drift`). -/
theorem cascade_exp_bound (g : ℕ → X → X) (x0 : X) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hg : ∀ (t : ℕ) (x : X), ‖g t x‖ ≤ (1 + delta) * ‖x‖)
    (T : ℕ) :
    ‖cascade g x0 T‖ ≤ (1 + delta) ^ T * ‖x0‖ := by
  induction T with
  | zero =>
      rw [show cascade g x0 0 = x0 from rfl]
      norm_num
  | succ t ih =>
      have hsplit : cascade g x0 (t + 1)
          = g t (cascade g x0 t) := rfl
      rw [hsplit]
      have hg' := hg t (cascade g x0 t)
      rw [pow_succ]
      calc ‖g t (cascade g x0 t)‖
          ≤ (1 + delta) * ‖cascade g x0 t‖ := hg'
        _ ≤ (1 + delta) * ((1 + delta) ^ t * ‖x0‖) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (1 + delta) ^ t * (1 + delta) * ‖x0‖ := by ring

/-- КОНТРАСТ ЛИНЕЙНОГО И ЭКСПОНЕНЦИАЛЬНОГО: мультипликативная
оценка доминирует линейную снизу Бернулли (1+δ)^T ≥ 1+Tδ —
residual-дрейф растёт ЛИНЕЙНО, plain-каскад — как минимум
линейно и в общем случае экспоненциально. Формальное ядро
того, почему глубокие plain-сети необучаемы, а
residual-обучаемы. -/
theorem linear_le_exp_contrast (delta : ℝ) (hdelta : 0 ≤ delta)
    (T : ℕ) :
    1 + (T:ℝ) * delta ≤ (1 + delta) ^ T :=
  one_add_mul_le_pow (by linarith) T

end Hagi.Model.Residual
