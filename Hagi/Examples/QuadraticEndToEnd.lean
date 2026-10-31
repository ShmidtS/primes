import Mathlib

/-!
# QuadraticEndToEnd — сквозной обучающий шаг (аудит v13 P4,
# критерий завершения рефакторинга)

Первый END-TO-END переход, где ВСЕ величины ВЫЧИСЛЕНЫ из
реальной функции потерь, а не переданы гипотезами:
F(x) = (x − a)², градиент F' = 2(x − a), шаг
x' = x − η·F'(x), реальное убывание F(x') < F(x) —
чистая арифметика, НОЛЬ эмпирических гипотез.
Форма: «модель → операция → ИЗМЕРЕННАЯ функция потерь →
доказанный результат операции» (аудит v13 §10 P5).
-/

namespace Hagi.Examples.QuadraticEndToEnd

/-- Квадратичная функция потерь F(x) = (x − a)². -/
def qLoss (a x : ℝ) : ℝ := (x - a) ^ 2

/-- Реальный градиент: 2(x − a). -/
theorem qGrad (a x : ℝ) : deriv (qLoss a) x = 2 * (x - a) := by
  have h1 : HasDerivAt (fun y : ℝ => y - a) 1 x :=
    (hasDerivAt_id x).sub_const a
  exact ((h1.pow 2).congr_deriv (by ring)).deriv

/-- Обучающий шаг: x' = x − η·F'(x) (вычислен из F). -/
def qStep (a x eta : ℝ) : ℝ := x - eta * (2 * (x - a))

/-- Постшаговая функция потерь — В ТОЧНОСТИ вычислена:
F(x') = (1 − 2η)²·(x − a)². -/
theorem qStep_loss_exact (a x eta : ℝ) :
    qLoss a (qStep a x eta) = (1 - 2 * eta) ^ 2 * (x - a) ^ 2 := by
  unfold qLoss qStep
  ring

/-- СКВОЗНОЕ УБЫВАНИЕ (уровень 1): при η ∈ (0, 1) и x ≠ a
реальный шаг СТРОГО уменьшает функцию потерь — вычислено,
не постулировано. -/
theorem qStep_descent (a x eta : ℝ) (heta : 0 < eta)
    (heta1 : eta < 1) (hx : x ≠ a) :
    qLoss a (qStep a x eta) < qLoss a x := by
  rw [qStep_loss_exact, qLoss]
  have hne : x - a ≠ 0 := sub_ne_zero.mpr hx
  have hsq : 0 < (x - a) ^ 2 := by positivity
  have hkey : ((1 - 2 * eta) - 1) * ((1 - 2 * eta) + 1) < 0 := by
    nlinarith
  have hfac : (1 - 2 * eta) ^ 2 < 1 := by
    nlinarith
  nlinarith [hsq, hfac]

/-- СХОДИМОСТЬ ПО ШАГАМ (уровень 2): t шагов дают
F(x_t) = (1−2η)^{2t}·F(x₀) — геометрическое убывание,
вычисленное точно. -/
theorem qIter_loss (a x eta : ℝ) (t : ℕ) :
    qLoss a ((List.range t).foldl (fun acc _ =>
      qStep a acc eta) x)
      = (1 - 2 * eta) ^ (2 * t) * (x - a) ^ 2 := by
  induction t with
  | zero =>
      simp only [List.range_zero, List.foldl_nil]
      norm_num [qLoss]
  | succ k ih =>
      have hfold : (List.range (k + 1)).foldl
          (fun acc _ => qStep a acc eta) x
          = qStep a ((List.range k).foldl
              (fun acc _ => qStep a acc eta) x) eta := by
        simp [List.range_succ, List.foldl_append]
      rw [hfold, qStep_loss_exact]
      have ih' := ih
      rw [qLoss] at ih'
      rw [ih']
      have hsplit : (1 - 2 * eta) ^ 2
          * ((1 - 2 * eta) ^ (2 * k) * (x - a) ^ 2)
          = (1 - 2 * eta) ^ (2 * (k + 1)) * (x - a) ^ 2 := by
        have hp : (2 * (k + 1) : ℕ) = 2 * k + 2 := by omega
        rw [hp, pow_add]
        ring
      rw [hsplit]

end Hagi.Examples.QuadraticEndToEnd
