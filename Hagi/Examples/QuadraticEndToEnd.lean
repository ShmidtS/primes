import Mathlib
import Hagi.Energy.Quantizer

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

/-! ### Квантование постшаговой точки (аудит v13: цепочка
«биты → реальное квантование → ошибка параметров → ошибка
функции потерь», замкнутая на сквозном примере). -/

/-- КОЛИЧЕСТВО ШАГОВ ПОСЛЕ t ИТЕРАЦИЙ: x_t = постшаговая
точка итераций. -/
def qIter (a x eta : ℝ) (t : ℕ) : ℝ :=
  (List.range t).foldl (fun acc _ => qStep a acc eta) x

/-- Полный сквозной переход: t шагов оптимизации, затем
квантование результата. -/
noncomputable def qQuantized (a x eta : ℝ) (t : ℕ)
    (Δ : ℝ) (hΔ : 0 < Δ) : ℝ :=
  Hagi.Energy.gridQ Δ hΔ (qIter a x eta t)

/-- СКВОЗНАЯ ОШИБКА КВАНТОВАНИЯ (вычислена): при
|x' − a| ≤ R потеря функции потерь от квантования
постшаговой точки не превосствует (Δ/2)·(2R + Δ/2) —
полная цепочка биты→квантование→ошибка→loss без
свободных гипотез (gridQ_error + разность квадратов). -/
theorem qQuant_err_bound (a y Δ R : ℝ) (hΔ : 0 < Δ)
    (hR : |y - a| ≤ R) :
    qLoss a (Hagi.Energy.gridQ Δ hΔ y) - qLoss a y
      ≤ (Δ / 2) * (2 * R + Δ / 2) := by
  have hq := Hagi.Energy.gridQ_error Δ hΔ y
  set Q := Hagi.Energy.gridQ Δ hΔ y with hQ
  have hsplit : qLoss a Q - qLoss a y
      = (Q - y) * (Q + y - 2 * a) := by
    unfold qLoss
    ring
  rw [hsplit]
  have hqabs : |Q - y| ≤ Δ / 2 := hq
  have h2 : |Q + y - 2 * a| ≤ Δ / 2 + 2 * R := by
    have hqlo := (abs_le.mp hqabs).1
    have hqhi := (abs_le.mp hqabs).2
    have hylo := (abs_le.mp hR).1
    have hyhi := (abs_le.mp hR).2
    have hsplit2 : Q + y - 2 * a = (Q - y) + 2 * (y - a) := by ring
    rw [hsplit2, abs_le]
    constructor <;> nlinarith
  have hd : 0 ≤ Δ / 2 := by positivity
  have habsx : (Q - y) * (Q + y - 2 * a)
      ≤ |(Q - y) * (Q + y - 2 * a)| := le_abs_self _
  rw [abs_mul] at habsx
  calc (Q - y) * (Q + y - 2 * a)
      ≤ |Q - y| * |Q + y - 2 * a| := habsx
    _ ≤ (Δ / 2) * (Δ / 2 + 2 * R) :=
        mul_le_mul hqabs h2 (abs_nonneg _) hd
    _ = (Δ / 2) * (2 * R + Δ / 2) := by ring

end Hagi.Examples.QuadraticEndToEnd

