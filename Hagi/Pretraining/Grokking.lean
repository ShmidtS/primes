import Mathlib

/-!
# Grokking: разделение временных шкал при weight decay

Источник №9: Boursier, Pesme, Dragomir (NeurIPS 2025),
"Interpolation followed by Riemannian Norm Minimisation".

Gradient flow с малым weight decay lam имеет двухфазную
динамику: быстрое схождение к многообразию критических точек,
затем медленный дрейф нормы на времени O(1/lam). Формализовано
ядро механизма: пост-сходимость траектория следует w' = -lamw
(дрейф нормы), норма экспоненциально убывает как e^{-lamt},
время полужизни ln 2/lam → ∞ при lam → 0. Отсюда grokking:
время обобщения (норма-управляемое) сколь угодно позже
времени обучения (фиксированного) при малом lam.
-/

namespace Hagi.Pretraining.Grokking

open Real

/-- РЕШЕНИЕ ДРЕЙФА: w(t) = w₀·e^{-lamt} — траектория
пост-интерполяционного дрейфа (критическое многообразие:
∇F = 0, остаётся только weight decay). -/
theorem drift_solution (lam w0 t : ℝ) :
    (fun s => w0 * exp (-lam * s)) t = w0 * exp (-lam * t) := rfl

/-- ПРОИЗВОДНАЯ ДРЕЙФА: w' = -lam·w вдоль дрейфа —
решение линеаризованного градиентного потока на
критическом многообразии. -/
theorem drift_hasDeriv (lam w0 t : ℝ) :
    HasDerivAt (fun s => w0 * exp (-lam * s))
      (-lam * (w0 * exp (-lam * t))) t := by
  have h1 : HasDerivAt (fun s => -lam * s) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have h2 := (Real.hasDerivAt_exp _).comp t h1
  have h3 : HasDerivAt (fun s => w0 * exp (-lam * s))
      (w0 * (exp (-lam * t) * (-lam))) t := h2.const_mul w0
  convert h3 using 1
  ring

/-- МОНОТОННЫЙ СПАД НОРМЫ: при lam > 0 норма дрейфа
невозрастает — медленная релаксация к минимальной норме
(риаманов дрейф ℓ₂-нормы из источника). -/
theorem drift_norm_nondecreasing (lam w0 t : ℝ) (hlam : 0 < lam) (ht : 0 ≤ t) :
    |w0 * exp (-lam * t)| ≤ |w0| := by
  have hexp : 0 ≤ exp (-lam * t) := exp_nonneg _
  have hexp_le : exp (-lam * t) ≤ 1 := by
    have h := exp_le_exp.mpr (show -lam * t ≤ 0 by nlinarith)
    simpa using h
  rw [abs_mul, abs_of_nonneg hexp]
  calc |w0| * exp (-lam * t)
      ≤ |w0| * 1 := mul_le_mul_of_nonneg_left hexp_le (abs_nonneg w0)
    _ = |w0| := mul_one _

/-- ПОЛУЖИЗНЬ НОРМЫ: |w(ln 2/lam)| = |w₀|/2 — характерное время
дрейфа равно (ln 2)/lam, т.е. Θ(1/lam). -/
theorem drift_half_life (lam w0 : ℝ) (hlam : 0 < lam) :
    |w0 * exp (-lam * ((log 2) / lam))| = |w0| / 2 := by
  have hmul : -lam * ((log 2) / lam) = -(log 2) := by
    field_simp
  have hval : exp (-lam * ((log 2) / lam)) = 1 / 2 := by
    rw [hmul, exp_neg, exp_log two_pos]
    norm_num
  have hw : w0 * exp (-lam * ((log 2) / lam)) = w0 / 2 := by
    rw [hval, mul_one_div]
  rw [hw]
  simp [abs_div]

/-- РАЗДЕЛЕНИЕ ШКАЛ (grokking-ядро): для любого быстрого
времени обучения T_fast > 0 найдётся lam > 0 такое, что
время полужизни нормы (ln 2)/lam строго больше T_fast·k —
обобщение задержано сколь угодно относительно обучения
при достаточно малом weight decay. -/
theorem grokking_timescale_separation (T_fast k : ℝ)
    (hT : 0 < T_fast) (hk : 0 < k) :
    ∃ lam > 0, (log 2) / lam > k * T_fast := by
  refine ⟨(log 2) / (k * T_fast + 1), ?_, ?_⟩
  · have h1 : 0 < log 2 := by positivity
    have h2 : 0 < k * T_fast + 1 := by nlinarith
    exact div_pos h1 h2
  · have h1 : 0 < log 2 := by positivity
    have h2 : 0 < k * T_fast + 1 := by nlinarith
    field_simp
    nlinarith

open Real intervalIntegral

/-- ДЛИНА ПУТИ ДРЕЙФА ОГРАНИЧЕНА: полная вариация
пост-интерполяционного дрейфа на [0,t] не превосходит
начальную норму — риманов дрейф ℓ₂-нормы имеет конечный
«бюджет движения» |w₀|, независимо от t. -/
theorem drift_total_variation (lam w0 : ℝ) (hlam : 0 < lam) (t : ℝ) :
    ∫ x in (0)..t, |(-lam) * (w0 * exp (-lam * x))| ≤ |w0| := by
  have habs : ∀ x : ℝ, |(-lam) * (w0 * exp (-lam * x))|
      = lam * |w0| * exp (-lam * x) := by
    intro x
    calc |(-lam) * (w0 * exp (-lam * x))|
        = |(-lam)| * |w0 * exp (-lam * x)| := abs_mul _ _
      _ = lam * (|w0| * |exp (-lam * x)|) := by
          rw [abs_of_neg (show (0:ℝ) > -lam by nlinarith), abs_mul]
          ring
      _ = lam * |w0| * exp (-lam * x) := by
          rw [abs_of_nonneg (exp_nonneg _)]
          ring
  have heq := intervalIntegral.integral_congr
    (a := 0) (b := t) (μ := MeasureTheory.volume)
    (f := fun x => |(-lam) * (w0 * exp (-lam * x))|)
    (fun x _ => habs x)
  rw [heq, intervalIntegral.integral_const_mul]
  -- ∫₀^t e^{−λx} dx = (1 − e^{−λt})/λ  через замену u = −λx
  have hint : ∫ x in (0)..t, exp (-lam * x)
      = (1 - exp (-lam * t)) / lam := by
    have hcom : ∀ x : ℝ, exp (-lam * x) = exp (x * (-lam)) :=
      fun x => by congr 1; ring
    have he := intervalIntegral.integral_congr
      (a := 0) (b := t) (μ := MeasureTheory.volume)
      (f := fun x => exp (-lam * x)) (fun x _ => hcom x)
    rw [he, integral_comp_mul_right exp
      (by nlinarith : (-lam : ℝ) ≠ 0), integral_exp]
    rw [zero_mul, mul_neg, smul_eq_mul, exp_zero]
    field_simp
    ring
  rw [hint]
  have hexp : 0 ≤ exp (-lam * t) := exp_nonneg _
  have hle : 1 - exp (-lam * t) ≤ 1 := by nlinarith
  have hcancel : lam * |w0| * ((1 - exp (-lam * t)) / lam)
      = |w0| * (1 - exp (-lam * t)) := by
    field_simp
  rw [hcancel]
  calc |w0| * (1 - exp (-lam * t))
      ≤ |w0| * 1 := mul_le_mul_of_nonneg_left hle (abs_nonneg w0)
    _ = |w0| := mul_one _

end Hagi.Pretraining.Grokking
