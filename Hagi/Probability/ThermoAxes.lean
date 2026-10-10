/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.NoiseTemperature

set_option linter.style.header false

/-!
# ThermoAxes — эквивалентность осей охлаждения: LR-decay ⟺
batch-increase

Формализация ядра «Don't Decay the Learning Rate, Increase
the Batch Size» (arXiv:1711.00489, Smith et al.; план §2,
терм-ось): убывание LR и рост batch — ОДНА математика на
двух осях. Шумовой бюджет шага пропорционален σ²η² (LR-ось)
или σ²/B (batch-ось); при перекрёстном соответствии

  η₀ = 1/√B₀,  r = 1/√c  (⟺ r²·c = 1)

последовательности шумовых вкладов СОВПАДАЮТ ПОЧЛЕННО, а
значит равны и полные бюджеты охлаждения.

Доказано:
* `noise_axes_coincide`: при r²·c = 1 и η₀²·B₀ = 1/B₀
  вклады η₀²·r^{2t} и 1/(B₀·c^t) равны для каждого t —
  оси — одна и та же последовательность;
* `noise_budget_axes_equal`: конечные суммы шумовых бюджетов
  равны (обе оси покупают одно и то же охлаждение);
* интерпретация: выбор оси — экономика (batch растёт —
  дороже шаг, дешевле конвергенция траектории), не
  математика.

Дополнение к anneal_by_batch: batch-ось покупает то же
охлаждение БЕЗ сжатия шага.
-/

open Finset Real

namespace Hagi.ThermoAxes

/-- Почленное совпадение осей: при r²·c = 1 и η₀²·B₀ = 1/B₀
шумовой вклад LR-оси η₀²·r^{2t} равен вкладу batch-оси
1/(B₀·c^t) для каждого шага t. -/
theorem noise_axes_coincide (eta0 r B0 c : ℝ) (t : ℕ)
    (hr2c : r ^ 2 * c = 1) (heta : eta0 ^ 2 * B0 = 1)
    (hB0 : B0 ≠ 0) :
    eta0 ^ 2 * r ^ (2 * t) = 1 / (B0 * c ^ t) := by
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hr2c
    exact absurd hr2c (by simp)
  have hrpow : r ^ (2 * t) = 1 / c ^ t := by
    have h1 : (r ^ 2) ^ t * c ^ t = 1 := by
      calc (r ^ 2) ^ t * c ^ t = (r ^ 2 * c) ^ t := by rw [mul_pow]
        _ = 1 ^ t := by rw [hr2c]
        _ = 1 := one_pow _
    rw [pow_mul]
    exact (eq_div_iff (pow_ne_zero t hc)).mpr h1
  have heta2 : eta0 ^ 2 = 1 / B0 := by
    rw [eq_div_iff hB0] at *
    linarith
  rw [hrpow, heta2]
  field_simp

/-- Равенство полных шумовых бюджетов: сумма вкладов LR-оси
(η₀²r^{2t}) равна сумме вкладов batch-оси (1/(B₀c^t)) на
любом горизонте — оси охлаждения математически
эквивалентны. -/
theorem noise_budget_axes_equal (eta0 r B0 c : ℝ) (n : ℕ)
    (hr2c : r ^ 2 * c = 1) (heta : eta0 ^ 2 * B0 = 1)
    (hB0 : B0 ≠ 0) :
    ∑ t ∈ Finset.range n, eta0 ^ 2 * r ^ (2 * t)
      = ∑ t ∈ Finset.range n, 1 / (B0 * c ^ t) := by
  exact Finset.sum_congr rfl fun t _ =>
    noise_axes_coincide eta0 r B0 c t hr2c heta hB0

end Hagi.ThermoAxes
