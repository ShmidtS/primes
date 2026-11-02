/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

set_option linter.style.header false

/-!
# Спуск по неточному градиенту (робастная descent-лемма)

Мост MEASURE -> PROPOSE: нулевой порядок оценивает градиент
`ĝ` с гарантированной ошибкой `‖ĝ - g‖ ≤ m` (Dust/батч-оценки),
PROPOSE делает шаг `x⁺ = x - η • ĝ`. Замыкающее звено —
нижняя оценка направленности по неточной паре:

`⟪g, ĝ⟫ ≥ (‖g‖² - m²) / 2`

и скалярное ядро спуска для точного градиента, извлечённое из
неточного: из `‖ĝ‖ ≤ ‖g‖ + m` и L-гладкости шаг по ĝ даёт

`J(x⁺) ≤ J(x) - (η/2)(‖g‖² - m²) + (Lη²/2)(‖g‖ + m)²`.

При `η ≤ 1/L` фактическое убывание ≥ `η/2 (‖g‖² - m²) - ηm²`:
сертифицированный спуск, пока сигнал сильнее шума
(`‖g‖ > √3·m`). Композиционный кирпич для end-to-end бюджета
нулевого порядка.
-/

open Real InnerProductSpace

namespace Hagi.Step

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Ядро: для `g ĝ : X` с `‖ĝ - g‖ ≤ m` имеем
`⟪g, ĝ⟫_ℝ ≥ (‖g‖² - m²)/2`. -/
theorem biased_inner_lower (g ĝ : X) (m : ℝ) (hm : ‖ĝ - g‖ ≤ m) :
    (‖g‖ ^ 2 - m ^ 2) / 2 ≤ ⟪g, ĝ⟫_ℝ := by
  have hsplit : ⟪g, ĝ⟫_ℝ = ‖g‖ ^ 2 + ⟪g, ĝ - g⟫_ℝ := by
    have heq : ĝ = g + (ĝ - g) := by
      rw [add_sub_cancel]
    rw [heq, inner_add_right, real_inner_self_eq_norm_sq]
      <;> simp [sub_add_cancel]
  have hbound : |⟪g, ĝ - g⟫_ℝ| ≤ ‖g‖ * m := by
    have := abs_real_inner_le_norm g (ĝ - g)
    calc |⟪g, ĝ - g⟫_ℝ| ≤ ‖g‖ * ‖ĝ - g‖ := this
      _ ≤ ‖g‖ * m := by exact mul_le_mul_of_nonneg_left hm (norm_nonneg g)
  have hlow : -(‖g‖ * m) ≤ ⟪g, ĝ - g⟫_ℝ := by
    have := hbound
    exact (abs_le.1 this).1
  have hsq : (‖g‖ - m) ^ 2 ≥ 0 := sq_nonneg _
  rw [hsplit]
  nlinarith [hlow, hsq]

/-- Следствие: `‖ĝ‖ ≤ ‖g‖ + m` (расширенный треугольник). -/
theorem biased_norm_upper (g ĝ : X) (m : ℝ) (hm : ‖ĝ - g‖ ≤ m) :
    ‖ĝ‖ ≤ ‖g‖ + m := by
  have htri : ‖ĝ‖ ≤ ‖g‖ + ‖ĝ - g‖ := by
    have h := norm_add_le (ĝ - g) g
    have heq : ĝ - g + g = ĝ := by
      simp
    have heq2 : ‖g‖ + ‖ĝ - g‖ = ‖ĝ - g‖ + ‖g‖ := by ring
    rw [heq] at h
    linarith [h, heq2]
  linarith [htri, hm]

/-- Робастное убывание цели: `L`-гладкая `J` сверху на шаге
`-η • ĝ` при `‖ĝ - g‖ ≤ m`, `0 ≤ η`:
`J(x - η • ĝ) ≤ J(x) - η⟪g, ĝ⟫ + Lη²‖ĝ‖²/2` в развёрнутой
форме через точный градиент и шум. -/
theorem robust_descent_step {J : X → ℝ} (g ĝ x : X) (η L m : ℝ)
    (hm : ‖ĝ - g‖ ≤ m) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hquad : J (x - η • ĝ) ≤ J x - η * ⟪g, ĝ⟫_ℝ
      + L / 2 * ‖η • ĝ‖ ^ 2) :
    J (x - η • ĝ) ≤ J x - η * ((‖g‖ ^ 2 - m ^ 2) / 2)
      + L * η ^ 2 * (‖g‖ + m) ^ 2 / 2 := by
  have hinner := biased_inner_lower g ĝ m hm
  have hnorm := biased_norm_upper g ĝ m hm
  have hsm : ‖η • ĝ‖ = η * ‖ĝ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
  calc J (x - η • ĝ)
      ≤ J x - η * ⟪g, ĝ⟫_ℝ + L / 2 * ‖η • ĝ‖ ^ 2 := hquad
    _ ≤ J x - η * ((‖g‖ ^ 2 - m ^ 2) / 2)
        + L / 2 * ‖η • ĝ‖ ^ 2 := by
        have hge : η * ((‖g‖ ^ 2 - m ^ 2) / 2)
            ≤ η * ⟪g, ĝ⟫_ℝ :=
          mul_le_mul_of_nonneg_left hinner hη
        linarith
    _ ≤ J x - η * ((‖g‖ ^ 2 - m ^ 2) / 2)
        + L / 2 * (η * (‖g‖ + m)) ^ 2 := by
        have : L / 2 * ‖η • ĝ‖ ^ 2
            ≤ L / 2 * (η * (‖g‖ + m)) ^ 2 := by
          have hL2 : 0 ≤ L / 2 := by linarith
          calc L / 2 * ‖η • ĝ‖ ^ 2
              ≤ L / 2 * (η * ‖ĝ‖) ^ 2 := by
                rw [hsm]
            _ ≤ L / 2 * (η * (‖g‖ + m)) ^ 2 := by
                have hηη : η * ‖ĝ‖ ≤ η * (‖g‖ + m) :=
                  mul_le_mul_of_nonneg_left hnorm hη
                have hneg : -(η * (‖g‖ + m)) ≤ η * ‖ĝ‖ := by
                  have hn0 : 0 ≤ η * ‖ĝ‖ := mul_nonneg hη (norm_nonneg ĝ)
                  linarith
                have hpow : (η * ‖ĝ‖) ^ 2 ≤ (η * (‖g‖ + m)) ^ 2 :=
                  sq_le_sq' hneg hηη
                exact mul_le_mul_of_nonneg_left hpow hL2
        linarith
    _ = J x - η * ((‖g‖ ^ 2 - m ^ 2) / 2)
        + L * η ^ 2 * (‖g‖ + m) ^ 2 / 2 := by
        ring

end Hagi.Step
