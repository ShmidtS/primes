/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Принятие шага по Armijo / достаточному убыванию

Условие достаточного убывания для шага θ + α d по гладкой
цели: при первом порядке + L-члене и направленности
⟪g, d⟫ ≤ −c₁‖d‖² шаг уменьшает цель на c·α‖d‖² при
достаточно малом α. Форма контроля шага для
MDL-предобусловленного SafeQP-направления.

Никакого утверждения о глобальной сходимости: только
по-шаговое достаточное убывание при явных посылках.
-/

open Real InnerProductSpace

namespace Hagi.Armijo

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Достаточное убывание: при L-гладкой верхней оценке и
направленности d (⟪g, d⟫ ≤ −c₁‖d‖²) шаг αd уменьшает цель
не менее чем на (c₁ − Lα/2)·α·‖d‖²; при α ≤ c₁/L это
c·α‖d‖² с c := c₁ − Lα/2 ≥ c₁/2. -/
theorem armijo_sufficient_decrease (J : X → ℝ) (g d : X)
    (L c1 alpha : ℝ) (hL : 0 ≤ L) (hc1 : 0 < c1) (halpha : 0 < alpha)
    (hdir : ⟪g, d⟫_ℝ ≤ -(c1 * ‖d‖ ^ 2))
    (hsmooth : J (0 + alpha • d) ≤ J 0 + ⟪g, alpha • d⟫_ℝ
      + L / 2 * ‖alpha • d‖^2) :
    J (0 + alpha • d) ≤ J 0 - (c1 - L * alpha / 2) * alpha * ‖d‖^2 := by
  have hab : 0 ≤ alpha := halpha.le
  have hnormsq : ‖alpha • d‖^2 = alpha^2 * ‖d‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hab]
    ring
  have hinnersmul : ⟪g, alpha • d⟫_ℝ = alpha * ⟪g, d⟫_ℝ :=
    real_inner_smul_right g d alpha
  calc J (0 + alpha • d)
      ≤ J 0 + ⟪g, alpha • d⟫_ℝ + L / 2 * ‖alpha • d‖^2 := hsmooth
    _ = J 0 + alpha * ⟪g, d⟫_ℝ + L / 2 * (alpha^2 * ‖d‖^2) := by
          rw [hinnersmul, hnormsq]
    _ ≤ J 0 + alpha * (-(c1 * ‖d‖^2)) + L / 2 * (alpha^2 * ‖d‖^2) := by
          have hmono : alpha * ⟪g, d⟫_ℝ ≤ alpha * (-(c1 * ‖d‖^2)) :=
            mul_le_mul_of_nonneg_left hdir hab
          linarith
    _ = J 0 - (c1 - L * alpha / 2) * alpha * ‖d‖^2 := by
          have hq : (c1 - L * alpha / 2) * alpha * ‖d‖^2
              = c1 * (alpha * ‖d‖^2) - L / 2 * (alpha^2 * ‖d‖^2) := by
            field_simp
          have : alpha * -(c1 * ‖d‖^2) = -(c1 * (alpha * ‖d‖^2)) := by ring
          linarith [this]

/-- Явный размер шага: при α ≤ c₁/L убывание не менее
(c₁/2)·α·‖d‖². -/
theorem armijo_step_size (J : X → ℝ) (g d : X)
    (L c1 alpha : ℝ) (hL : 0 ≤ L) (hc1 : 0 < c1) (halpha : 0 < alpha)
    (hsize : alpha ≤ c1 / L)
    (hdir : ⟪g, d⟫_ℝ ≤ -(c1 * ‖d‖ ^ 2))
    (hsmooth : J (0 + alpha • d) ≤ J 0 + ⟪g, alpha • d⟫_ℝ
      + L / 2 * ‖alpha • d‖^2) :
    J (0 + alpha • d) ≤ J 0 - (c1 / 2) * alpha * ‖d‖^2 := by
  have hLpos : 0 < L := by
    rcases eq_or_lt_of_le hL with hL0 | hLpos
    · exfalso
      rw [← hL0] at hsize
      simp [div_zero] at hsize
      linarith
    · exact hLpos
  have h := armijo_sufficient_decrease J g d L c1 alpha hL hc1 halpha
    hdir hsmooth
  have hLA : L * alpha ≤ c1 := by
    rw [le_div_iff₀ hLpos] at hsize
    linarith
  have hhalf : c1 - L * alpha / 2 ≥ c1 / 2 := by linarith
  have hsq : (c1 - L * alpha / 2) * ‖d‖^2 ≥ (c1 / 2) * ‖d‖^2 :=
    mul_le_mul_of_nonneg_right hhalf (by positivity)
  have hab : 0 ≤ alpha := halpha.le
  calc J (0 + alpha • d)
      ≤ J 0 - alpha * ((c1 - L * alpha / 2) * ‖d‖^2) := by
          have : alpha * (c1 - L * alpha / 2) * ‖d‖^2
              = alpha * ((c1 - L * alpha / 2) * ‖d‖^2) := by ring
          linarith [this]
    _ ≤ J 0 - alpha * ((c1 / 2) * ‖d‖^2) := by
          have hle : alpha * ((c1 / 2) * ‖d‖^2)
              ≤ alpha * ((c1 - L * alpha / 2) * ‖d‖^2) :=
            mul_le_mul_of_nonneg_left hsq hab
          linarith
    _ = J 0 - (c1 / 2) * alpha * ‖d‖^2 := by ring

end Hagi.Armijo
