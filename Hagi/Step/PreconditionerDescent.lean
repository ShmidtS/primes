/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Спуск через предобусловленное направление

Условия, при которых предобусловленное направление
`u = P(g)` (Muon-подобная ортогонализация, любой
предобуславливатель) остаётся направлением спуска для
гладкой цели, и шаг `θ − α·u` уменьшает цель.

Гладкость входит явной посылкой (первый порядок + L-член),
как во всём Step-слое. Никакое утверждение о конкретном
оптимизаторе (Muon, AdamW) не делается: P абстрактен,
коэрцитивность `⟪g, u⟫ ≥ μ‖u‖²` — измеряемая посылка.
-/

open Real InnerProductSpace

namespace Hagi.PreconditionerDescent

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Главная теорема: при коэрцитивности направления
(⟪g, u⟫_ℝ ≥ μ‖u‖², μ > 0) и L-гладкости цели шаг θ − αu
уменьшает цель на α(μ − Lα/2)‖u‖²; при α < 2μ/L убывание
строгое. -/
theorem preconditioned_descent (J : X → ℝ) (g u : X) (L mu alpha : ℝ)
    (hL : 0 ≤ L) (hmu : 0 < mu) (halpha : 0 < alpha)
    (halpha2 : alpha < 2 * mu / L)
    (hcoerc : mu * ‖u‖^2 ≤ ⟪g, u⟫_ℝ)
    (hsmooth : J (0 - alpha • u) ≤ J 0 + ⟪g, 0 - alpha • u⟫_ℝ
        + L / 2 * ‖0 - alpha • u‖^2) :
    J (0 - alpha • u) ≤ J 0 - alpha * (mu - L * alpha / 2) * ‖u‖^2 := by
  have hab : 0 ≤ alpha := halpha.le
  have hstep : (0:X) - alpha • u = -(alpha • u) := by simp
  have hnormsq : ‖(0:X) - alpha • u‖^2 = alpha^2 * ‖u‖^2 := by
    rw [hstep, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hab]
    ring
  have hinnersub : ⟪g, (0:X) - alpha • u⟫_ℝ = -(alpha * ⟪g, u⟫_ℝ) := by
    rw [hstep, inner_neg_right, inner_smul_right]
  calc J (0 - alpha • u)
      ≤ J 0 + ⟪g, (0:X) - alpha • u⟫_ℝ
          + L / 2 * ‖(0:X) - alpha • u‖^2 := hsmooth
    _ = J 0 - alpha * ⟪g, u⟫_ℝ + L / 2 * (alpha^2 * ‖u‖^2) := by
          rw [hinnersub, hnormsq]; ring
    _ ≤ J 0 - alpha * (mu * ‖u‖^2) + L / 2 * (alpha^2 * ‖u‖^2) := by
          have hmono : alpha * ⟪g, u⟫_ℝ ≥ alpha * (mu * ‖u‖^2) :=
            mul_le_mul_of_nonneg_left hcoerc hab
          linarith
    _ = J 0 - alpha * (mu - L * alpha / 2) * ‖u‖^2 := by
          have hq : alpha * (mu - L * alpha / 2) * ‖u‖^2
              = alpha * (mu * ‖u‖^2) - L / 2 * (alpha^2 * ‖u‖^2) := by
            field_simp
          linarith

/-- Достаточное условие на α в явном виде: любое
0 < α ≤ μ/L даёт убывание не хуже (μ/2)·α·‖u‖². -/
theorem preconditioned_step_size (J : X → ℝ) (g u : X) (L mu alpha : ℝ)
    (hL : 0 ≤ L) (hmu : 0 < mu) (halpha : 0 < alpha)
    (hsize : alpha ≤ mu / L)
    (hcoerc : mu * ‖u‖^2 ≤ ⟪g, u⟫_ℝ)
    (hsmooth : J (0 - alpha • u) ≤ J 0 + ⟪g, 0 - alpha • u⟫_ℝ
        + L / 2 * ‖0 - alpha • u‖^2) :
    J (0 - alpha • u) ≤ J 0 - (mu / 2) * alpha * ‖u‖^2 := by
  have hab : 0 ≤ alpha := halpha.le
  have hLpos : 0 < L := by
    rcases eq_or_lt_of_le hL with hL0 | hLpos
    · exfalso
      rw [← hL0] at hsize
      simp [div_zero] at hsize
      linarith
    · exact hLpos
  have h2 : alpha < 2 * mu / L := by
    have hpos : 0 < mu / L := div_pos hmu hLpos
    have hmuL : mu / L < 2 * (mu / L) :=
      lt_mul_of_one_lt_left hpos one_lt_two
    have hring : 2 * mu / L = 2 * (mu / L) := by ring
    rw [hring]
    linarith [hmuL]
  have h := preconditioned_descent J g u L mu alpha hL hmu halpha h2
    hcoerc hsmooth
  have hLA : L * alpha ≤ mu := by
    rw [le_div_iff₀ hLpos] at hsize
    linarith
  have hhalf : mu - L * alpha / 2 ≥ mu / 2 := by linarith
  have hsq : (mu - L * alpha / 2) * ‖u‖^2 ≥ (mu / 2) * ‖u‖^2 := by
    exact mul_le_mul_of_nonneg_right hhalf (by positivity)
  have hn : 0 ≤ ‖u‖^2 := by positivity
  calc J (0 - alpha • u)
      ≤ J 0 - alpha * (mu - L * alpha / 2) * ‖u‖^2 := h
    _ ≤ J 0 - alpha * ((mu / 2) * ‖u‖^2) := by
          have hle : alpha * ((mu / 2) * ‖u‖^2)
              ≤ alpha * ((mu - L * alpha / 2) * ‖u‖^2) :=
            mul_le_mul_of_nonneg_left hsq hab
          linarith
    _ = J 0 - (mu / 2) * alpha * ‖u‖^2 := by ring

end Hagi.PreconditionerDescent
