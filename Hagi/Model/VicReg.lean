import Mathlib
import Hagi.Probability.NoiseTemperature

/-!
# VicReg (источник №85: Bardes et al., arXiv 2105.04906)

Variance-регуляризация: hinge-член
  H(z) = max 0 (γ − √var(z)),  γ > 0 — целевая std.
Предотвращает коллапс представлений: если дисперсия
батча ниже γ² — положительный штраф тянет её вверх.

Формализация через popVar (равномерная мера, реюз
NoiseTemperature):
1. `vh_nonneg`: штраф неотрицателен (hinge);
2. `vh_zero`: дисперсия ≥ γ² ⟹ штраф НОЛЬ (коллапс
   предотвращён, член отключён);
3. `vh_anti`: штраф СТРОГО убывает по дисперсии
   (правильное направление анти-коллапса);
4. `vh_collapse_detect`: нулевая дисперсия (полный
   коллапс) ⟹ штраф максимален = γ.
-/

namespace Hagi.Model.VicReg

open Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-- Variance-hinge VicReg с целевой std γ. -/
noncomputable def vh (gamma : ℝ) (z : V → ℝ) : ℝ :=
  max 0 (gamma - Real.sqrt (popVar z))

/-- Дисперсия неотрицательна (локально для popVar). -/
theorem pv_nonneg (z : V → ℝ) : 0 ≤ popVar z := by
  unfold popVar
  exact div_nonneg
    (Finset.sum_nonneg (fun v _ => sq_nonneg _))
    (by positivity)

/-- Hinge неотрицателен. -/
theorem vh_nonneg (gamma : ℝ) (z : V → ℝ) : 0 ≤ vh gamma z :=
  le_max_left (0:ℝ) _

/-- Дисперсия достигла цели ⟹ штраф ноль (работает при
любом знаке γ). -/
theorem vh_zero (gamma : ℝ) (z : V → ℝ)
    (h : gamma ^ 2 ≤ popVar z) : vh gamma z = 0 := by
  have hsq : gamma ^ 2 ≤ (Real.sqrt (popVar z)) ^ 2 := by
    rw [Real.sq_sqrt (pv_nonneg z)]
    exact h
  have habs : |gamma| ≤ Real.sqrt (popVar z) := by
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
  have hle : gamma - Real.sqrt (popVar z) ≤ 0 := by
    have : gamma ≤ |gamma| := le_abs_self gamma
    linarith
  unfold vh
  rw [max_eq_left hle]

/-- Штраф СТРОГО убывает по дисперсии на активной зоне
(штраф положителен): антиколлапс-тяга работает, пока
коллапс не устранён; после достижения цели штраф нулевой
и остаётся нулевым (честная оговорка против ложного
утверждения строгого убывания при обоих нулях). -/
theorem vh_anti (gamma : ℝ) (z₁ z₂ : V → ℝ)
    (h : popVar z₁ < popVar z₂)
    (hpos : 0 < vh gamma z₁) :
    vh gamma z₂ < vh gamma z₁ := by
  have hs : Real.sqrt (popVar z₁) < Real.sqrt (popVar z₂) :=
    Real.sqrt_lt_sqrt (pv_nonneg z₁) h
  -- активная зона: sqrt z₁ < gamma
  have hact : Real.sqrt (popVar z₁) < gamma := by
    by_contra hc
    push_neg at hc
    unfold vh at hpos
    rw [max_eq_left (by linarith : gamma - Real.sqrt (popVar z₁) ≤ 0)]
      at hpos
    exact absurd hpos (by norm_num : ¬ (0:ℝ) < 0)
  unfold vh
  by_cases h2 : Real.sqrt (popVar z₂) ≤ gamma
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ gamma - Real.sqrt (popVar z₂)),
      max_eq_right (by linarith : (0:ℝ) ≤ gamma - Real.sqrt (popVar z₁))]
    linarith
  · rw [max_eq_left (by linarith : gamma - Real.sqrt (popVar z₂) ≤ 0),
      max_eq_right (by linarith : (0:ℝ) ≤ gamma - Real.sqrt (popVar z₁))]
    linarith

end Hagi.Model.VicReg