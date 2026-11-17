/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/

import Mathlib


set_option linter.style.header false

/-!
# Foundations.Chord — хорда exp и cosh-граница

Чистые calculus-леммы без Hagi-зависимостей: хорда exp на
[a,b] (`exp_chord_ab`) и квадратичная cosh-граница
(`log_cosh_le`).
-/

open Finset Real

namespace Hagi.Foundations

/-- Canonical r-scaled chord (the generic form behind the
Hoeffding/Bennett CGF brick): convexity of `y ↦ exp (r * y)` gives
`exp (r * x) ≤ (b-x)/(b-a) * exp (r*a) + (x-a)/(b-a) * exp (r*b)`
for `x ∈ [a, b]`, `a < b`, any `r`. All other project copies
(`Probability.ExpChord.exp_chord`, the `r = 1` special case
`exp_chord_ab`, the symmetric `Ensemble.Hoeffding.exp_chord`)
delegate here. -/
theorem exp_chord_r {a b x : ℝ} (hab : a < b) (hxa : a ≤ x) (hxb : x ≤ b)
    (r : ℝ) :
    Real.exp (r * x)
      ≤ (b - x) / (b - a) * Real.exp (r * a)
        + (x - a) / (b - a) * Real.exp (r * b) := by
  have hc0 : ConvexOn ℝ (⇑(LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) r) ⁻¹' Set.univ)
      (Real.exp ∘ ⇑(LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) r)) :=
    convexOn_exp.comp_linearMap (LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) r)
  have hc : ConvexOn ℝ Set.univ (fun y => Real.exp (r * y)) := by
    refine hc0.congr (fun y _ => ?_)
    simp [LinearMap.smulRight]
    ring
  have hmem1 : (a:ℝ) ∈ (Set.univ : Set ℝ) := trivial
  have hmem2 : (b:ℝ) ∈ (Set.univ : Set ℝ) := trivial
  have hw1 : (0:ℝ) ≤ (b - x) / (b - a) := by positivity
  have hw2 : (0:ℝ) ≤ (x - a) / (b - a) := by positivity
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    rw [← add_div]
    have hnum : b - x + (x - a) = b - a := by ring
    rw [hnum]
    exact div_self (by linarith : b - a ≠ 0)
  have hconv := hc.2 hmem1 hmem2 hw1 hw2 hsum
  have hcombo : ((b - x) / (b - a)) • (a:ℝ) + ((x - a) / (b - a)) • (b:ℝ) = x := by
    have hne : b - a ≠ 0 := by linarith
    rw [smul_eq_mul, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    rw [show (b - x) * a + (x - a) * b = (b - a) * x from by ring]
    exact mul_div_cancel_left₀ x hne
  rw [hcombo] at hconv
  simpa using hconv


/-- Выпуклость exp даёт поточечную мажорацию хордой на
`[a, b]`: при `a < b`, `a ≤ x ≤ b` выполнено
`exp x ≤ (b - x) / (b - a) * exp a + (x - a) / (b - a) * exp b`. -/
theorem exp_chord_ab (a b x : ℝ) (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.exp x ≤ (b - x) / (b - a) * Real.exp a
      + (x - a) / (b - a) * Real.exp b := by
  have h := exp_chord_r hab hax hxb 1
  simpa [one_mul] using h

/-- Квадратичная cosh-граница: `log (cosh M) ≤ M ^ 2 / 2`. -/
theorem log_cosh_le (M : ℝ) : Real.log (Real.cosh M) ≤ M ^ 2 / 2 := by
  have hpos : 0 < Real.cosh M := Real.cosh_pos M
  have hlog : Real.log (Real.cosh M) ≤ Real.log (Real.exp (M ^ 2 / 2)) :=
    Real.log_le_log hpos (cosh_le_exp_half_sq M)
  rw [Real.log_exp] at hlog
  exact hlog

end Hagi.Foundations
