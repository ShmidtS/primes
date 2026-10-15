/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
set_option linter.style.header false

open Finset Real Set

/-!
# Хорда экспоненты (R498)

Выпуклость e^{r*y} через ConvexOn.comp_linearMap даёт хорду:
e^{r*x} <= ((b-x)/(b-a)) e^{r a} + ((x-a)/(b-a)) e^{r b} для
x in [a,b], a < b. Базовый кирпич Hoeffding/Bennett CGF-оценок.
Процесс-урок: приоритет оператора `•` выше `/` — веса в smul
нужны в скобках: `((b - x) / (b - a)) • a`.
-/
theorem exp_chord {a b x : ℝ} (hab : a < b) (hxa : a ≤ x) (hxb : x ≤ b)
    (r : ℝ) :
    Real.exp (r * x)
      ≤ (b - x) / (b - a) * Real.exp (r * a)
        + (x - a) / (b - a) * Real.exp (r * b) := by
  have hc0 : ConvexOn ℝ (⇑(LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) r) ⁻¹' univ)
      (Real.exp ∘ ⇑(LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) r)) :=
    convexOn_exp.comp_linearMap (LinearMap.smulRight (1 : ℝ →ₗ[ℝ] ℝ) r)
  have hc : ConvexOn ℝ univ (fun y => Real.exp (r * y)) := by
    refine hc0.congr (fun y _ => ?_)
    simp [LinearMap.smulRight]
    ring
  have hmem1 : (a:ℝ) ∈ (univ : Set ℝ) := trivial
  have hmem2 : (b:ℝ) ∈ (univ : Set ℝ) := trivial
  have hw1 : (0:ℝ) ≤ (b - x) / (b - a) := by positivity
  have hw2 : (0:ℝ) ≤ (x - a) / (b - a) := by positivity
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    rw [← add_div]
    have hnum : b - x + (x - a) = b - a := by ring
    rw [hnum]
    exact div_self (by linarith : b - a ≠ 0)
  have hconv := hc.2 hmem1 hmem2 hw1 hw2 hsum
  -- hconv : exp (r * (w1 • a + w2 • b)) <= w1 • exp (r a) + w2 • exp (r b)
  have hcombo : ((b - x) / (b - a)) • (a:ℝ) + ((x - a) / (b - a)) • (b:ℝ) = x := by
    have hne : b - a ≠ 0 := by linarith
    rw [smul_eq_mul, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    rw [show (b - x) * a + (x - a) * b = (b - a) * x from by ring]
    exact mul_div_cancel_left₀ x hne
  rw [hcombo] at hconv
  simpa using hconv
