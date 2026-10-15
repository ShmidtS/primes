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

/-! ## Шаг Хёффдинга: взвешенное хордовое MGF (R499)

E_q e^{r(g - mu)} <= ((b-mu)/(b-a)) e^{r(a-mu)} + ((mu-a)/(b-a)) e^{r(b-mu)}:
хорда R498 суммируется с весами q, аффинные веса усредняются к
барицентру (sum q (b - g) = b - mu, sum q (g - a) = mu - a),
константы выносятся из сумм через mul_sum-коммутационный simp.
-/
theorem hoeffding_chord_mgf {V : Type*} [Fintype V] [Nonempty V]
    (q g : V → ℝ) (a b : ℝ)
    (hq : ∀ v, 0 < q v) (hq1 : ∑ v : V, q v = 1)
    (hlo : ∀ v, a ≤ g v) (hhi : ∀ v, g v ≤ b) (hab : a < b) (r : ℝ) :
    ∑ v : V, q v * Real.exp (r * (g v - ∑ x : V, q x * g x))
      ≤ (b - ∑ x : V, q x * g x) / (b - a) * Real.exp (r * (a - ∑ x : V, q x * g x))
        + (∑ x : V, q x * g x - a) / (b - a)
          * Real.exp (r * (b - ∑ x : V, q x * g x)) := by
  set μ := ∑ x : V, q x * g x with hμd
  -- per-vertex chord on [a - mu, b - mu]
  have hdev : ∀ v : V, (a - μ) ≤ (g v - μ) ∧ (g v - μ) ≤ (b - μ) := by
    intro v
    constructor <;> linarith [hlo v, hhi v]
  have hlt : a - μ < b - μ := by linarith
  -- sum the chord with weights
  have hchord : ∀ v : V, q v * Real.exp (r * (g v - μ))
      ≤ q v * ((b - μ - (g v - μ)) / (b - μ - (a - μ)) * Real.exp (r * (a - μ))
        + (g v - μ - (a - μ)) / (b - μ - (a - μ)) * Real.exp (r * (b - μ))) :=
    fun v => mul_le_mul_of_nonneg_left
      (exp_chord (a := a - μ) (b := b - μ) hlt (hdev v).1 (hdev v).2 r)
      (le_of_lt (hq v))
  refine le_trans (Finset.sum_le_sum (fun v _ => hchord v)) ?_
  · -- sum of weights times chord = RHS (weights sum to 1)
    have h1 : ∑ v : V, q v * (((b - μ) - (g v - μ)) / (b - μ - (a - μ))
          * Real.exp (r * (a - μ))
        + ((g v - μ) - (a - μ)) / (b - μ - (a - μ)) * Real.exp (r * (b - μ)))
        = ∑ v : V, q v * ((b - g v) / (b - a) * Real.exp (r * (a - μ))
          + (g v - a) / (b - a) * Real.exp (r * (b - μ))) := by
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have hden : b - μ - (a - μ) = b - a := by ring
      rw [hden]
      ring
    rw [h1]
    -- now average the affine weights
    have hwavg1 : ∑ v : V, q v * ((b - g v) / (b - a))
        = (b - μ) / (b - a) := by
      have : ∀ v : V, q v * ((b - g v) / (b - a))
          = (q v * (b - g v)) / (b - a) := fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => this v)]
      rw [← Finset.sum_div]
      have hbg : ∑ v : V, q v * (b - g v) = b - μ := by
        have hsplit : ∀ v : V, q v * (b - g v) = q v * b - q v * g v := by
          intro v; ring
        rw [Finset.sum_congr rfl (fun v _ => hsplit v)]
        rw [Finset.sum_sub_distrib]
        have hqb : ∑ v : V, q v * b = b := by
          rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) b),
            ← Finset.mul_sum, hq1, mul_one]
        rw [hqb]
      rw [hbg]
    have hwavg2 : ∑ v : V, q v * ((g v - a) / (b - a))
        = (μ - a) / (b - a) := by
      have : ∀ v : V, q v * ((g v - a) / (b - a))
          = (q v * (g v - a)) / (b - a) := fun v => by ring
      rw [Finset.sum_congr rfl (fun v _ => this v)]
      rw [← Finset.sum_div]
      have hga : ∑ v : V, q v * (g v - a) = μ - a := by
        have hsplit : ∀ v : V, q v * (g v - a) = q v * g v - q v * a := by
          intro v; ring
        rw [Finset.sum_congr rfl (fun v _ => hsplit v)]
        rw [Finset.sum_sub_distrib]
        have hqa : ∑ v : V, q v * a = a := by
          rw [Finset.sum_congr rfl (fun v _ => mul_comm (q v) a)]
          rw [← Finset.mul_sum, hq1, mul_one]
        rw [hqa]
      rw [hga]
    -- distribute the sum over the two terms
    have hsplit : ∑ v : V, q v * ((b - g v) / (b - a) * Real.exp (r * (a - μ))
        + (g v - a) / (b - a) * Real.exp (r * (b - μ)))
        = ∑ v : V, q v * ((b - g v) / (b - a)) * Real.exp (r * (a - μ))
          + ∑ v : V, q v * ((g v - a) / (b - a)) * Real.exp (r * (b - μ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [hsplit]
    have e1 : ∑ v : V, q v * ((b - g v) / (b - a)) * Real.exp (r * (a - μ))
        = (∑ v : V, q v * ((b - g v) / (b - a))) * Real.exp (r * (a - μ)) := by
      simp [Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]
    have e2 : ∑ v : V, q v * ((g v - a) / (b - a)) * Real.exp (r * (b - μ))
        = (∑ v : V, q v * ((g v - a) / (b - a))) * Real.exp (r * (b - μ)) := by
      simp [Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]
    rw [e1, e2, hwavg1, hwavg2]

/-! ## Хорда логарифма (R500)

Вогнутость ln: (1-w) ln a + w ln b <= ln((1-w)a + w b) для
a,b > 0, 0 < w < 1. Через strictConcaveOn_log_Ioi.concaveOn;
двухточечный Jensen. Основа для вариационных KL-шагов
(взвешенные log-sum оценки). -/
theorem log_chord {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℝ)
    (hw : 0 < w) (hw2 : w < 1) :
    (1 - w) * Real.log a + w * Real.log b
      ≤ Real.log ((1 - w) * a + w * b) := by
  have hc : ConcaveOn ℝ (Ioi (0:ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have hma : (a:ℝ) ∈ Ioi (0:ℝ) := ha
  have hmb : (b:ℝ) ∈ Ioi (0:ℝ) := hb
  have hw1 : (0:ℝ) ≤ 1 - w := by linarith
  have hsum : (1 - w) + w = 1 := by ring
  have h := hc.2 hma hmb hw1 (le_of_lt hw) hsum
  -- h : log ((1-w) • a + w • b) >= (1-w) • log a + w • log b
  have hcombo : ((1 - w)) • (a:ℝ) + (w) • (b:ℝ) = (1 - w) * a + w * b := by
    rw [smul_eq_mul, smul_eq_mul]
  rw [hcombo] at h
  simpa using h
