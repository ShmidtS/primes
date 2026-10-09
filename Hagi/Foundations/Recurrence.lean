/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
set_option linter.style.header false

/-!
# Foundations.Recurrence — каноническая рекуррентная лемма

Канонические леммы для линейной рекурренты
`x_{t+1} ≤ rho * x_t + c` на горизонте `t < T`: посылки
только при `t < T`, горизонт `T` — в самой лемме.
-/

open Finset Real

namespace Hagi.Foundations

variable (rho c : ℝ)

/-- Телескоп-тождество геометрической суммы:
(1 - rho) * sum_{i<t} rho^i = 1 - rho^t. -/
theorem geom_telescope (T : ℕ) :
    (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i = 1 - rho ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ]
      have hexp : (1 - rho) * (∑ i ∈ Finset.range T, rho ^ i + rho ^ T)
          = (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i
            + (1 - rho) * rho ^ T := by ring
      rw [hexp, ih, pow_succ]
      ring

/-- **Верхняя рекуррента (горизонтная форма)**: если
x_{t+1} <= rho * x_t + c при t < T и rho ∈ [0,1), то

  x T <= rho^T * x 0 + c * ((1 - rho^T) / (1 - rho)). -/
theorem recurrence_upper (x : ℕ → ℝ) (T : ℕ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hstep : ∀ t < T, x (t + 1) ≤ rho * x t + c) :
    x T ≤ rho ^ T * x 0 + c * ((1 - rho ^ T) / (1 - rho)) := by
  -- ключевое тождество индукции: rho * sum_t + 1 = sum_{t+1}
  have hstepid : ∀ t : ℕ,
      rho * ∑ i ∈ Finset.range t, rho ^ i + 1
        = ∑ i ∈ Finset.range (t + 1), rho ^ i := by
    intro t
    have h := geom_telescope rho t
    rw [Finset.sum_range_succ]
    linarith
  have hmain : ∀ t, t ≤ T →
      x t ≤ rho ^ t * x 0 + c * (∑ i ∈ Finset.range t, rho ^ i) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have htlt : t < T := by omega
        have hs := hstep t htlt
        have hih := ih (by omega)
        have hconv : rho * (rho ^ t * x 0 + c * ∑ i ∈ Finset.range t, rho ^ i)
            = rho ^ (t + 1) * x 0 + c * (rho * ∑ i ∈ Finset.range t, rho ^ i) := by
          rw [pow_succ]
          ring
        calc x (t + 1) ≤ rho * x t + c := hs
          _ ≤ rho * (rho ^ t * x 0
                + c * ∑ i ∈ Finset.range t, rho ^ i) + c := by
              have hmul := mul_le_mul_of_nonneg_left hih hrho
              linarith
          _ = rho ^ (t + 1) * x 0
                + c * (rho * ∑ i ∈ Finset.range t, rho ^ i) + c := by
                rw [hconv]
          _ = rho ^ (t + 1) * x 0
                + c * (∑ i ∈ Finset.range (t + 1), rho ^ i) := by
                have hrw : rho ^ (t + 1) * x 0
                    + c * (rho * ∑ i ∈ Finset.range t, rho ^ i) + c
                    = rho ^ (t + 1) * x 0
                      + c * (rho * ∑ i ∈ Finset.range t, rho ^ i + 1) := by
                  ring
                rw [hrw, hstepid t]
  have hgeom : ∑ i ∈ Finset.range T, rho ^ i
      = (1 - rho ^ T) / (1 - rho) := by
    have hne : 1 - rho ≠ 0 :=
      sub_ne_zero_of_ne (ne_of_lt hrho1).symm
    have hsum := geom_telescope rho T
    field_simp
    linarith [hsum]
  have h := hmain T (le_refl T)
  rw [hgeom] at h
  exact h

/-- **Чистая рекуррента (c = 0)**: x_{t+1} <= rho * x_t при
t < T и rho ≥ 0 ⟹ x T <= rho^T * x 0. Требования rho < 1
НЕ нужно (в отличие от recurrence_upper с c ≠ 0): случай
rho = 1 — тривиальная нестрогая нерастущесть. -/
theorem recurrence_pure (x : ℕ → ℝ) (T : ℕ)
    (hrho : 0 ≤ rho)
    (hstep : ∀ t < T, x (t + 1) ≤ rho * x t) :
    x T ≤ rho ^ T * x 0 := by
  have hmain : ∀ t : ℕ, t ≤ T →
      x t ≤ rho ^ t * x 0 := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have hs := hstep t (by omega)
        have hih := ih (by omega)
        have hmul : rho * x t ≤ rho * (rho ^ t * x 0) :=
          mul_le_mul_of_nonneg_left hih hrho
        rw [pow_succ]
        calc x (t + 1) ≤ rho * x t := hs
          _ ≤ rho * (rho ^ t * x 0) := hmul
          _ = rho ^ t * rho * x 0 := by ring
  exact hmain T (le_refl T)

/-- **Нижняя рекуррента (c = 0, горизонт)**: x_{t+1} >= rho * x_t
при t < T и rho >= 0 ⟹ rho^T * x 0 <= x T. -/
theorem recurrence_lower (x : ℕ → ℝ) (T : ℕ)
    (hrho : 0 ≤ rho)
    (hstep : ∀ t < T, rho * x t ≤ x (t + 1)) :
    rho ^ T * x 0 ≤ x T := by
  have hmain : ∀ t : ℕ, t ≤ T → rho ^ t * x 0 ≤ x t := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have hs := hstep t (by omega)
        have hih := ih (by omega)
        have hstepmul : rho ^ t * x 0 * rho ≤ x t * rho :=
          mul_le_mul_of_nonneg_right hih hrho
        rw [pow_succ]
        calc rho ^ t * rho * x 0 = rho ^ t * x 0 * rho := by ring
          _ ≤ x t * rho := hstepmul
          _ = rho * x t := by ring
          _ ≤ x (t + 1) := hs
  exact hmain T (le_refl T)

/-- Геометрическая хвостовая граница: для `rho ∈ [0,1)`
конечная геометрическая сумма `∑ i < T, rho ^ i ≤ 1 / (1 - rho)`. -/
theorem geom_sum_le_inv (T : ℕ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    ∑ i ∈ Finset.range T, rho ^ i ≤ 1 / (1 - rho) := by
  have hpos : 0 < 1 - rho := by linarith
  have hid := geom_telescope rho T
  have h1 : rho ^ T ≥ 0 := by positivity
  have hle : 1 - rho ^ T ≤ 1 := by linarith
  have hsplit : (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i ≤ 1 := by linarith
  rw [le_div_iff₀ hpos]
  have hfinal : (1 - rho) * (1 / (1 - rho)) = 1 := by field_simp
  have hmono : (1 - rho) * ∑ i ∈ Finset.range T, rho ^ i
      ≤ (1 - rho) * (1 / (1 - rho)) := by
    rw [hfinal]
    exact hsplit
  have hdiv : (1 / (1 - rho)) * (1 - rho) = 1 := by field_simp
  nlinarith [hmono, hpos]

/-- Предел сжатия: если `x (t + 1) ≤ rho * x t + delta` для
всех `t` и `rho < 1`, то `x T ≤ rho ^ T * x 0 + delta / (1 - rho)`. -/
theorem contraction_limit (x : ℕ → ℝ) (delta : ℝ) (T : ℕ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hdelta : 0 ≤ delta)
    (hstep : ∀ t, x (t + 1) ≤ rho * x t + delta) :
    x T ≤ rho ^ T * x 0 + delta / (1 - rho) := by
  have hexact : ∀ t : ℕ, t ≤ T →
      x t ≤ rho ^ t * x 0 + delta * ∑ i ∈ Finset.range t, rho ^ i := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
        intro hle
        have h1 := hstep t
        have hchain : x (t + 1)
            ≤ rho * (rho ^ t * x 0 + delta * ∑ i ∈ Finset.range t, rho ^ i) + delta := by
          calc x (t + 1) ≤ rho * x t + delta := h1
            _ ≤ rho * (rho ^ t * x 0 + delta * ∑ i ∈ Finset.range t, rho ^ i) + delta := by
                have hmul := mul_le_mul_of_nonneg_left (ih (by omega)) hrho
                linarith
        rw [Finset.sum_range_succ, pow_succ]
        have htel := geom_telescope rho t
        nlinarith [hchain, htel, hdelta]
  have hsum := geom_sum_le_inv rho T hrho hrho1
  have hfin := hexact T (le_refl T)
  have hdelta' : delta * ∑ i ∈ Finset.range T, rho ^ i ≤ delta / (1 - rho) := by
    calc delta * ∑ i ∈ Finset.range T, rho ^ i
        ≤ delta * (1 / (1 - rho)) := mul_le_mul_of_nonneg_left hsum hdelta
      _ = delta / (1 - rho) := by field_simp
  linarith

/-- **The linear compounding law.** If each cycle improves the
mean by at least `c`, the mean after `k` cycles is at most
`M₀ − k • c`. -/
theorem genMean_compound (M₀ c : ℝ) (_hc : 0 < c)
    (step : ℕ → ℝ → ℝ)
    (hstep : ∀ k M, step k M ≤ M - c)
    (iter : ℕ → ℝ) (hiter0 : iter 0 = M₀)
    (hiterS : ∀ k, iter (k + 1) = step k (iter k)) :
    ∀ k : ℕ, iter k ≤ M₀ - (k : ℝ) * c := by
  intro k
  induction k with
  | zero => rw [hiter0]; norm_num
  | succ n ih =>
      have h1 := hstep n (iter n)
      have h2 : iter (n + 1) ≤ iter n - c := by
        rw [hiterS n]
        exact h1
      -- the goal: iter (n+1) <= M0 - (n+1)c
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
        push_cast
        ring
      have hgoal : iter n - c ≤ M₀ - ((n + 1 : ℕ) : ℝ) * c := by
        rw [hcast]
        linarith [ih]
      linarith [h2, hgoal]

/-- If `G (t + 1) ≤ ρ * G t + D` for all `t` with
`0 ≤ ρ < 1` and `G 0 ≤ G₀`, then
`G t ≤ ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)` for every `t`. -/
theorem genGap_decay (ρ D G₀ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (_hD : 0 ≤ D) (G : ℕ → ℝ) (hG0 : G 0 ≤ G₀)
    (hstep : ∀ t, G (t + 1) ≤ ρ * G t + D) :
    ∀ t, G t ≤ ρ ^ t * G₀ + (D * (1 - ρ ^ t)) / (1 - ρ) := by
  intro t
  induction t with
  | zero =>
      have hρ0 : (ρ : ℝ) ^ 0 = 1 := by simp
      rw [hρ0]
      norm_num
      exact hG0
  | succ t ih =>
      have h1 := hstep t
      have hexp : ρ * ρ ^ t = ρ ^ (t + 1) := by
        rw [pow_succ]
        ring
      have hne : (1 - ρ) ≠ 0 := by
        have := ne_of_lt hρ1
        exact fun h => this (by linarith)
      have h2 : ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D
          = ρ ^ (t + 1) * G₀ + D * (1 - ρ ^ (t + 1)) / (1 - ρ) := by
        rw [pow_succ]
        field_simp
        ring
      have hcomb : ρ * G t + D
          ≤ ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D := by
        calc ρ * G t + D
            ≤ ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D := by
              refine add_le_add_left ?_ D
              exact mul_le_mul_of_nonneg_left ih hρ
          _ = ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D := rfl
      -- the goal: G (t+1) <= ρ^{t+1} G0 + D(1-ρ^{t+1})/(1-ρ)
      have hfinal : ρ * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + D
          ≤ ρ ^ (t + 1) * G₀ + D * (1 - ρ ^ (t + 1)) / (1 - ρ) :=
        le_of_eq h2
      linarith [h1, hcomb, hfinal]


end Hagi.Foundations

