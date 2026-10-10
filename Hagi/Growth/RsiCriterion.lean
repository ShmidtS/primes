/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# RsiCriterion — пошаговое условие самоподдержки RSI

* `rsi_step_growth`: при динамике
  `ρ·D t + β·C t − ξ t ≤ D (t+1)` и превышении производства
  над затуханием `ξ t + (1−ρ)·D t < β·C t` следует
  `D t < D (t+1)`. Сама по себе динамика роста не
  гарантирует — нужна верхняя оценка на D (см. ниже);
* `rsi_cone_criterion`: при конусной оценке
  `D t ≤ (α/γ)·C t`, `0 < γ`, `0 < C t`, `ρ ≤ 1` рост следует
  из безразмерного барьера
  `(1−ρ)·α + γ·ξ t/C t < β·γ`.
-/

open Finset Real

namespace Hagi.Growth

/-- Если `ρ·D t + β·C t − ξ t ≤ D (t+1)` и
`ξ t + (1−ρ)·D t < β·C t`, то `D t < D (t+1)`. -/
theorem rsi_step_growth (D C : ℕ → ℝ) (rho beta : ℝ) (xi : ℕ → ℝ)
    (t : ℕ)
    (hdyn : rho * D t + beta * C t - xi t ≤ D (t + 1))
    (hstep : xi t + (1 - rho) * D t < beta * C t) :
    D t < D (t + 1) := by
  have hE : D (t + 1) - D t
      ≥ rho * D t + beta * C t - xi t - D t := by linarith
  have hkey : rho * D t + beta * C t - xi t - D t
      = beta * C t - xi t - (1 - rho) * D t := by ring
  rw [hkey] at hE
  linarith

/-- Если `0 < γ`, `0 < C t`, `ρ ≤ 1`,
`ρ·D t + β·C t − ξ t ≤ D (t+1)`, `D t ≤ (α/γ)·C t` и
`(1−ρ)·α + γ·ξ t/C t < β·γ`, то `D t < D (t+1)`. -/
theorem rsi_cone_criterion (D C : ℕ → ℝ) (rho beta alpha gamma : ℝ)
    (xi : ℕ → ℝ) (t : ℕ)
    (hgamma : 0 < gamma) (hCpos : 0 < C t) (hrho : rho ≤ 1)
    (hdyn : rho * D t + beta * C t - xi t ≤ D (t + 1))
    (hcone : D t ≤ alpha / gamma * C t)
    (hcriterion : (1 - rho) * alpha + gamma * xi t / C t
      < beta * gamma) :
    D t < D (t + 1) := by
  have hrho0 : (0:ℝ) ≤ 1 - rho := by linarith
  -- конус ⟹ (1-rho)*D ≤ (1-rho)*(alpha/gamma)*C
  have h1 : (1 - rho) * D t
      ≤ (1 - rho) * (alpha / gamma * C t) :=
    mul_le_mul_of_nonneg_left hcone hrho0
  -- критерий ⟹ умножение на C/gamma > 0
  have h2 : ((1 - rho) * alpha) * C t / gamma + xi t
      < beta * C t := by
    have hmul : ((1 - rho) * alpha + gamma * xi t / C t) * (C t / gamma)
        < beta * gamma * (C t / gamma) :=
      mul_lt_mul_of_pos_right hcriterion (by positivity)
    have hsplit : ((1 - rho) * alpha + gamma * xi t / C t) * (C t / gamma)
        = ((1 - rho) * alpha) * C t / gamma + xi t := by
      field_simp
    have hsplit2 : beta * gamma * (C t / gamma) = beta * C t := by
      field_simp
    rw [hsplit, hsplit2] at hmul
    exact hmul
  -- перегруппировка: (1-rho)*(alpha/gamma)*C = ((1-rho)*alpha)*C/gamma
  have h3 : (1 - rho) * (alpha / gamma * C t)
      = ((1 - rho) * alpha) * C t / gamma := by
    field_simp
  rw [h3] at h1
  have hstep : xi t + (1 - rho) * D t < beta * C t := by
    linarith
  exact rsi_step_growth D C rho beta xi t hdyn hstep

end Hagi.Growth

namespace Hagi
export Hagi.Growth (rsi_step_growth rsi_cone_criterion)
end Hagi
