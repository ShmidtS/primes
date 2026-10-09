/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.FrontierScaling
set_option linter.style.header false

/-!
# RatioTakeoff — takeoff через динамику отношения r = D/C

Посылки: точный шаг `C' = C + γ·D`, односторонняя динамика
`D' ≥ ρ·D + β·C − ξ` (ξ = 0 в ядре), без верхней границы на `C'`.

* `cone_ratio_step`: при `ρ ≥ γk` и пороге
  `β ≥ γk² + (1−ρ)k` конус `k·C t ≤ D t` переходит из t в t+1
  (одностороннее неравенство: `D' − kC' ≥ (ρ−γk)(D−kC) + margin·C`);
* `cone_ratio_invariant`: индукция — конус при всех t;
* `ratio_takeoff`: при конусе `C 0·(1+γk)^T ≤ C T`, без h_C_cap;
* `frontier_decay_no_growth`: при `D (t+1) ≤ ρ·D t` выполнено
  `D T ≤ ρ^T·D 0`.

ξ ≠ 0-компенсация и насыщение C* — вне этого модуля.
-/

open Finset Real

namespace Hagi

/-- Конус отношения: `ConeRatio C D k` означает
`∀ t, k·C t ≤ D t` (без деления). -/
def ConeRatio (C D : ℕ → ℝ) (k : ℝ) : Prop :=
  ∀ t, k * C t ≤ D t

/-- Шаг конуса (ξ = 0): при `C (t+1) = C t + γ·D t`,
`ρ·D t + β·C t ≤ D (t+1)`, `γ·k ≤ ρ`,
`γ·k² + (1−ρ)·k ≤ β`, `0 < C t` и `k·C t ≤ D t` следует
`k·C (t+1) ≤ D (t+1)`. При ξ ≠ 0 полю усиливается до
`β ≥ γk² + (1−ρ)k + ξ/C`. -/
theorem cone_ratio_step (C D : ℕ → ℝ) (γ ρ β k : ℝ)
    (hstep : ∀ t, C (t + 1) = C t + γ * D t)
    (hdyn : ∀ t, ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    {t : ℕ}
    (hCpos : 0 < C t) (hcone : k * C t ≤ D t) :
    k * C (t + 1) ≤ D (t + 1) := by
  have hd := hdyn t
  have hb := hbeta
  have hs := hstep t
  have hkey : ρ * D t + β * C t - k * (C t + γ * D t)
      = (ρ - γ * k) * (D t - k * C t)
        + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t := by
    field_simp
    ring
  have h1 : (0:ℝ) ≤ (ρ - γ * k) * (D t - k * C t) := by
    have hsub : (0:ℝ) ≤ D t - k * C t := by linarith [hcone]
    exact mul_nonneg (by linarith [hrhogk]) hsub
  have h2 : (0:ℝ) ≤ (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t :=
    mul_nonneg (by linarith [hb]) hCpos.le
  have h3 : D (t + 1) - k * C (t + 1)
      ≥ (ρ - γ * k) * (D t - k * C t)
        + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t := by
    rw [hs]
    linarith [hd, hkey]
  linarith

/-- Если `0 < C t` при всех t, выполнены посылки
`cone_ratio_step` и `k·C 0 ≤ D 0`, то `ConeRatio C D k`. -/
theorem cone_ratio_invariant (C D : ℕ → ℝ) (γ ρ β k : ℝ)
    (hCpos : ∀ t, 0 < C t)
    (hstep : ∀ t, C (t + 1) = C t + γ * D t)
    (hdyn : ∀ t, ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (hcone0 : k * C 0 ≤ D 0) :
    ConeRatio C D k := by
  intro t
  induction t with
  | zero => exact hcone0
  | succ t ih =>
      exact cone_ratio_step C D γ ρ β k hstep hdyn hrhogk hbeta
        (hCpos t) ih

/-- Если `0 < γ`, `0 < k`, `C (t+1) = C t + γ·D t` и
`ConeRatio C D k`, то `C 0·(1+γk)^T ≤ C T`. -/
theorem ratio_takeoff (C D : ℕ → ℝ) (γ k : ℝ)
    (hγ : 0 < γ) (hk : 0 < k)
    (hstep : ∀ t, C (t + 1) = C t + γ * D t)
    (hcone : ConeRatio C D k) (T : ℕ) :
    C 0 * (1 + γ * k) ^ T ≤ C T := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hc := hcone T
      have hs := hstep T
      have hgrow : (1 + γ * k) * C T ≤ C (T + 1) := by
        rw [hs]
        have hring : C T + γ * k * C T = (1 + γ * k) * C T := by ring
        have hmul : γ * (k * C T) ≤ γ * D T :=
          mul_le_mul_of_nonneg_left hc hγ.le
        have hring2 : C T + γ * k * C T = C T + γ * (k * C T) := by ring
        linarith [hring, hring2, hmul]
      have hcast : (1 + γ * k) ^ (T + 1)
          = (1 + γ * k) ^ T * (1 + γ * k) := by ring
      rw [hcast]
      calc C 0 * ((1 + γ * k) ^ T * (1 + γ * k))
          = (C 0 * (1 + γ * k) ^ T) * (1 + γ * k) := by ring
        _ ≤ C T * (1 + γ * k) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = (1 + γ * k) * C T := by ring
        _ ≤ C (T + 1) := hgrow

/-- Если `0 ≤ ρ` и `D (t+1) ≤ ρ·D t` при всех t, то
`D T ≤ ρ^T·D 0`. -/
theorem frontier_decay_no_growth (D : ℕ → ℝ) (ρ : ℝ)
    (hrho : 0 ≤ ρ)
    (hdyn : ∀ t, D (t + 1) ≤ ρ * D t) (T : ℕ) :
    D T ≤ ρ ^ T * D 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hdyn T
      have h2 : ρ ^ (T + 1) * D 0 = ρ * (ρ ^ T * D 0) := by ring
      calc D (T + 1) ≤ ρ * D T := h1
        _ ≤ ρ * (ρ ^ T * D 0) :=
            mul_le_mul_of_nonneg_left ih hrho
        _ = ρ ^ (T + 1) * D 0 := h2.symm

end Hagi
