/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.FrontierScaling
import Hagi.Growth.TakeoffElasticity
import Hagi.Foundations.ConeTakeoff
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

namespace Hagi.Growth

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
    (h_emp_step : ∀ t, C (t + 1) = C t + γ * D t)
    (h_emp_dyn : ∀ t, ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    {t : ℕ}
    (hCpos : 0 < C t) (h_emp_cone : k * C t ≤ D t) :
    k * C (t + 1) ≤ D (t + 1) :=
  -- dedup R291: delegation to the canonical Foundations.cone_step
  Hagi.Foundations.cone_step C D γ ρ β k t hCpos
    (h_emp_step t) (h_emp_dyn t) hrhogk hbeta h_emp_cone

/-- Если `0 < C t` при всех t, выполнены посылки
`cone_ratio_step` и `k·C 0 ≤ D 0`, то `ConeRatio C D k`. -/
theorem cone_ratio_invariant (C D : ℕ → ℝ) (γ ρ β k : ℝ)
    (hCpos : ∀ t, 0 < C t)
    (h_emp_step : ∀ t, C (t + 1) = C t + γ * D t)
    (h_emp_dyn : ∀ t, ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (h_emp_cone0 : k * C 0 ≤ D 0) :
    ConeRatio C D k := by
  intro t
  induction t with
  | zero => exact h_emp_cone0
  | succ t ih =>
      exact cone_ratio_step C D γ ρ β k h_emp_step h_emp_dyn hrhogk hbeta
        (hCpos t) ih

/-- Если `0 < γ`, `0 < k`, `C (t+1) = C t + γ·D t` и
`ConeRatio C D k`, то `C 0·(1+γk)^T ≤ C T`. -/
theorem ratio_takeoff (C D : ℕ → ℝ) (γ k : ℝ)
    (hγ : 0 < γ) (hk : 0 < k)
    (h_emp_step : ∀ t, C (t + 1) = C t + γ * D t)
    (h_emp_cone : ConeRatio C D k) (T : ℕ) :
    C 0 * (1 + γ * k) ^ T ≤ C T := by
  -- dedup R-scan: the manual induction is exactly the
  -- specialization of TakeoffElasticity.elasticity_chain with
  -- the constant cone elasticity `e t = γ·k` — the cone gives
  -- the per-step elasticity lower bound, the product chain
  -- does the rest.
  have hstep : ∀ t, (1 + γ * k) * C t ≤ C (t + 1) := by
    intro t
    rw [h_emp_step t]
    have hring2 : C t + γ * k * C t = C t + γ * (k * C t) := by ring
    have hmul : γ * (k * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left (h_emp_cone t) hγ.le
    have hring : C t + γ * k * C t = (1 + γ * k) * C t := by ring
    linarith [hring, hring2, hmul]
  have hchain := Hagi.Growth.elasticity_chain C (fun _ => γ * k) T
    hstep (fun t _ => by positivity)
  rwa [Finset.prod_const, Finset.card_range] at hchain

/-- Если `0 ≤ ρ` и `D (t+1) ≤ ρ·D t` при всех t, то
`D T ≤ ρ^T·D 0`. -/
theorem frontier_decay_no_growth (D : ℕ → ℝ) (ρ : ℝ)
    (hrho : 0 ≤ ρ)
    (h_emp_dyn : ∀ t, D (t + 1) ≤ ρ * D t) (T : ℕ) :
    D T ≤ ρ ^ T * D 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := h_emp_dyn T
      have h2 : ρ ^ (T + 1) * D 0 = ρ * (ρ ^ T * D 0) := by ring
      calc D (T + 1) ≤ ρ * D T := h1
        _ ≤ ρ * (ρ ^ T * D 0) :=
            mul_le_mul_of_nonneg_left ih hrho
        _ = ρ ^ (T + 1) * D 0 := h2.symm

end Hagi.Growth

namespace Hagi
export Hagi.Growth (ConeRatio cone_ratio_step cone_ratio_invariant ratio_takeoff frontier_decay_no_growth)
end Hagi
