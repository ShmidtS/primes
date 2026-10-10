/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.Saturation
import Hagi.Growth.StateBinding
set_option linter.style.header false

/-!
# StateClosedRenewal — state-closed замыкание C→D→G→S

Динамика на полях состояния:
`C t = (S t).capability`, `D t = usableFrontier (S t)`.

* `state_closed_takeoff`: при шаге
  `C' = C + γ·D`, динамике `D' ≥ ρ·D + β·C`, `ρ ≥ γk`, пороге
  `β ≥ γk² + (1−ρ)k` и старте в конусе —
  `(S 0).capability·(1+γk)^T ≤ (S T).capability`;
* `state_closed_renewal_step`: то же с трением ξ и усиленным
  порогом `β ≥ γk² + (1−ρ)k + ξ/C t` — шаг конуса на полях
  состояния;
* `state_closed_band`: двусторонняя полоса
  `C₀(1+γk)^T ≤ (S T).capability ≤ C* − (1−σ)^T·(C* − C₀)`.

Полю β, PL-окно и `ρ ≥ γk` — пошаговые измеряемые посылки.
-/

open Finset Real

namespace Hagi.Growth

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- При `0 < γ`, `0 < k`, `0 < (S t).capability`, шаге
`C' = C + γ·usableFrontier`, динамике `D' ≥ ρ·D + β·C`,
`ρ ≥ γk`, пороге `β ≥ γk² + (1−ρ)k` и старте в конусе —
`(S 0).capability·(1+γk)^T ≤ (S T).capability`
(композиция `ratio_takeoff` и `cone_ratio_invariant`). -/
theorem state_closed_takeoff (S : ℕ → GrowthState X)
    (γ ρ β k : ℝ)
    (hγ : 0 < γ) (hk : 0 < k)
    (hCpos : ∀ t, 0 < (S t).capability)
    (h_emp_step : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (h_emp_dyn : ∀ t, ρ * usableFrontier (S t) + β * (S t).capability
      ≤ usableFrontier (S (t + 1)))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (h_emp_cone0 : k * (S 0).capability ≤ usableFrontier (S 0))
    (T : ℕ) :
    (S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability := by
  exact ratio_takeoff (fun t => (S t).capability)
    (fun t => usableFrontier (S t)) γ k hγ hk h_emp_step
    (cone_ratio_invariant (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) γ ρ β k hCpos h_emp_step h_emp_dyn
      hrhogk hbeta h_emp_cone0) T

/-- Шаг конуса с трением: при шаге `C' = C + γ·D`, динамике
`ρ·D + β·C − ξ t ≤ D'`, `ρ ≥ γk`, пороге
`γk² + (1−ρ)k + ξ t/C t ≤ β`, `0 < C t` и конусе
`k·C t ≤ D t` следует
`k·(S (t+1)).capability ≤ usableFrontier (S (t+1))`. -/
theorem state_closed_renewal_step (S : ℕ → GrowthState X)
    (γ ρ β k : ℝ) (xi : ℕ → ℝ)
    (h_emp_step : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (h_emp_dyn : ∀ t, ρ * usableFrontier (S t) + β * (S t).capability
      - xi t ≤ usableFrontier (S (t + 1)))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : ∀ t, γ * k ^ 2 + (1 - ρ) * k
      + xi t / (S t).capability ≤ β)
    {t : ℕ}
    (hCpos : 0 < (S t).capability)
    (h_emp_cone : k * (S t).capability ≤ usableFrontier (S t)) :
    k * (S (t + 1)).capability ≤ usableFrontier (S (t + 1)) := by
  have hd := h_emp_dyn t
  have hb := hbeta t
  have hs := h_emp_step t
  set C := (S t).capability with hC
  set D := usableFrontier (S t) with hD
  set C' := (S (t + 1)).capability with hC'
  set D' := usableFrontier (S (t + 1)) with hD'
  -- ключевая алгебра: D' − kC' ≥ (ρ−γk)(D−kC) + margin·C,
  -- margin = β − γk² − (1−ρ)k − ξ/C ≥ 0
  have hkey : ρ * D + β * C - xi t - k * (C + γ * D)
      = (ρ - γ * k) * (D - k * C)
        + (β - (γ * k ^ 2 + (1 - ρ) * k + xi t / C)) * C := by
    field_simp
    ring
  have h1 : (0:ℝ) ≤ (ρ - γ * k) * (D - k * C) := by
    have hsub : (0:ℝ) ≤ D - k * C := by linarith [h_emp_cone]
    exact mul_nonneg (by linarith [hrhogk]) hsub
  have h2 : (0:ℝ)
      ≤ (β - (γ * k ^ 2 + (1 - ρ) * k + xi t / C)) * C :=
    mul_nonneg (by linarith [hb]) hCpos.le
  have h3 : D' - k * C'
      ≥ (ρ - γ * k) * (D - k * C)
        + (β - (γ * k ^ 2 + (1 - ρ) * k + xi t / C)) * C := by
    rw [hs]
    linarith [hkey, hd]
  linarith

/-- При посылках `state_closed_takeoff` и обеих PL-формах с
`(S 0).capability ≤ Cstar` выполнено
`(S 0).capability·(1+γk)^T ≤ (S T).capability
≤ Cstar − (1−σ)^T·(Cstar − (S 0).capability)`. -/
theorem state_closed_band (S : ℕ → GrowthState X)
    (γ ρ β k Cstar σ : ℝ)
    (hγ : 0 < γ) (hk : 0 < k) (hσ1 : σ ≤ 1)
    (hCpos : ∀ t, 0 < (S t).capability)
    (h_emp_step : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (h_emp_dyn : ∀ t, ρ * usableFrontier (S t) + β * (S t).capability
      ≤ usableFrontier (S (t + 1)))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (h_emp_cone0 : k * (S 0).capability ≤ usableFrontier (S 0))
    (hpl_up : ∀ t, (S (t + 1)).capability
      ≤ (S t).capability + σ * (Cstar - (S t).capability))
    (hpl_lo : ∀ t, (S t).capability
      + σ * (Cstar - (S t).capability) ≤ (S (t + 1)).capability)
    (hC0 : (S 0).capability ≤ Cstar) (T : ℕ) :
    (S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability
      ∧ (S T).capability
        ≤ Cstar - (1 - σ) ^ T * (Cstar - (S 0).capability) := by
  exact takeoff_with_saturation (fun t => (S t).capability)
    (fun t => usableFrontier (S t)) γ k Cstar σ hγ hk hσ1 h_emp_step
    hpl_up hpl_lo
    (cone_ratio_invariant (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) γ ρ β k hCpos h_emp_step h_emp_dyn
      hrhogk hbeta h_emp_cone0) hC0 T

end Hagi.Growth

namespace Hagi
export Hagi.Growth (state_closed_takeoff state_closed_renewal_step state_closed_band)
end Hagi
