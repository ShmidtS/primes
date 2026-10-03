/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.Saturation
import Hagi.Growth.StateBinding
set_option linter.style.header false

/-!
# R126: StateClosedRenewal — state-closed замыкание C→D→G→S

Аудит R126 (§6, §31): центральная нерешённая теорема системы —
state-bound рост без shadow-последовательностей:

  C_t = (S t).capability,  D_t = usableFrontier (S t).

Настоящий модуль замыкает контур на полях состояния,
композируя РОБАСТНЫЙ ratio-конус (R124, без h_C_cap) с
динамикой frontier и насыщением (R125):

* `state_closed_takeoff` — при динамике состояния
  C' = C + γ·D, D' ≥ ρD + βC, полю зажигания
  β ≥ γk² + (1−ρ)k и ρ ≥ γk — экспоненциальный рост
  НАСТОЯЩЕГО поля (S t).capability: (1+γk)^T-мультипликатор.
  Никаких отдельных C G D : ℕ → ℝ: конус и шаг проверяются на
  измеряемых полях состояния на каждом цикле.
* `state_closed_renewal_step` — пошаговое замыкание контура
  при трении ξ: полю β ≥ γk² + (1−ρ)k + ξ/C_t (ξ-компенсация
  R124-наброска, теперь формально на состоянии): ξ сокращается
  точно, шаг конуса односторонний.
* `state_closed_band` — двусторонняя полоса на состоянии
  (взлёт ↔ ёмкость, R125): (1+γk)^T снизу, PL-окно сверху.

**Честные границы**: полю β — измеряемое (R117 сертифицирует
по разногласию экспертов); PL-окно и ρ ≥ γk — пошаговые
измеряемые посылки (h_emp_-слой); «runtime ⇒ success»-стрелка
и генератор frontier (CandidateComplete) остаются открытыми
(P0-1, P0-5 аудита).
-/

open Finset Real

namespace Hagi

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **State-closed takeoff**: экспоненциальный рост
НАСТОЯЩЕГО поля (S t).capability. Все посылки — пошаговые
сертификаты на измеряемых полях состояния
((S t).capability, usableFrontier (S t) = (S t).dataField);
никаких shadow-последовательностей C G D : ℕ → ℝ.
Контур: конус {D ≥ kC} инвариантен (R124) ⇒ каждый шаг
умножает capability на (1+γk). -/
theorem state_closed_takeoff (S : ℕ → GrowthState X)
    (γ ρ β k : ℝ)
    (hγ : 0 < γ) (hk : 0 < k)
    (hCpos : ∀ t, 0 < (S t).capability)
    (hstep : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (hdyn : ∀ t, ρ * usableFrontier (S t) + β * (S t).capability
      ≤ usableFrontier (S (t + 1)))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (hcone0 : k * (S 0).capability ≤ usableFrontier (S 0))
    (T : ℕ) :
    (S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability := by
  exact ratio_takeoff (fun t => (S t).capability)
    (fun t => usableFrontier (S t)) γ k hγ hk hstep
    (cone_ratio_invariant (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) γ ρ β k hCpos hstep hdyn
      hrhogk hbeta hcone0) T

/-- **State-closed шаг конуса с трением ξ**: при полю зажигания,
усиленном на ξ_t/C_t (трение конечных данных), шаг конуса
D ≥ kC ⇒ D' ≥ kC' выполняется на полях состояния; ξ-слагаемое
компенсируется ТОЧНО (алгебра R124: D'−kC' ≥ (ρ−γk)(D−kC) ≥ 0).
Это пошаговая переэкземпляриация `cone_ratio_step` на
состоянии — контроллер перепроверяет конус по измерениям
каждого цикла, а не доверяет глобальному сертификату. -/
theorem state_closed_renewal_step (S : ℕ → GrowthState X)
    (γ ρ β k : ℝ) (xi : ℕ → ℝ)
    (hstep : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (hdyn : ∀ t, ρ * usableFrontier (S t) + β * (S t).capability
      - xi t ≤ usableFrontier (S (t + 1)))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : ∀ t, γ * k ^ 2 + (1 - ρ) * k
      + xi t / (S t).capability ≤ β)
    {t : ℕ}
    (hCpos : 0 < (S t).capability)
    (hcone : k * (S t).capability ≤ usableFrontier (S t)) :
    k * (S (t + 1)).capability ≤ usableFrontier (S (t + 1)) := by
  have hd := hdyn t
  have hb := hbeta t
  have hs := hstep t
  set C := (S t).capability with hC
  set D := usableFrontier (S t) with hD
  set C' := (S (t + 1)).capability with hC'
  set D' := usableFrontier (S (t + 1)) with hD'
  -- ключевая алгебра: D' − kC' ≥ (ρ−γk)(D−kC) + margin·C,
  -- где margin = β − γk² − (1−ρ)k − ξ/C ≥ 0, а ξ входит в D'
  have hkey : ρ * D + β * C - xi t - k * (C + γ * D)
      = (ρ - γ * k) * (D - k * C)
        + (β - (γ * k ^ 2 + (1 - ρ) * k + xi t / C)) * C := by
    field_simp
    ring
  have h1 : (0:ℝ) ≤ (ρ - γ * k) * (D - k * C) := by
    have hsub : (0:ℝ) ≤ D - k * C := by linarith [hcone]
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

/-- **State-closed двусторонняя полоса**: взлёт (R124-конус)
и насыщение (R125 PL-окно) вместе на полях состояния:

  C₀(1+γk)^T ≤ (S T).capability
    ≤ C* − (1−σ)^T·(C* − C₀).

Полный state-closed контракт роста HAGI: измеряемые поля,
пошаговые сертификаты, никаких shadow-последовательностей. -/
theorem state_closed_band (S : ℕ → GrowthState X)
    (γ ρ β k Cstar σ : ℝ)
    (hγ : 0 < γ) (hk : 0 < k) (hσ1 : σ ≤ 1)
    (hCpos : ∀ t, 0 < (S t).capability)
    (hstep : ∀ t, (S (t + 1)).capability
      = (S t).capability + γ * usableFrontier (S t))
    (hdyn : ∀ t, ρ * usableFrontier (S t) + β * (S t).capability
      ≤ usableFrontier (S (t + 1)))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (hcone0 : k * (S 0).capability ≤ usableFrontier (S 0))
    (hpl_up : ∀ t, (S (t + 1)).capability
      ≤ (S t).capability + σ * (Cstar - (S t).capability))
    (hpl_lo : ∀ t, (S t).capability
      + σ * (Cstar - (S t).capability) ≤ (S (t + 1)).capability)
    (hC0 : (S 0).capability ≤ Cstar) (T : ℕ) :
    (S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability
      ∧ (S T).capability
        ≤ Cstar - (1 - σ) ^ T * (Cstar - (S 0).capability) := by
  exact takeoff_with_saturation (fun t => (S t).capability)
    (fun t => usableFrontier (S t)) γ k Cstar σ hγ hk hσ1 hstep
    hpl_up hpl_lo
    (cone_ratio_invariant (fun t => (S t).capability)
      (fun t => usableFrontier (S t)) γ ρ β k hCpos hstep hdyn
      hrhogk hbeta hcone0) hC0 T

end Hagi
