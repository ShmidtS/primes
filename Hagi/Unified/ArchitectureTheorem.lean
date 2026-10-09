/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Autonomy.Universality
import Hagi.Foundations.ConeTakeoff
import Hagi.Foundations.Recurrence
import Hagi.Growth.StateClosedRenewal
import Hagi.Growth.Saturation
import Hagi.Step.SafeQPPL
import Hagi.Ensemble.MergePrice
import Hagi.Ensemble.DistillTransfer
set_option linter.style.header false

/-!
# HAGI Synthesis — horizon-form capstone

All step premises are quantified over the horizon only
(`t ∈ Finset.range T`); `Cstar` and `sigma` are certificate
parameters. The T3 operator premise is an abstract measured
gain stream `g : ℕ → ℝ` (nats/step). Truncated band lemmas
(`cone_invariant_trunc`, `takeoff_lower_trunc`,
`pl_gap_lower_trunc`) prove the growth band from
horizon-only premises; `band_witness` exhibits a concrete
numeric pair satisfying the truncated band premises, so
`hagi_synthesis` is not vacuous. The certificate is usable
while `C0 * (1 + gamma * k) ^ T ≤ Cstar`.
-/

open Finset

namespace Hagi

variable {Xs V : Type*} [NormedAddCommGroup Xs]
  [InnerProductSpace ℝ Xs]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Truncated cone invariant: from the cone at 0 and
horizon-only step/dynamics premises, D t >= k * C t holds
for every t <= T. -/
theorem cone_invariant_trunc (C D : ℕ → ℝ) (γ ρ β k : ℝ) (T : ℕ)
    (hCpos : ∀ t ∈ Finset.range (T + 1), 0 < C t)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + γ * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (hcone0 : k * C 0 ≤ D 0) :
    ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t := Foundations.cone_invariant_horizon C D γ ρ β k T
    hCpos hstep hdyn hrhogk hbeta hcone0

/-- Truncated takeoff lower bound: C T >= C 0 * (1+gamma k)^T
from horizon-only premises (steps t < T only). -/
theorem takeoff_lower_trunc (C D : ℕ → ℝ) (γ k : ℝ) (T : ℕ)
    (hγ : 0 ≤ γ) (hk : 0 ≤ k)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + γ * D t)
    (hcone : ∀ t ∈ Finset.range (T + 1), k * C t ≤ D t) :
    C 0 * (1 + γ * k) ^ T ≤ C T := Foundations.takeoff_from_cone C D γ k T
    (mul_nonneg hγ hk) hγ hk hstep hcone

/-- Truncated band UPPER bound: from the upper PL form at
steps t < T, (1-sigma)^T * (Cstar - C 0) <= Cstar - C T,
i.e. C T <= Cstar - (1-sigma)^T * (Cstar - C 0). -/
theorem pl_gap_lower_trunc (C : ℕ → ℝ) (Cstar σ : ℝ) (T : ℕ)
    (hσ1 : σ ≤ 1)
    (hpl_up : ∀ t ∈ Finset.range T,
      C (t + 1) ≤ C t + σ * (Cstar - C t)) :
    (1 - σ) ^ T * (Cstar - C 0) ≤ Cstar - C T := by
  have hgapstep : ∀ t < T,
      (1 - σ) * (Cstar - C t) ≤ Cstar - C (t + 1) := by
    intro t ht
    have h := hpl_up t (Finset.mem_range.mpr ht)
    have hE : (1 - σ) * (Cstar - C t)
        = Cstar - C t - σ * (Cstar - C t) := by ring
    rw [hE]
    linarith [h]
  have hσ0 : (0:ℝ) ≤ 1 - σ := by linarith
  exact Hagi.Foundations.recurrence_lower (1 - σ)
    (fun t => Cstar - C t) T hσ0 hgapstep

/-- Пошаговые сертификаты цикла HAGI на горизонте `T`
(измеряемые h_emp_-посылки): рост (шаг состояния и динамика
фронтира с gain-потоком `g`), конус, PL-окно с параметрами
`Cstar` и `sigma`, Hedge-универсальность и суммируемый
дрейф. Все посылки квантифицированы только по
`t < T`; выполнимость — пока
`C0 * (1 + gamma * k) ^ T ≤ Cstar` (см. `band_witness`). -/
structure HAGICert (S : ℕ → GrowthState Xs)
    (g : ℕ → ℝ)
    (risk : ℕ → Fin 1 → ℝ) (best : Fin 1 → ℝ) (r : ℕ → ℝ)
    (γ ρ k ξ ηT Cstar σ ε0 ρe R : ℝ) (T : ℕ) where
  hCpos : ∀ t ∈ Finset.range (T + 1), 0 < (S t).capability
  hstep : ∀ t ∈ Finset.range T, (S (t + 1)).capability
    = (S t).capability + γ * usableFrontier (S t)
  hop : ∀ t ∈ Finset.range T, ρ * usableFrontier (S t)
    + ηT * g t - ξ
      ≤ usableFrontier (S (t + 1))
  hsuff : ∀ t ∈ Finset.range T, γ * k ^ 2 * (S t).capability
    + (1 - ρ) * k * (S t).capability + ξ
    ≤ ηT * g t
  hrhogk : γ * k ≤ ρ
  hcone0 : k * (S 0).capability ≤ usableFrontier (S 0)
  hpl_up : ∀ t ∈ Finset.range T, (S (t + 1)).capability
    ≤ (S t).capability + σ * (Cstar - (S t).capability)
  hpl_lo : ∀ t ∈ Finset.range T, (S t).capability
    + σ * (Cstar - (S t).capability) ≤ (S (t + 1)).capability
  hCstar : 0 < Cstar
  hσ0 : 0 < σ
  hσ1 : σ ≤ 1
  hC0 : (S 0).capability ≤ Cstar
  hrisk : ∀ t ∈ Finset.range T,
    risk t (0 : Fin 1) ≤ best (0 : Fin 1) + r t + ε0 * ρe ^ t
  hregret : ∑ t ∈ Finset.range T, r t ≤ R
  hε0 : 0 ≤ ε0
  hρe : 0 ≤ ρe
  hρe1 : ρe < 1

/-- При сертификате `HAGICert` на горизонте `T` одновременно:
`C0 * (1 + γk) ^ T ≤ C_T ≤ Cstar − (1−σ)^T · (Cstar − C0)`
и `Σ risk ≤ T * best + R + ε0 / (1 − ρe)`. -/
theorem hagi_synthesis (S : ℕ → GrowthState Xs)
    (g : ℕ → ℝ)
    (risk : ℕ → Fin 1 → ℝ) (best : Fin 1 → ℝ) (r : ℕ → ℝ)
    (γ ρ k ξ ηT Cstar σ ε0 ρe R : ℝ) (T : ℕ)
    (hγ : 0 < γ) (hk : 0 < k)
    (cert : HAGICert S g risk best r
      γ ρ k ξ ηT Cstar σ ε0 ρe R T) :
    ((S 0).capability * (1 + γ * k) ^ T ≤ (S T).capability
      ∧ (S T).capability
        ≤ Cstar - (1 - σ) ^ T * (Cstar - (S 0).capability))
    ∧ (∑ t ∈ Finset.range T, risk t (0 : Fin 1)
      ≤ T * best (0 : Fin 1) + R + ε0 / (1 - ρe)) := by
  obtain ⟨hCpos, hstep, hop, hsuff, hrhogk, hcone0, hpl_up,
    hpl_lo, hCstar, hσ0, hσ1, hC0, hrisk, hregret, hε0,
    hρe, hρe1⟩ := cert
  constructor
  · -- полоса роста: динамика на горизонте ⟹ конус
    have hdyn : ∀ t ∈ Finset.range T,
        ρ * usableFrontier (S t)
        + (γ * k ^ 2 + (1 - ρ) * k) * (S t).capability
        ≤ usableFrontier (S (t + 1)) := by
      intro t ht
      have h1 := hop t ht
      have h2 := hsuff t ht
      linarith
    have hcone := cone_invariant_trunc
      (fun t => (S t).capability)
      (fun t => usableFrontier (S t))
      γ ρ (γ * k ^ 2 + (1 - ρ) * k) k T
      hCpos hstep hdyn hrhogk
      (by linarith) hcone0
    constructor
    · exact takeoff_lower_trunc
        (fun t => (S t).capability)
        (fun t => usableFrontier (S t)) γ k T
        (le_of_lt hγ) (le_of_lt hk) hstep hcone
    · have hband := pl_gap_lower_trunc
        (fun t => (S t).capability) Cstar σ T hσ1 hpl_up
      linarith
  · exact universality_longhorizon risk best r (0 : Fin 1) R ε0 ρe
      hrisk hregret hε0 hρe hρe1

/-- The powers of 1/2 stay in [0,1]. -/
theorem half_pow_bounds (t : ℕ) :
    0 < (1/2 : ℝ) ^ t ∧ (1/2 : ℝ) ^ t ≤ 1 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [pow_succ]
      obtain ⟨h0, h1⟩ := ih
      constructor
      · positivity
      · nlinarith

/-- Powers of 1/2 are antitone in the exponent. -/
theorem half_pow_anti (t s : ℕ) (h : s ≤ t) :
    (1/2 : ℝ) ^ t ≤ (1/2 : ℝ) ^ s := by
  induction t with
  | zero =>
      have hs : s = 0 := Nat.le_zero.mp h
      subst hs
      rfl
  | succ t ih =>
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · have hstep := ih (by omega)
        have hp : 0 < (1/2 : ℝ) ^ s := by positivity
        rw [pow_succ]
        nlinarith
      · have hseq : s = t + 1 := by omega
        rw [hseq]

/-- A concrete witness of the truncated band premises
(`C t = 100 − 99·(1/2)^t`, `D t = 990·(1/2)^t`,
`Cstar = 100`, `sigma = 1/2`, `gamma = 1/20`,
`k = 1/1000`, any `T ≤ 10`): step, dynamics, cone, and PL
window all hold, so the horizon certificate is satisfiable.
The risk/Hedge side is supplied by the measured layer. -/
theorem band_witness :
    (∀ T ≤ 10,
      (∀ t ∈ Finset.range T,
          (100 - 99 * (1/2 : ℝ) ^ (t + 1))
            = (100 - 99 * (1/2 : ℝ) ^ t)
              + (1/20) * (990 * (1/2 : ℝ) ^ t))
        ∧ (∀ t ∈ Finset.range T,
          (1/20000) * (990 * (1/2 : ℝ) ^ t)
            + ((1/20) * (1/1000) ^ 2
                + (1 - 1/20000) * (1/1000))
                * (100 - 99 * (1/2 : ℝ) ^ t)
            ≤ 990 * (1/2 : ℝ) ^ (t + 1))
        ∧ (∀ t ∈ Finset.range (T + 1),
          (1/1000) * (100 - 99 * (1/2 : ℝ) ^ t)
            ≤ 990 * (1/2 : ℝ) ^ t)
        ∧ (∀ t ∈ Finset.range T,
          (100 - 99 * (1/2 : ℝ) ^ t)
            + (1/2) * (100 - (100 - 99 * (1/2 : ℝ) ^ t))
            ≤ 100 - 99 * (1/2 : ℝ) ^ (t + 1)
            ∧ 100 - 99 * (1/2 : ℝ) ^ (t + 1)
              ≤ (100 - 99 * (1/2 : ℝ) ^ t)
                + (1/2)
                  * (100 - (100 - 99 * (1/2 : ℝ) ^ t)))) := by
  intro T _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t _
    rw [pow_succ]
    field_simp
    ring
  · -- dynamics: 0.00005*D + beta*C <= D'
    intro t _
    -- t < T <= 10  =>  h := (1/2)^t >= (1/2)^9
    have ht9 : t ≤ 9 := by
      have hmem := Finset.mem_range.mp ‹t ∈ Finset.range T›
      have := ‹T ≤ 10›
      omega
    have hlo : (1/512 : ℝ) ≤ (1/2 : ℝ) ^ t := by
      have hanti := half_pow_anti 9 t ht9
      norm_num at hanti ⊢
      linarith
    have hC100 : 100 - 99 * (1/2 : ℝ) ^ t ≤ 100 := by linarith
    rw [show 990 * (1/2 : ℝ) ^ (t + 1)
        = 495 * (1/2 : ℝ) ^ t from by
      rw [pow_succ]
      ring]
    linarith
  · intro t _
    have hlo : (1/1024 : ℝ) ≤ (1/2 : ℝ) ^ t := by
      have ht10 : t ≤ 10 := by
        have hmem := Finset.mem_range.mp ‹t ∈ Finset.range (T + 1)›
        omega
      have hanti := half_pow_anti 10 t ht10
      norm_num at hanti ⊢
      linarith
    have hC100 : 100 - 99 * (1/2 : ℝ) ^ t ≤ 100 := by linarith
    linarith
  · intro t _
    -- PL window: EXACT equality at sigma = 1/2
    constructor
    · rw [pow_succ]
      field_simp
      have h0 := (half_pow_bounds t).1
      linarith
    · rw [pow_succ]
      field_simp
      have h0 := (half_pow_bounds t).1
      linarith

end Hagi
