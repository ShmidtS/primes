/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.ConeTakeoff

/-!
# ConeDynamics — abstract cone laws

* `ConeData`: carrier with capability `C`, frontier `D`, forcing `ξ`,
  and law constants `γ`, `ρ`, `β`.
* `cone_data_invariant` (cap form): one-step cone preservation
  under a capability cap `C (t+1) ≤ (1 + γk) * C t`.
* `frontier_cone_inductive_is_cone_data`: the FrontierScaling
  theorem `frontier_cone_inductive` as an instance of
  `cone_data_invariant` at `k = α / γ`.
* `cone_reinvest_invariant` (reinvest form): one-step cone
  preservation under a reinvest cap `C (t+1) ≤ C t + γ * D t`, with
  retention `γ * k ≤ ρ`.
* `cone_ratio_step_is_reinvest`: the RatioTakeoff theorem
  `cone_ratio_step` (exact step) as the equality case of
  `cone_reinvest_invariant`.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- The abstract cone-dynamics carrier: capability,
frontier, forcing, and the law constants. -/
structure ConeData where
  /-- capability channel. -/
  C : ℕ → ℝ
  /-- frontier channel. -/
  D : ℕ → ℝ
  /-- the forcing/friction term (losses that drain the
  frontier; ξ ≡ 0 recovers the zero-error cone). -/
  ξ : ℕ → ℝ
  γ : ℝ
  ρ : ℝ
  β : ℝ

/-- Cone step law with forcing and capability cap: given
`0 ≤ k`, `0 ≤ γ`, `0 ≤ ρ`, `0 < C t`, the cone
`k * C t ≤ D t`, the frontier dynamics
`ρ * D t + β * C t - ξ t ≤ D (t + 1)`, the cap
`C (t + 1) ≤ (1 + γ * k) * C t`, and the threshold
`k * ((1 + γ * k) - ρ) + ξ t / C t ≤ β`, the cone is preserved:
`k * C (t + 1) ≤ D (t + 1)`. -/
theorem cone_data_invariant (cd : ConeData) (k : ℝ) (t : ℕ)
    (hk : 0 ≤ k) (hγ : 0 ≤ cd.γ) (hρ : 0 ≤ cd.ρ)
    (hCpos : 0 < cd.C t)
    (hcone : k * cd.C t ≤ cd.D t)
    (h_dyn : cd.ρ * cd.D t + cd.β * cd.C t - cd.ξ t
      ≤ cd.D (t + 1))
    (h_C_cap : cd.C (t + 1) ≤ (1 + cd.γ * k) * cd.C t)
    (hβ : k * ((1 + cd.γ * k) - cd.ρ) + cd.ξ t / cd.C t
      ≤ cd.β) :
    k * cd.C (t + 1) ≤ cd.D (t + 1) := by
  have h1 : cd.ρ * (k * cd.C t) ≤ cd.ρ * cd.D t :=
    mul_le_mul_of_nonneg_left hcone hρ
  have h2 : (k * ((1 + cd.γ * k) - cd.ρ)) * cd.C t
      + cd.ξ t ≤ cd.β * cd.C t := by
    have hm := mul_le_mul_of_nonneg_right hβ hCpos.le
    have e : (k * ((1 + cd.γ * k) - cd.ρ)
        + cd.ξ t / cd.C t) * cd.C t
        = (k * ((1 + cd.γ * k) - cd.ρ)) * cd.C t + cd.ξ t := by
      field_simp
    rw [← e]
    exact hm
  have hkγ : 0 ≤ k * cd.γ := mul_nonneg hk hγ
  have h3 : k * cd.C (t + 1) ≤ k * ((1 + cd.γ * k) * cd.C t) :=
    mul_le_mul_of_nonneg_left h_C_cap hk
  have h4 : k * ((1 + cd.γ * k) * cd.C t)
      = (k * ((1 + cd.γ * k) - cd.ρ)) * cd.C t
        + cd.ρ * (k * cd.C t) := by ring
  linarith

/-- `frontier_cone_inductive` from `Hagi.Growth.FrontierScaling`
as an instance of `cone_data_invariant` with `k = α / γ`:
under the same hypotheses, `α / γ * C (t + 1) ≤ D (t + 1)`. -/
theorem frontier_cone_inductive_is_cone_data
    (C D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (t : ℕ)
    (hCpos : 0 < C t)
    (hcone : α / γ * C t ≤ D t)
    (h_dyn : ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : C (t + 1) ≤ (1 + α) * C t)
    (hβ : α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    α / γ * C (t + 1) ≤ D (t + 1) := by
  have hcap : C (t + 1) ≤ (1 + γ * (α / γ)) * C t := by
    have hgg : γ * (α / γ) = α := by
      field_simp
    rw [hgg]
    exact h_C_cap
  have hthr : α / γ * ((1 + γ * (α / γ)) - ρ) + ξ t / C t ≤ β := by
    have hgg : γ * (α / γ) = α := by field_simp
    rw [hgg]
    exact hβ
  exact cone_data_invariant
    { C := C, D := D, ξ := ξ, γ := γ, ρ := ρ, β := β }
    (α / γ) t
    (div_nonneg hα.le hγ.le)
    hγ.le hρ hCpos hcone h_dyn hcap hthr


/-! ## The reinvest-form cone law -/

/-- Cone step law in reinvest form: given `0 < C t`, `0 ≤ k`,
retention `γ * k ≤ ρ`, the cone `k * C t ≤ D t`, the frontier
dynamics `ρ * D t + β * C t ≤ D (t + 1)`, the reinvest cap
`C (t + 1) ≤ C t + γ * D t`, and the threshold
`γ * k ^ 2 + (1 - ρ) * k ≤ β`, the cone is preserved:
`k * C (t + 1) ≤ D (t + 1)`. -/
theorem cone_reinvest_invariant (C D : ℕ → ℝ) (γ ρ β k : ℝ)
    (t : ℕ) (hCpos : 0 < C t) (hk : 0 ≤ k)
    (hrho : γ * k ≤ ρ)
    (hcone : k * C t ≤ D t)
    (h_dyn : ρ * D t + β * C t - 0 ≤ D (t + 1))
    (h_cap : C (t + 1) ≤ C t + γ * D t)
    (hβ : γ * k ^ 2 + (1 - ρ) * k ≤ β) :
    k * C (t + 1) ≤ D (t + 1) := by
  have hkey : ρ * D t + β * C t - k * (C t + γ * D t)
      = (ρ - γ * k) * (D t - k * C t)
        + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t := by
    field_simp
    ring
  have h1 : (0:ℝ) ≤ (ρ - γ * k) * (D t - k * C t) := by
    have hsub : (0:ℝ) ≤ D t - k * C t := by linarith [hcone]
    exact mul_nonneg (by linarith [hrho]) hsub
  have h2 : (0:ℝ) ≤ (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t :=
    mul_nonneg (by linarith [hβ]) hCpos.le
  have hkC : k * C (t + 1) ≤ k * (C t + γ * D t) :=
    mul_le_mul_of_nonneg_left h_cap hk
  have h3 : D (t + 1) - k * C (t + 1)
      ≥ (ρ - γ * k) * (D t - k * C t)
        + (β - (γ * k ^ 2 + (1 - ρ) * k)) * C t := by
    linarith [h_dyn, hkey, hkC]
  linarith

/-- `cone_ratio_step` (exact step `C (t + 1) = C t + γ * D t`,
zero forcing) as the equality case of `cone_reinvest_invariant`:
under the same hypotheses, `k * C (t + 1) ≤ D (t + 1)`. -/
theorem cone_ratio_step_is_reinvest (C D : ℕ → ℝ)
    (γ ρ β k : ℝ) {t : ℕ} (hk : 0 ≤ k)
    (hstep : C (t + 1) = C t + γ * D t)
    (hdyn : ρ * D t + β * C t ≤ D (t + 1))
    (hrhogk : γ * k ≤ ρ)
    (hbeta : γ * k ^ 2 + (1 - ρ) * k ≤ β)
    (hCpos : 0 < C t) (hcone : k * C t ≤ D t) :
    k * C (t + 1) ≤ D (t + 1) :=
  cone_reinvest_invariant C D γ ρ β k t hCpos
    hk hrhogk hcone
    (by linarith [hdyn]) (le_of_eq hstep) hbeta

end Hagi.Growth
