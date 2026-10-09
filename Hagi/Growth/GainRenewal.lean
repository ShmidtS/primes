/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.Liveness
import Hagi.Foundations.Recurrence
set_option linter.style.header false

/-!
# GainRenewal — renewal gains and sustained takeoff

Under renewal semantics (each generation's gain `G t` produced
from its usable disagreement `D t`, `γ·D t ≤ G t ≤ γ·D t`;
`D (t+1) ≥ ρ·D t + inj − ξ`):

* `gain_renewal_recurrence`: `G (t+1) ≥ ρ·G t + γ·(inj − ξ)`;
* `gain_renewal_growth`: for `ρ < 1`, the closed form
  `G t ≥ ρ^t·G 0 + γ(inj − ξ)(1 − ρ^t)/(1 − ρ)`;
* `gain_renewal_floor_pos` / `gain_renewal_floor`: the stationary
  floor `γ(inj − ξ)/(1 − ρ) > 0`; every `t ≥ 1` has
  `G t ≥ γ(inj − ξ)`;
* `gain_renewal_growth_one`: for `ρ = 1`, linear growth
  `G t ≥ G 0 + γ(inj − ξ)·t`;
* `sustained_takeoff_window_lift`: with the additive step
  `C (t+1) = C t + G t` and gate `α·C t ≤ G t` at every t,
  `C 0·(1+α)^T ≤ C T`;
* `renewal_feeds_takeoff`: the same conclusion from the
  frontier-scaling hypothesis `α·C t ≤ γ·D t` (an empirical
  premise, not derived here);
* `bounded_frontier_no_sustained_growth`: if `G t ≤ γ·D t`,
  `D t ≤ D̄`, and the gate holds, then `C t ≤ γ·D̄/α`.
-/

open Real Finset

namespace Hagi

/-! ## The renewal semantics

Each generation's gain is produced from that generation's
measured usable disagreement by the linear harvest
`gainFromD γ D = γ·D`. The hypotheses quantify this:
`h_gain_prod` (lower bound), `h_gain_exact` (upper bound),
`h_D_renew` (the `diversity_floor` law). -/

/-- The linear harvest `gainFromD γ D = γ·D`; the theorems only
use the bounds `γ·D ≤ G` and `G ≤ γ·D`. -/
noncomputable def gainFromD (γ D : ℝ) : ℝ := γ * D

/-! ## The renewal recurrence -/

/-- If `0 < γ`, `0 ≤ ρ`, `γ·D t ≤ G t ≤ γ·D t` at every t, and
`D (t+1) ≥ ρ·D t + inj − ξ`, then
`ρ·G t + γ·(inj − ξ) ≤ G (t+1)`. Both bounds on `G` are
needed: with the lower bound alone the recurrence fails (a
one-off large gain satisfies `γ·D ≤ G` while decaying). -/
theorem gain_renewal_recurrence (G D : ℕ → ℝ) (γ ρ inj ξ : ℝ)
    (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_gain_exact : ∀ t, G t ≤ γ * D t)
    (h_D_renew : ∀ t, D (t + 1) ≥ ρ * D t + inj - ξ)
    (t : ℕ) :
    ρ * G t + γ * (inj - ξ) ≤ G (t + 1) := by
  have h1 := h_gain_prod (t + 1)
  have h2 := h_D_renew t
  have h3 : γ * (ρ * D t + inj - ξ) ≤ γ * D (t + 1) :=
    mul_le_mul_of_nonneg_left h2 hγ.le
  have h4 : ρ * G t ≤ ρ * (γ * D t) :=
    mul_le_mul_of_nonneg_left (h_gain_exact t) hρ
  have hrw : ρ * (γ * D t) + γ * (inj - ξ)
      = γ * (ρ * D t + inj - ξ) := by ring
  have hchain : ρ * (γ * D t) + γ * (inj - ξ) ≤ G (t + 1) := by
    calc ρ * (γ * D t) + γ * (inj - ξ)
        = γ * (ρ * D t + inj - ξ) := hrw
      _ ≤ γ * D (t + 1) := h3
      _ ≤ G (t + 1) := h1
  linarith [h4, hchain]

/-! ## Solving the recurrence -/

/-- Geometric-sum closed form: for ρ ≠ 1,
Σ_{i<t} ρ^i = (1 − ρ^t)/(1 − ρ). -/
private theorem geo_sum_mul (ρ : ℝ) (t : ℕ) :
    (1 - ρ) * ∑ i ∈ Finset.range t, ρ ^ i = 1 - ρ ^ t :=
  -- R197 dedup: = Foundations.Recurrence.geom_telescope
  Hagi.Foundations.geom_telescope ρ t

private theorem geo_sum_closed (ρ : ℝ) (hρ : ρ ≠ 1) (t : ℕ) :
    ∑ i ∈ Finset.range t, ρ ^ i = (1 - ρ ^ t) / (1 - ρ) := by
  field_simp
  rw [mul_comm]
  exact geo_sum_mul ρ t

/-- If `0 < γ`, `0 ≤ ρ < 1`, `ξ ≤ inj`, `0 ≤ ξ`, `0 ≤ inj`,
`γ·D t ≤ G t ≤ γ·D t`, and `D (t+1) ≥ ρ·D t + inj − ξ`, then
`ρ^t·G 0 + γ·(inj − ξ)·(1 − ρ^t)/(1 − ρ) ≤ G t`. -/
theorem gain_renewal_growth (G D : ℕ → ℝ) (γ ρ inj ξ : ℝ)
    (hγ : 0 < γ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (_hinj : ξ < inj) (hxi : 0 ≤ ξ) (hinj0 : 0 ≤ inj)
    (_hD0 : 0 ≤ D 0)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_gain_exact : ∀ t, G t ≤ γ * D t)
    (h_D_renew : ∀ t, D (t + 1) ≥ ρ * D t + inj - ξ)
    (t : ℕ) :
    ρ ^ t * G 0 + γ * (inj - ξ) * (1 - ρ ^ t) / (1 - ρ) ≤ G t := by
  have hd := diversity_floor D ρ inj ξ hρ hinj0 hxi h_D_renew t
  have hgd : γ * (ρ ^ t * D 0 + (inj - ξ) * ∑ i ∈ Finset.range t, ρ ^ i)
      ≤ G t := by
    calc γ * (ρ ^ t * D 0 + (inj - ξ) * ∑ i ∈ Finset.range t, ρ ^ i)
        ≤ γ * D t := mul_le_mul_of_nonneg_left hd hγ.le
      _ ≤ G t := h_gain_prod t
  have hrw : γ * (ρ ^ t * D 0 + (inj - ξ) * ∑ i ∈ Finset.range t, ρ ^ i)
      = ρ ^ t * (γ * D 0) + γ * (inj - ξ)
          * ∑ i ∈ Finset.range t, ρ ^ i := by ring
  rw [hrw] at hgd
  have hbump : ρ ^ t * G 0 ≤ ρ ^ t * (γ * D 0) :=
    mul_le_mul_of_nonneg_left (h_gain_exact 0) (pow_nonneg hρ t)
  have hgeom : ρ ^ t * G 0
      + γ * (inj - ξ) * ∑ i ∈ Finset.range t, ρ ^ i ≤ G t := by
    linarith [hgd, hbump]
  rw [geo_sum_closed ρ (ne_of_lt hρ1) t] at hgeom
  rw [← mul_div_assoc] at hgeom
  exact hgeom

/-- If `0 < γ`, `ρ < 1`, and `ξ < inj`, then
`0 < γ·(inj − ξ)/(1 − ρ)`. -/
theorem gain_renewal_floor_pos (γ ρ inj ξ : ℝ)
    (hγ : 0 < γ) (hρ1 : ρ < 1) (hinj : ξ < inj) :
    0 < γ * (inj - ξ) / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < γ * (inj - ξ) := by positivity
  exact div_pos h2 h1

/-- Geometric sums of a nonnegative base are at least 1 once
nonempty (the i = 0 term is ρ⁰ = 1). -/
private theorem geo_sum_ge_one (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ t : ℕ, t ≠ 0 → (1:ℝ) ≤ ∑ i ∈ Finset.range t, ρ ^ i := by
  intro t
  cases t with
  | zero => intro h; exact absurd rfl h
  | succ m =>
      intro _
      have hmem : (0:ℕ) ∈ Finset.range (m + 1) := by simp
      have hnn : ∀ i ∈ Finset.range (m + 1), (0:ℝ) ≤ ρ ^ i :=
        fun i _ => pow_nonneg hρ i
      simpa using Finset.single_le_sum hnn hmem

/-- If `0 < γ`, `0 ≤ ρ`, `ξ < inj`, `0 ≤ ξ`, `0 ≤ inj`,
`0 ≤ D 0`, `γ·D t ≤ G t`, `D (t+1) ≥ ρ·D t + inj − ξ`, and
`t ≠ 0`, then `γ·(inj − ξ) ≤ G t`. -/
theorem gain_renewal_floor (G D : ℕ → ℝ) (γ ρ inj ξ : ℝ)
    (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hinj : ξ < inj) (hxi : 0 ≤ ξ) (hinj0 : 0 ≤ inj)
    (hD0 : 0 ≤ D 0)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_D_renew : ∀ t, D (t + 1) ≥ ρ * D t + inj - ξ)
    (t : ℕ) (ht : t ≠ 0) :
    γ * (inj - ξ) ≤ G t := by
  have hd := diversity_floor D ρ inj ξ hρ hinj0 hxi h_D_renew t
  have hgd : γ * (ρ ^ t * D 0 + (inj - ξ) * ∑ i ∈ Finset.range t, ρ ^ i)
      ≤ G t := by
    calc γ * (ρ ^ t * D 0 + (inj - ξ) * ∑ i ∈ Finset.range t, ρ ^ i)
        ≤ γ * D t := mul_le_mul_of_nonneg_left hd hγ.le
      _ ≤ G t := h_gain_prod t
  have hge1 := geo_sum_ge_one ρ hρ t ht
  have e1 : (0:ℝ) ≤ γ * (ρ ^ t * D 0) := by positivity
  have e2 : γ * (ρ ^ t * D 0 + (inj - ξ) * ∑ i ∈ Finset.range t, ρ ^ i)
      = γ * (ρ ^ t * D 0)
        + (γ * (inj - ξ)) * ∑ i ∈ Finset.range t, ρ ^ i := by ring
  have e3 : γ * (inj - ξ)
      ≤ (γ * (inj - ξ)) * ∑ i ∈ Finset.range t, ρ ^ i := by
    have hc : 0 ≤ γ * (inj - ξ) := by positivity
    calc γ * (inj - ξ) = (γ * (inj - ξ)) * 1 := (mul_one _).symm
      _ ≤ (γ * (inj - ξ)) * ∑ i ∈ Finset.range t, ρ ^ i :=
          mul_le_mul_of_nonneg_left hge1 hc
  linarith [hgd, e1, e2, e3]

/-- If `0 < γ`, `γ·D t ≤ G t ≤ γ·D t`, and
`D (t+1) ≥ 1·D t + inj − ξ`, then
`G 0 + γ·(inj − ξ)·t ≤ G t`. -/
theorem gain_renewal_growth_one (G D : ℕ → ℝ) (γ inj ξ : ℝ)
    (hγ : 0 < γ)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_gain_exact : ∀ t, G t ≤ γ * D t)
    (h_D_renew : ∀ t, D (t + 1) ≥ 1 * D t + inj - ξ)
    (t : ℕ) :
    G 0 + γ * (inj - ξ) * t ≤ G t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hr := gain_renewal_recurrence G D γ 1 inj ξ hγ zero_le_one
        h_gain_prod h_gain_exact h_D_renew t
      have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
      have hsplit : G 0 + γ * (inj - ξ) * ((t : ℝ) + 1)
          = (G 0 + γ * (inj - ξ) * (t : ℝ)) + γ * (inj - ξ) := by ring
      rw [hcast, hsplit]
      linarith [hr]

/-! ## The R102 window lift -/

/-- If `0 < α`, `C (t+1) = C t + G t`, and `α·C t ≤ G t` at
every t, then `C 0·(1 + α)^T ≤ C T`. -/
theorem sustained_takeoff_window_lift (C G : ℕ → ℝ) (α : ℝ)
    (hα : 0 < α)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gate : ∀ t, α * C t ≤ G t)
    (T : ℕ) :
    C 0 * (1 + α) ^ T ≤ C T := by
  have hstep : ∀ t, C t * (1 + α) ≤ C (t + 1) := by
    intro t
    rw [h_step t]
    have h1 : C t * α ≤ G t := by
      rw [← mul_comm α (C t)]; exact h_gate t
    linarith
  have hpos : 0 < 1 + α := by linarith
  induction T with
  | zero => simp
  | succ T ih =>
      have hs := hstep T
      have hmul : C 0 * (1 + α) ^ T * (1 + α) ≤ C T * (1 + α) :=
        mul_le_mul_of_nonneg_right ih hpos.le
      rw [pow_succ (1 + α) T]
      nlinarith

/-- If `0 < α`, `C (t+1) = C t + G t`, `γ·D t ≤ G t`, and the
frontier-scaling hypothesis `α·C t ≤ γ·D t` holds at every t,
then `C 0·(1 + α)^T ≤ C T`. The scaling hypothesis is an
empirical premise, not derived here (see
`bounded_frontier_no_sustained_growth` for the converse under
a bounded frontier). -/
theorem renewal_feeds_takeoff (C G D : ℕ → ℝ) (α γ : ℝ)
    (hα : 0 < α)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_emp_frontier_scaling : ∀ t, α * C t ≤ γ * D t)
    (T : ℕ) :
    C 0 * (1 + α) ^ T ≤ C T :=
  sustained_takeoff_window_lift C G α hα h_step
    (fun t => le_trans (h_emp_frontier_scaling t) (h_gain_prod t)) T

/-- If `0 < α`, `G t ≤ γ·D t`, `D t ≤ D̄`, and `α·C t ≤ G t`,
then `C t ≤ γ·D̄/α`. -/
theorem bounded_frontier_no_sustained_growth (C G D : ℕ → ℝ)
    (α γ Dbar : ℝ)
    (hα : 0 < α) (hγ : 0 < γ)
    (h_gain_exact : ∀ t, G t ≤ γ * D t)
    (h_D_bound : ∀ t, D t ≤ Dbar)
    (h_gate : ∀ t, α * C t ≤ G t)
    (t : ℕ) :
    C t ≤ γ * Dbar / α := by
  have h1 : α * C t ≤ γ * D t :=
    le_trans (h_gate t) (h_gain_exact t)
  have h2 : γ * D t ≤ γ * Dbar :=
    mul_le_mul_of_nonneg_left (h_D_bound t) hγ.le
  exact (le_div_iff₀ hα).mpr (by linarith)

end Hagi
