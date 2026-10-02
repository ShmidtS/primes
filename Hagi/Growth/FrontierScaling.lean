/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.GainRenewal
set_option linter.style.header false

/-!
# R107: frontier scaling — the cone invariant D ≥ (α/γ)·C DERIVED from production dynamics

R104 closed with `renewal_feeds_takeoff`, whose remaining
empirical premise was the FREE hypothesis

  h_emp_frontier_scaling : ∀ t, α·C_t ≤ γ·D_t

— "usable disagreement scales with capability". This module
REPLACES that free hypothesis with a DERIVED dynamic invariant
(the audit front D proposal), making the remaining empirical
content explicit and measurable.

**The production dynamics.** The frontier (usable
disagreement) is no longer an exogenous constant-injection
stream (R104's `diversity_floor` law) but is PRODUCED BY the
growing system itself:

  D_{t+1} ≥ ρ·D_t + β·C_t − ξ_t

with ρ ≥ 0 the frontier retention, β the PRODUCTION rate (new
usable disagreement per unit of current capability — the model
itself surfaces new disagreement as it grows), and ξ_t ≥ 0 the
friction (absorption / consensus collapse / data loss). The
capability grows at most the certified rate per cycle,
C_{t+1} ≤ (1+α)·C_t (`h_C_cap`: the additive renewal law
C_{t+1} = C_t + G_t of R104 combined with the gate-certified
factor — the model does not leap ahead of its own certified
growth rate).

**The cone invariant.** With k := α/γ (the gate constant), the
cone D_t ≥ k·C_t is INDUCTIVE under the exact threshold

  β ≥ k·((1+α) − ρ) + ξ_t / C_t

(the production rate covers the cone's widening per cycle plus
the per-unit friction). Algebra: from D_t ≥ k·C_t,
D_{t+1} ≥ ρ·k·C_t + β·C_t − ξ_t, and we need this ≥ k·C_{t+1}
where k·C_{t+1} ≤ k·(1+α)·C_t; the slack is
C_t·(β − k((1+α)−ρ)) − ξ_t ≥ 0 — exactly the threshold.

Results:

* `frontier_cone_inductive` — the step lemma: cone at t +
  dynamics + cap + threshold ⟹ cone at t+1.
* `frontier_cone_invariant` — the induction: cone at 0 +
  per-step conditions ⟹ cone at EVERY t.
* `sustained_takeoff_from_production` — the composition with
  R104: the cone invariant SUPPLIES the gate α·C_t ≤ γ·D_t at
  every t, so `renewal_feeds_takeoff` applies — NO
  `h_emp_frontier_scaling` appears; the premises are the
  dynamics (ρ, β, ξ), the cap, the cone initial condition and
  the per-step threshold. Conclusion: C_T ≥ C₀·(1+α)^T for ALL
  T — THE sustained takeoff now DERIVED from the production
  dynamics, not assumed.
* `frontier_asymptotic` — the audit's asymptotic law made
  exact: if friction is PROPORTIONAL to capability
  (ξ_t ≤ ξ̄·C_t — the measured form), the per-step threshold
  collapses to the CONSTANT β ≥ k·((1+α) − ρ) + ξ̄.

**Honesty of what remains empirical** (this UPGRADES R104's
open bridge): (a) the production dynamics
D_{t+1} ≥ ρ·D_t + β·C_t − ξ_t itself — measurable from the
Diversity/GapLaw telemetry (per-generation usable-disagreement
change regressed on capability); (b) the constant threshold
β ≥ (α/γ)·(1+α−ρ) + ξ̄ being MET by the measured rates. Note
the audit's iff-correction (already in R104 and still exact
here): a BOUNDED frontier still kills sustained growth
(`bounded_frontier_no_sustained_growth`, R104) — the cone
condition is the exact BOUNDARY between the bounded-frontier
collapse and sustained takeoff: unbounded-but-slow frontier
(D growing sub-geometrically) fails the cone and hence the
gate. One more honesty point: under the renewal law
C_{t+1} = C_t + G_t with the derived gate α·C_t ≤ G_t AND the
cap C_{t+1} ≤ (1+α)·C_t, the gain is pinned to G_t = α·C_t —
the premises describe the system riding exactly its certified
rate; any slack appears as cap violations, which are excluded
by hypothesis, not derived.
-/

open Real Finset

namespace Hagi

/-! ## The cone step -/

/-- **The cone step (inductive base case machinery)**: with
k := α/γ, if the cone `D_t ≥ k·C_t` holds, the capability is
positive, the frontier obeys the production dynamics
`D_{t+1} ≥ ρ·D_t + β·C_t − ξ_t`, the capability grows at most
the certified rate `C_{t+1} ≤ (1+α)·C_t`, and the EXACT
threshold

  k·((1+α) − ρ) + ξ_t / C_t ≤ β

holds (production covers the cone's widening plus friction),
then the cone is preserved: `D_{t+1} ≥ k·C_{t+1}`. The
threshold is exact: with β below it the step fails (the
inequality chain is a chain of ⟹ whose slack is precisely
C_t·(β − k((1+α)−ρ)) − ξ_t). -/
theorem frontier_cone_inductive (C D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ) (t : ℕ)
    (hCpos : 0 < C t)
    (hcone : α / γ * C t ≤ D t)
    (h_dyn : ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : C (t + 1) ≤ (1 + α) * C t)
    (hβ : α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    α / γ * C (t + 1) ≤ D (t + 1) := by
  -- the cone lower-bounds the retained part
  have h1 : ρ * (α / γ * C t) ≤ ρ * D t :=
    mul_le_mul_of_nonneg_left hcone hρ
  -- the threshold, cleared of denominators (C_t > 0)
  have h2 : (α / γ * ((1 + α) - ρ)) * C t + ξ t ≤ β * C t := by
    have hm := mul_le_mul_of_nonneg_right hβ hCpos.le
    have e : (α / γ * ((1 + α) - ρ) + ξ t / C t) * C t
        = (α / γ * ((1 + α) - ρ)) * C t + ξ t := by
      field_simp
    rw [← e]
    exact hm
  -- the cap upper-bounds the demand by k·(1+α)·C_t
  have hk : 0 ≤ α / γ := div_nonneg hα.le hγ.le
  have h3 : α / γ * C (t + 1) ≤ α / γ * ((1 + α) * C t) :=
    mul_le_mul_of_nonneg_left h_C_cap hk
  -- k·(1+α)·C_t = k·((1+α)−ρ)·C_t + ρ·(k·C_t)
  have h4 : α / γ * ((1 + α) * C t)
      = (α / γ * ((1 + α) - ρ)) * C t + ρ * (α / γ * C t) := by
    ring
  linarith

/-! ## The cone invariant -/

/-- **The cone invariant (induction over t)**: with the cone at
t = 0 (`α/γ · C₀ ≤ D₀`), positivity of capability at every t,
and the per-step conditions of `frontier_cone_inductive`
holding at EVERY t (production dynamics, capability cap, and
the exact threshold
`α/γ·((1+α) − ρ) + ξ_t/C_t ≤ β`), the cone
`D_t ≥ (α/γ)·C_t` holds at EVERY t. This is the dynamic
invariant replacing R104's free `h_emp_frontier_scaling`. -/
theorem frontier_cone_invariant (C D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hCpos : ∀ t, 0 < C t)
    (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hβ : ∀ t, α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    ∀ t, α / γ * C t ≤ D t := by
  intro t
  induction t with
  | zero => exact h_cone0
  | succ t ih =>
      exact frontier_cone_inductive C D ξ α γ ρ β hα hγ hρ t
        (hCpos t) ih (h_dyn t) (h_C_cap t) (hβ t)

/-! ## The composition with R104 -/

/-- **Simultaneous positivity + cone by induction** (private
workhorse): under the composition hypotheses below,
`0 < C_t ∧ (α/γ)·C_t ≤ D_t` holds at every t. Positivity
cannot be separated from the cone here: the per-step threshold
divides by C_t, and positivity of C_{t+1} is itself derived
from the cone at t (C_{t+1} = C_t + G_t ≥ C_t + γ·D_t ≥
(1+α)·C_t > 0), so the two facts are proven together. -/
private theorem cone_and_pos (C G D ξ : ℕ → ℝ) (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC0 : 0 < C 0) (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hβ : ∀ t, 0 < C t → α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β) :
    ∀ t, 0 < C t ∧ α / γ * C t ≤ D t := by
  intro t
  induction t with
  | zero => exact ⟨hC0, h_cone0⟩
  | succ t ih =>
      obtain ⟨hpos, hcone⟩ := ih
      -- the gate at t from the cone: α·C_t = γ·(k·C_t) ≤ γ·D_t ≤ G_t
      have hg : γ * (α / γ * C t) ≤ G t :=
        le_trans (mul_le_mul_of_nonneg_left hcone hγ.le) (h_gain_prod t)
      have e : γ * (α / γ * C t) = α * C t := by
        field_simp
      rw [e] at hg
      have hA : 0 < α * C t := by positivity
      refine ⟨?_, frontier_cone_inductive C D ξ α γ ρ β hα hγ hρ t
        hpos hcone (h_dyn t) (h_C_cap t) (hβ t hpos)⟩
      rw [h_step t]
      linarith

/-- **Sustained takeoff FROM PRODUCTION DYNAMICS (R104's free
hypothesis replaced)**: under the renewal semantics of R104
(`C_{t+1} = C_t + G_t`, produced gain `γ·D_t ≤ G_t`) plus the
frontier PRODUCTION dynamics `D_{t+1} ≥ ρ·D_t + β·C_t − ξ_t`,
the capability cap `C_{t+1} ≤ (1+α)·C_t`, the cone initial
condition `(α/γ)·C₀ ≤ D₀`, and the exact per-step threshold

  (α/γ)·((1+α) − ρ) + ξ_t / C_t ≤ β,

the capability grows as C_T ≥ C₀·(1+α)^T for EVERY T.

NO `h_emp_frontier_scaling` appears: the gate α·C_t ≤ γ·D_t is
now the cone invariant `frontier_cone_invariant` DERIVED from
the (ρ, β, ξ) dynamics, and `renewal_feeds_takeoff` (R104) is
applied with the gate supplied. The remaining empirical
content is (a) the production dynamics itself (measurable from
Diversity/GapLaw telemetry) and (b) the threshold being met —
see `frontier_asymptotic` for its constant form. -/
theorem sustained_takeoff_from_production (C G D ξ : ℕ → ℝ)
    (α γ ρ β : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC0 : 0 < C 0)
    (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (hβ : ∀ t, α / γ * ((1 + α) - ρ) + ξ t / C t ≤ β)
    (T : ℕ) :
    C 0 * (1 + α) ^ T ≤ C T := by
  have hcp := cone_and_pos C G D ξ α γ ρ β hα hγ hρ hC0 h_cone0
    h_step h_gain_prod h_dyn h_C_cap (fun t _ => hβ t)
  have hCpos : ∀ t, 0 < C t := fun t => (hcp t).1
  have hcone := frontier_cone_invariant C D ξ α γ ρ β hα hγ hρ hCpos
    h_cone0 h_dyn h_C_cap hβ
  -- the gate, DERIVED from the cone: α·C_t = γ·((α/γ)·C_t) ≤ γ·D_t
  have hgate : ∀ t, α * C t ≤ γ * D t := by
    intro t
    have h1 : γ * (α / γ * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left (hcone t) hγ.le
    have e : γ * (α / γ * C t) = α * C t := by
      field_simp
    linarith
  exact renewal_feeds_takeoff C G D α γ hα h_step h_gain_prod hgate T

/-! ## The asymptotic (constant-threshold) corollary -/

/-- **The audit's asymptotic law made exact**: if the friction
is PROPORTIONAL to capability — `ξ_t ≤ ξ̄·C_t` for all t, the
measured form (friction telemetry scales with system size) —
then the per-step threshold
`(α/γ)·((1+α) − ρ) + ξ_t/C_t ≤ β` reduces to the CONSTANT

  (α/γ)·((1+α) − ρ) + ξ̄ ≤ β,

and the sustained takeoff C_T ≥ C₀·(1+α)^T follows for ALL T
from the dynamics alone. The audit's asymptotic
β ≳ k(1+α−ρ) (with ξ_t/C_t → 0) is the ξ̄ → 0 shadow of this
exact statement. -/
theorem frontier_asymptotic (C G D ξ : ℕ → ℝ)
    (α γ ρ β ξbar : ℝ)
    (hα : 0 < α) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hC0 : 0 < C 0)
    (h_cone0 : α / γ * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_dyn : ∀ t, ρ * D t + β * C t - ξ t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + α) * C t)
    (h_xibar : ∀ t, ξ t ≤ ξbar * C t)
    (h_beta_const : α / γ * ((1 + α) - ρ) + ξbar ≤ β)
    (T : ℕ) :
    C 0 * (1 + α) ^ T ≤ C T := by
  have hcp := cone_and_pos C G D ξ α γ ρ β hα hγ hρ hC0 h_cone0
    h_step h_gain_prod h_dyn h_C_cap
      (fun t ht => by
        have h := (div_le_iff₀ ht).mpr (h_xibar t)
        linarith [h, h_beta_const])
  have hCpos : ∀ t, 0 < C t := fun t => (hcp t).1
  have hcone : ∀ t, α / γ * C t ≤ D t := fun t => (hcp t).2
  have hgate : ∀ t, α * C t ≤ γ * D t := by
    intro t
    have h1 : γ * (α / γ * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left (hcone t) hγ.le
    have e : γ * (α / γ * C t) = α * C t := by
      field_simp
    linarith
  exact renewal_feeds_takeoff C G D α γ hα h_step h_gain_prod hgate T

end Hagi
