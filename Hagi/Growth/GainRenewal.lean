/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.GrowthBridge
import Hagi.Unified.Liveness
set_option linter.style.header false

/-!
# R104: gain renewal — disagreement→gain production + diversity floor ⟹ sustained takeoff

R102 proved `growth_state_takeoff_window`: with the gain field G
INVARIANT under `grow` (`growCycle_growGain`), the certified
exponential takeoff is a BOUNDED transient (success count ≤
1/α + 1 − C₀/G; certified factor ≤ exp(1 + α − αC₀/G)). The
audit's conclusion: sustained exponential growth requires GAIN
RENEWAL — a mechanism making the next gain PROPORTIONAL to the
current measured usable disagreement, so the success gate
α·C_t ≤ G_t is re-supplied every generation instead of being
spent once.

This module is that mechanism, as a conditional theorem chain
whose premises are the quantities the system already measures:

* **γ (harvest ratio)** — the produced gain per unit of usable
  disagreement: `γ·D_t ≤ G_t ≤ γ·D_t` (h_gain_prod +
  h_gain_exact — the harvest is the ONLY gain source). The Liveness chain
  (`liveness_merge`: ¬consensus ⇒ twoGap > 0) is the qualitative
  ancestor; γ is its quantitative form, measurable from the
  GapLaw/twoGap telemetry (the per-generation certified merge
  gain divided by the disagreement mass that produced it).
* **inj / ξ (fresh-data injection / leakage)** — from the
  Diversity telemetry, exactly the `diversity_floor` hypotheses:
  `D_{t+1} ≥ ρ·D_t + inj − ξ` with inj > ξ (h_D_renew).
* **ρ (retention)** — the fraction of usable disagreement that
  survives one generation.

Results (the chain):

* `gain_renewal_recurrence` — DERIVED, not assumed: under
  h_gain_prod and h_D_renew the produced gains satisfy the
  renewal recurrence `G_{t+1} ≥ ρ·G_t + γ(inj − ξ)`.
* `gain_renewal_growth` — the closed-form solution for ρ < 1:
  `G_t ≥ ρ^t·G₀ + γ(inj−ξ)(1−ρ^t)/(1−ρ)` — gains do NOT die;
  the stationary gain floor is `G_min = γ(inj−ξ)/(1−ρ) > 0`
  (`gain_renewal_floor_pos`, `gain_renewal_floor`: every
  generation t ≥ 1 has `G_t ≥ γ(inj−ξ)`, a strictly positive
  uniform floor — the quantitative `liveness_data_axis`).
* `gain_renewal_growth_one` — the ρ = 1 case: gains grow
  linearly, `G_t ≥ G₀ + γ(inj−ξ)·t`.
* `sustained_takeoff_window_lift` — the connection to R102: the
  window bound applies to a stretch where G is CONSTANT because
  the gate α·C_t ≤ G is spent once; under renewal semantics
  (`C_{t+1} = C_t + G_t`, the per-generation additive law with a
  PER-GENERATION gain) the gate hypothesis holds at EVERY t
  precisely while the produced gain covers it — and then
  `C_T ≥ C₀·(1+α)^T` for ALL T: the window constraint is lifted
  generation over generation.
* `renewal_feeds_takeoff` — the honest empirical bridge: the
  frontier-scaling hypothesis h_emp_frontier_scaling
  (`α·C_t ≤ γ·D_t` at every t — usable disagreement scales with
  capability) is exactly what converts the renewal floor into
  the gate. THIS is the remaining empirical premise: since
  C_t itself grows like (1+α)^t, the frontier must grow
  geometrically too — fresh data/discovery must grow WITH the
  system. PPT's `discovery_prob_lower` (stationary mass of the
  good set) is the candidate source of that scaling, not yet
  wired to D_t (open bridge, stated honestly).
* `bounded_frontier_no_sustained_growth` — the converse
  direction making the iff honest: if the frontier is BOUNDED
  (D_t ≤ D̄) and the gain is exactly the produced gain
  (γ·D_t ≤ G_t ≤ γ·D_t), then the gate forces
  `C_t ≤ γ·D̄/α` FOREVER — without frontier scaling there is no
  sustained takeoff. Sustained growth holds IFF the frontier
  (usable disagreement) scales with capability.
-/

open Real Finset

namespace Hagi

/-! ## The renewal semantics

The minimal extension of the loop semantics: each generation's
gain is PRODUCED from that generation's measured usable
disagreement by the concrete harvest map `gainFromD γ D = γ·D`
(the linear harvest; γ the measured harvest ratio). The
hypotheses below quantify this: h_gain_prod is the production
law (lower bound — the system may harvest more than γ·D, never
less), h_D_renew is the Diversity floor law verbatim. -/

/-- The concrete gain producer: the linear harvest of usable
disagreement D at harvest ratio γ (the measured per-unit merge
gain — `twoGap` per unit disagreement mass, from the GapLaw
telemetry). Kept concrete (no homogeneity/monotonicity axiom
layer): the theorems only ever use `G ≥ γ·D` and `G ≤ γ·D`. -/
noncomputable def gainFromD (γ D : ℝ) : ℝ := γ * D

/-! ## The renewal recurrence -/

/-- **The renewal recurrence (DERIVED, not assumed per-step)**:
if each generation's gain is produced from that generation's
disagreement at harvest ratio γ — EXACTLY: the producer is the
ONLY gain source, `γ·D_t ≤ G_t ≤ γ·D_t` (h_gain_prod /
`h_gain_exact`) — and the disagreement obeys the Diversity floor
law `D_{t+1} ≥ ρ·D_t + inj − ξ` (h_D_renew, ρ ≥ 0 retention),
then the produced gains satisfy

  G_{t+1} ≥ ρ·G_t + γ·(inj − ξ)

— each generation's gain floor is a constant fraction ρ of the
previous plus the harvested fresh injection γ(inj − ξ). This is
the quantitative form of the Liveness chain (D > 0 ⇒ G > 0):
now the gain is a recurrent quantity with an explicit floor
dynamics, not a one-off positivity statement.

**Why exactness is needed**: with only the LOWER bound the
recurrence is FALSE — a one-off large gain satisfies `γ·D ≤ G`
forever while decaying in relative terms; the floor propagates
only if the gain is REPRODUCED each generation (the harvest is
the only gain source). This is the renewal mechanism's content,
not a technicality. -/
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

/-- **The renewal recurrence solved (ρ < 1)**: under
h_gain_prod and h_D_renew with ρ ∈ [0, 1), strict injection
dominance inj > ξ, and exact production
(γ·D_t ≤ G_t ≤ γ·D_t — the harvest is the only gain source,
the produced gains satisfy the geometric-floor closed form

  G_t ≥ ρ^t·G₀ + γ(inj − ξ)·(1 − ρ^t)/(1 − ρ),

i.e. `G_t ≥ ρ^t·G₀ + G_min·(1 − ρ^t)` with the STATIONARY GAIN
FLOOR `G_min = γ(inj − ξ)/(1 − ρ)`. Gains do NOT die: however
many generations pass, the gain never falls below the level
the injection term refills each cycle. (Derived by harvesting
the `diversity_floor` law through γ, not by a fresh induction.) -/
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

/-- **The stationary gain floor is strictly positive**: with
strict injection dominance (inj > ξ, the Diversity telemetry
condition of `liveness_data_axis`), ρ ∈ [0,1) and γ > 0, the
limiting gain level `G_min = γ(inj − ξ)/(1 − ρ)` is strictly
positive — the renewal mechanism never lets the produced gain
decay to zero. -/
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

/-- **The uniform renewal floor**: every generation t ≥ 1
produces gain at least `γ(inj − ξ)` — a strictly positive
CONSTANT, independent of t and of D₀. This is the quantitative
`liveness_data_axis`: not merely D_T > 0, but a uniform
harvestable floor at every generation. -/
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

/-- **The renewal recurrence solved (ρ = 1)**: with full
retention, the produced gains grow LINEARLY —
`G_t ≥ G₀ + γ(inj − ξ)·t` — the injection term accumulates
instead of saturating. -/
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

/-- **The window constraint LIFTED (the R102 bridge)**: R102's
`growth_state_takeoff_window` bounds the certified takeoff
because a FIXED gain G is spent once by the gate α·C_t ≤ G.
Under the RENEWAL loop semantics — the per-generation additive
law `C_{t+1} = C_t + G_t` with each generation's gain G_t
PRODUCED (not inherited) — the gate hypothesis

  h_gate : α·C_t ≤ G_t  (every t)

is re-supplied every generation, and then the certified
takeoff factor is `(1+α)^T` for EVERY horizon T:

  C_T ≥ C₀·(1 + α)^T.

No window, no bound: the multiplicative law applies at every
cycle because each cycle's gate is paid for by that cycle's
produced gain. (The gate itself is not free — see
`renewal_feeds_takeoff` for when renewal supplies it, and
`bounded_frontier_no_sustained_growth` for when its supply
provably runs out.) -/
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

/-- **The frontier-scaling bridge (THE remaining empirical
premise, named)**: composing the renewal production
`h_gain_prod : γ·D_t ≤ G_t` with the FRONTIER-SCALING
hypothesis

  h_emp_frontier_scaling : α·C_t ≤ γ·D_t  (every t)

— usable disagreement scales with capability, i.e. the
stationary frontier level covers the gate's demand — yields the
gate of `sustained_takeoff_window_lift`, hence
`C_T ≥ C₀·(1+α)^T` for ALL T: sustained exponential growth.

**Honesty of the premise**: since C_t grows like (1+α)^t, the
frontier D_t must grow geometrically too (`D_t ≥ (α/γ)·C_t`):
fresh data / discovery must GROW WITH THE SYSTEM. A stationary
frontier (bounded D) does NOT satisfy it — and then
`bounded_frontier_no_sustained_growth` shows sustained takeoff
is impossible. PPT's `discovery_prob_lower` (the stationary
mass of the good discovery set) is the CANDIDATE source of the
scaling — connecting that mass to D_t is the open empirical
bridge, NOT a theorem here. Growth is sustained IFF the
frontier scales with capability. -/
theorem renewal_feeds_takeoff (C G D : ℕ → ℝ) (α γ : ℝ)
    (hα : 0 < α)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, γ * D t ≤ G t)
    (h_emp_frontier_scaling : ∀ t, α * C t ≤ γ * D t)
    (T : ℕ) :
    C 0 * (1 + α) ^ T ≤ C T :=
  sustained_takeoff_window_lift C G α hα h_step
    (fun t => le_trans (h_emp_frontier_scaling t) (h_gain_prod t)) T

/-- **The converse: no frontier scaling, no sustained takeoff**.
If the gain is exactly the produced harvest
(`γ·D_t ≤ G_t ≤ γ·D_t` — the producer is the only gain source),
the diversity is BOUNDED (`D_t ≤ D̄` — a stationary frontier),
and the gate holds at every t, then capability is bounded
FOREVER: `C_t ≤ γ·D̄/α`. So under the renewal semantics the
certified takeoff is sustained IFF the frontier scales with
capability (the h_emp_frontier_scaling of
`renewal_feeds_takeoff`) — this is the honest iff-form of
"sustained growth". -/
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
