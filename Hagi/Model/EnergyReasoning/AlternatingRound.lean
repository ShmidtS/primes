/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.EnergyReasoning.AttentionCoupling
import Hagi.Model.EnergyReasoning.GreedyTermination
import Hagi.Probability.MirrorHedgeCertificates

set_option linter.style.header false

/-!
# Alternating (z, y) round: strict descent with an inexact latent

Track B4 (master-plan-v3 addendum A11 B4: "alternating minimization
with summable errors ... важно не выдавать текущий frozen-z result
за joint convergence"). DESIGN-FIRST beat: the joint latent-visible
descent is organized as ALTERNATING ROUNDS with per-round
tolerances (route R1 of `.tmp/C293/design.md`):

  round t = z-phase (settle `z` toward `z*` to tolerance η_t) +
            y-phase (one guarded visible move on computed
            `K(z_t)`-fields with the COMPOSED guard).

Structural fact driving the design: `latentUpdate N m G` and
`latentEnergy N m G` do NOT depend on the visible state `y`, so the
latent fixed point `z*` is STATIC across rounds — the coupling is
one-way (z → visible through `attentionK`). Route R2 (small-gain
floor `ε_round/(1−q)`) degenerates to R1's slack inequality in this
regime (no moving latent target ⇒ no nonzero asymptotic floor);
route R3 (joint Lyapunov `E_vis + c·‖z−z*‖²`) would need the
z-differentiability that the E3 protocol forbids claiming.

Main results:

* `alternating_round_nonincreasing` — (B4 MAIN, ROUND THEOREM,
  strict form) one full z-then-y round with an INEXACT latent: if
  the z-phase delivers `‖z_t − z*‖ ≤ η` (premise-form: contracted
  through the declared softmax-Lipschitz premise
  `hsoft : |w(z_t) − w(z*)| ≤ Lsm·η`, delivery lemma
  `LatentEnergy.latent_settle_tolerance`), the computed fields
  `L̂` of the `K(z_t)`-energy carry numerical error ≤ ε (C270
  premise), and the computed margin clears the COMPOSED slack
  `2·(ε + |S_i|·2κmax·fmax·L_sm·η)` (C270's 2ε plus C271's coupling
  bound), then the visible energy at the TRUE frozen-z* kernel
  `pairwiseEnergy B (attentionK κ w(z*) f)` STRICTLY decreases
  across the round. Composition of `guarded_energy_delta` with
  `latent_error_couples_field` via the triangle inequality — the
  frozen statements are used, not restated. Additive over C271's
  `latent_attention_guarded_drop`: the SEPARATE numerical ε on top
  of the coupling η and the round packaging.
* `alternating_zphase_one_step_error` — (B4 η-bookkeeping brick)
  one z-phase step from ANY state contracts the latent error:
  `‖latentUpdate N m G z − z*‖ ≤ (Δ/m)·‖z − z*‖` for a fixed point
  `z*` — per-round tolerances satisfy η_t ≤ q·η_{t−1}, q = Δ/m,
  WITHOUT restarting (the summability input of the R1 design).
* `alternating_round_slack_summable` — (B4 N1, C294) ROUND-ERROR
  SUMMABILITY: a round-guard slack sequence with premise-form
  geometric decay `slack (t+1) ≤ (Δ/m)·slack t` (delivered for
  the coupling part by `alternating_zphase_one_step_error`) has
  ALL partial sums bounded by the geometric budget
  `slack 0 · m/(m−Δ)`.
* `alternating_trajectory_bound` / `alternating_trajectory_
descent_budget` — (B4 N2, C294) TRAJECTORY TELESCOPING: rounds
  each dropping `d t` (premise-form) telescope to
  `E (y N) ≤ E (y 0) − Σ d t`; with a bounded-below PREMISE
  `Emin ≤ E (y t)` the total descent is budgeted by
  `E (y 0) − Emin` (the floor is a hypothesis, not a conclusion).
* `alternating_rounds_converge` — (B4 N3, C294) TERMINAL FINITE
  FORM: on a finite configuration space, strictly-decreasing
  alternating rounds terminate (length ≤ card of the energy
  image) — the C268 ranking bound reused; the unconditional
  analytic convergence stays OPEN (pinned negative).

## Honest boundaries (B4)

* PREMISE-FORM throughout: the z-phase inexactness (η, `hsoft`) and
  the numerical field error (ε) are HYPOTHESES, not conclusions;
  the softmax-Lipschitz step remains a declared premise (C271
  honesty inherited), and rejection below the slack carries no
  information (C270 honesty inherited).
* NO UNCONDITIONAL joint `(z, y)` convergence theorem exists or is
  claimed: the names `alternating_round_converges` and
  `visible_descent_joint_z` are NONEXISTENT (RootApi negative
  pins). What is proven: ONE round, strictly, under premises. The
  chain/summability follow-ups are the recorded next statements
  (N1 round chain nonincrease, N2 η_t summability, N3 bounded-below
  round decreases) — none of them claimed here.
* The latent block of a round is inexact but STATIC-TARGETED: the
  y-independence of `z*` is why no `ε_round/(1−q)` floor appears;
  if the latent energy ever becomes y-dependent, R2's small-gain
  machinery becomes necessary and this file's design must be
  revisited (design doc records the dispositions).
* C294 convergence lift (N1–N3) stays PREMISE-FORM and FINITE:
  the geometric slack decay and the per-round drops are HYPOTHESES;
  the energy floor `Emin` is a PREMISE; the terminal statement is
  the FINITE/STRICT form only (length bound via the C268 ranking
  argument). The UNCONDITIONAL analytic convergence statement
  `alternating_round_converges` STILL does not exist and stays
  OPEN (RootApi negative pin unchanged); the near-name
  `alternating_rounds_converge` (plural) is the finite terminal
  form and states termination, NOT convergence to a minimizer.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (localField pairwiseEnergy)

/-! ## The round theorem -/
section Round

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*}

/-- **`alternating_round_nonincreasing`** — (B4 MAIN, ROUND THEOREM,
strict form) one full z-then-y round with an inexact latent: with
the z-phase settled-state weights `w1 = w(z_t)` within `Lsm·η` of
the fixed-point weights `w2 = w(z*)` (premise-form delivery: η is
the settle tolerance of `latent_settle_tolerance`, composed through
the declared softmax-Lipschitz premise), computed fields `L̂` of the
`K(z_t)`-energy within ε of the exact ones (C270 numerical
premise), and the computed margin clearing the COMPOSED slack
`2·(ε + |S_i|·2κmax·fmax·(Lsm·η))`, the visible energy at the TRUE
frozen-z* kernel STRICTLY decreases across the round. -/
theorem alternating_round_nonincreasing [Nonempty α]
    (B : ι → α → ℝ) (κ : ι → ι → ℝ) (w1 w2 : ι → ι → ℝ) (f : α → α → ℝ)
    {κmax fmax Lsm η ε : ℝ} (hκ : ∀ i j, 0 ≤ κ i j ∧ κ i j ≤ κmax)
    (hf : ∀ a b, |f a b| ≤ fmax)
    (hε : 0 ≤ ε)
    (hsoft : ∀ i j, |w1 i j - w2 i j| ≤ Lsm * η)
    (y : ι → α) (i : ι) (a : α) (Lhat : ι → α → ℝ)
    (herr : ∀ b, |Lhat i b - localField B (attentionK κ w1 f) y i b| ≤ ε)
    (hguard : 2 * (ε + ((Finset.univ \ {i}).card : ℝ)
        * (2 * κmax * fmax * (Lsm * η)))
      < Lhat i (y i) - Lhat i a) :
    pairwiseEnergy B (attentionK κ w2 f) (Function.update y i a)
      < pairwiseEnergy B (attentionK κ w2 f) y := by
  have hfmax : (0:ℝ) ≤ fmax := le_trans (abs_nonneg (f (Classical.arbitrary α)
    (Classical.arbitrary α))) (hf _ _)
  have hκmax : (0:ℝ) ≤ κmax := le_trans (hκ i i).1 (hκ i i).2
  have hLη : (0:ℝ) ≤ Lsm * η := le_trans (abs_nonneg _) (hsoft i i)
  set C : ℝ := ((Finset.univ \ {i}).card : ℝ) * (2 * κmax * fmax * (Lsm * η))
    with hC
  have hC0 : (0:ℝ) ≤ C :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hκmax) hfmax) hLη)
  have htot : ∀ b, |Lhat i b - localField B (attentionK κ w2 f) y i b| ≤ ε + C := by
    intro b
    have h1 := herr b
    have h2 := latent_error_couples_field B κ w1 w2 f hκ hf hsoft y i b
    calc |Lhat i b - localField B (attentionK κ w2 f) y i b|
        = |(Lhat i b - localField B (attentionK κ w1 f) y i b)
            + (localField B (attentionK κ w1 f) y i b
                - localField B (attentionK κ w2 f) y i b)| := by ring_nf
      _ ≤ |Lhat i b - localField B (attentionK κ w1 f) y i b|
          + |localField B (attentionK κ w1 f) y i b
              - localField B (attentionK κ w2 f) y i b| := abs_add_le _ _
      _ ≤ ε + C := by linarith
  exact guarded_energy_delta B (attentionK κ w2 f)
    (attention_K_symmetric κ w2 f) y i a Lhat (ε + C)
    (by linarith) htot hguard

end Round

/-! ## The η-bookkeeping brick -/
section ZPhase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`alternating_zphase_one_step_error`** — (B4 η-bookkeeping
brick) one z-phase step contracts the latent error toward the
(y-independent, static) fixed point: for `latentUpdate N m G zstar =
zstar`, `‖latentUpdate N m G z − zstar‖ ≤ (Δ/m)·‖z − zstar‖`. This
is the summability input of the R1 design (per-round tolerance
η_t ≤ q·η_{t−1}, q = Δ/m, without restarting the settle loop); the
summable-series statement itself is NOT claimed here. -/
theorem alternating_zphase_one_step_error (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar z : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ‖latentUpdate N m G z - zstar‖ ≤ ((Δ : ℝ) / m) * ‖z - zstar‖ := by
  have h := latent_update_contraction N m G hΔ hm z zstar
  rw [hz] at h
  exact h

end ZPhase

/-! ## N1: round-error summability (geometric slack budget) -/
section SlackSummable

private theorem slack_partial_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (slack : ℕ → ℝ) (hs0 : 0 ≤ slack 0)
    (hslack : ∀ t, slack (t + 1) ≤ q * slack t) (N : ℕ) :
    ∑ t ∈ Finset.range N, slack t
      ≤ slack 0 * (1 - q ^ N) / (1 - q) := by
  have hdec : ∀ t, slack t ≤ q ^ t * slack 0 := fun t =>
    Hagi.Probability.compounding_bound q hq0 slack hslack t
  induction N with
  | zero => simp
  | succ n ih =>
    have hqn : 0 ≤ q ^ n := pow_nonneg hq0 n
    have h1 : (0:ℝ) < 1 - q := by linarith
    have h2 := hdec n
    have h3 : (1 - q) * slack n ≤ (1 - q) * (q ^ n * slack 0) :=
      mul_le_mul_of_nonneg_left h2 h1.le
    have h5 : (0:ℝ) ≤ q ^ n * slack 0 := mul_nonneg hqn hs0
    rw [Finset.sum_range_succ]
    calc ∑ t ∈ Finset.range n, slack t + slack n
        ≤ slack 0 * (1 - q ^ n) / (1 - q) + slack n :=
            add_le_add ih (le_refl _)
      _ ≤ slack 0 * (1 - q ^ (n + 1)) / (1 - q) := by
          have h4 : q ^ (n + 1) = q ^ n * q := pow_succ q n
          rw [h4]
          field_simp
          nlinarith [hqn, h5, h3]

/-- **`alternating_round_slack_summable`** — (B4 N1, C294,
ROUND-ERROR SUMMABILITY) the composed round-guard slack with
geometric decay (premise-form `slack (t+1) ≤ (Δ/m)·slack t`; the
delivery for the C·η_t part is `alternating_zphase_one_step_error`)
has ALL partial sums bounded by the geometric-series budget
`slack 0 * m/(m−Δ)`. Premise-form: the decay is a HYPOTHESIS; the
chain from latent-error contraction to slack decay is documented,
not claimed here. -/
theorem alternating_round_slack_summable {Δ : ℕ} {m : ℝ}
    (hm : 0 < m) (hΔm : (Δ : ℝ) < m)
    (slack : ℕ → ℝ) (hs0 : 0 ≤ slack 0)
    (hslack : ∀ t, slack (t + 1) ≤ ((Δ : ℝ) / m) * slack t)
    (N : ℕ) :
    ∑ t ∈ Finset.range N, slack t ≤ slack 0 * m / (m - Δ) := by
  set q : ℝ := (Δ : ℝ) / m with hq
  have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg (Nat.cast_nonneg _) hm.le
  have hq1 : q < 1 := by
    rw [hq]
    exact (div_lt_one hm).2 hΔm
  have hbound := slack_partial_sum hq0 hq1 slack hs0 hslack N
  have hqN : 0 ≤ q ^ N := pow_nonneg hq0 N
  have hp : (0:ℝ) < 1 - q := by linarith
  have hinner : slack 0 * (1 - q ^ N) ≤ slack 0 * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hs0
  have hle1 : slack 0 * (1 - q ^ N) / (1 - q)
      ≤ slack 0 * 1 / (1 - q) :=
    (div_le_div_iff₀ hp hp).2 (mul_le_mul_of_nonneg_right hinner hp.le)
  have hfinal : slack 0 * 1 / (1 - q) = slack 0 * m / (m - Δ) := by
    rw [hq]
    field_simp
  linarith [hbound, hle1, hfinal.ge]

end SlackSummable

/-! ## N2: trajectory telescoping and the descent budget -/
section Trajectory

variable {γ : Type*}

/-- **`alternating_trajectory_bound`** — (B4 N2, C294, TRAJECTORY
TELESCOPING) a trajectory of rounds `y 0, y 1, …` each satisfying
the strict-drop premise with per-round drop `d t` (premise-form)
telescopes: the final visible energy is at most the initial minus
the total drop. -/
theorem alternating_trajectory_bound {E : γ → ℝ} (y : ℕ → γ)
    (d : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ t < N, E (y (t + 1)) ≤ E (y t) - d t) :
    E (y N) ≤ E (y 0) - ∑ t ∈ Finset.range N, d t := by
  have hkey : ∀ (n : ℕ), (∀ t < n, E (y (t + 1)) ≤ E (y t) - d t) →
      E (y n) ≤ E (y 0) - ∑ t ∈ Finset.range n, d t := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : ∀ t < k, E (y (t + 1)) ≤ E (y t) - d t :=
        fun t ht => hk t (by omega)
      have hstep' := hk k (by omega)
      have hrec := ih hk'
      rw [Finset.sum_range_succ]
      have : E (y 0) - (∑ t ∈ Finset.range k, d t + d k)
          = E (y 0) - ∑ t ∈ Finset.range k, d t - d k := by ring
      rw [this]
      linarith
  exact hkey N hstep

/-- **`alternating_trajectory_descent_budget`** — (B4 N2, C294,
floor corollary) with the visible energy BOUNDED BELOW by `Emin`
(the honest floor premise — nonneg or bounded-below by
construction; a HYPOTHESIS, not a conclusion), the total descent
of a strictly-dropping trajectory is bounded: Σ drops ≤
`E (y 0) − Emin`. Combined with `alternating_round_slack_
summable`: a per-round drop `d t = c − slack t` with geometric
slack gives the cumulative descent budget `c·N − slack 0·m/(m−Δ)
≤ E (y 0) − Emin`, bounding the achievable number of guarded
rounds (remark, not a theorem — packaging the per-round premises
as a chain is the recorded next statement). -/
theorem alternating_trajectory_descent_budget {E : γ → ℝ} (y : ℕ → γ)
    (d : ℕ → ℝ) (N : ℕ) (Emin : ℝ)
    (hfloor : ∀ t, Emin ≤ E (y t))
    (hstep : ∀ t < N, E (y (t + 1)) ≤ E (y t) - d t) :
    ∑ t ∈ Finset.range N, d t ≤ E (y 0) - Emin := by
  have hb := alternating_trajectory_bound (E := E) y d N hstep
  have hf := hfloor N
  linarith

end Trajectory

/-! ## N3: terminal statement, finite form -/
section TerminalFinite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- **`alternating_rounds_converge`** — (B4 N3, C294, TERMINAL
FINITE FORM) on a finite configuration space, a trajectory of
alternating rounds along which the visible energy at the TRUE
frozen-z* kernel `pairwiseEnergy B (attentionK κ w f)` strictly
decreases at every pair has length at most the number of DISTINCT
energy values — the C268 ranking bound reused
(`greedy_strict_search_terminates` cited, not restated). Hence an
infinite strictly-improving alternating run CANNOT exist: the
process reaches a round where the composed guard fails (a STALL —
the honest terminal outcome; NOT a global-minimum claim).
Relation to the pinned negative: the UNCONDITIONAL analytic
convergence statement alternating_round_converges does NOT
exist and stays OPEN; this finite/strict version claims
TERMINATION only. -/
theorem alternating_rounds_converge (B : ι → α → ℝ) (κ : ι → ι → ℝ)
    (w : ι → ι → ℝ) (f : α → α → ℝ) (l : List (ι → α))
    (h : l.Pairwise (fun a b =>
      pairwiseEnergy B (attentionK κ w f) b
        < pairwiseEnergy B (attentionK κ w f) a)) :
    l.length ≤ Fintype.card (Set.image
      (pairwiseEnergy B (attentionK κ w f))
      (Set.univ : Set (ι → α))) :=
  greedy_strict_search_terminates _ l h

end TerminalFinite

/-! ## Numeric anchors (C294) -/
section Anchors

/-- ANCHOR (geometric slack sum numeric check): slack t = (1/2)^t
(q = Δ/m = 1/2, Δ = 1, m = 2): the budget is slack 0 * m/(m−Δ) = 2,
and the partial sum Σ_{t<5} (1/2)^t = 31/16 ≤ 2 through the
theorem itself. -/
example : ∑ t ∈ Finset.range 5, (1 / 2 : ℝ) ^ t ≤ 2 := by
  have h := alternating_round_slack_summable (Δ := 1) (m := 2)
    (by norm_num) (by norm_num) (fun t => (1 / 2 : ℝ) ^ t) (by norm_num)
    (fun t => by simp [pow_succ, mul_comm]) 5
  simp at h
  linarith

/-- ANCHOR (trajectory telescoping numeric check): E = 10 − t,
d = 1, N = 3: final 7 ≤ 10 − 3 through the theorem itself. -/
example : (fun t => (10 : ℝ) - t) 3
    ≤ (fun t => (10 : ℝ) - t) 0 - ∑ _t ∈ Finset.range 3, (1 : ℝ) := by
  have h := alternating_trajectory_bound (E := fun t => (10 : ℝ) - t)
    (fun t => t) (fun _ => 1) 3
    (by intro _t _; simp only [Nat.cast_succ]; linarith)
  show (10:ℝ) - 3 ≤ 10 - 0 - ∑ _t ∈ Finset.range 3, (1:ℝ)
  exact_mod_cast h

end Anchors

/-! ## Fixtures and witnesses -/
section Fixture

/-- **`fan2`** — agreement value-coupling on `Bool`
(`f a b = −1` iff `a = b`). -/
noncomputable def fan2 : Bool → Bool → ℝ := fun a b => if a = b then -1 else 0

/-- **`yan2`** — disagreeing fixture on `Fin 2` (cell 0 ≠ cell 1). -/
noncomputable def yan2 : Fin 2 → Bool := ![true, false]

/-- Numeric anchor (Fin 2 / Bool, APPLIED through the round theorem):
with constant weights (`w1 = w2`, so the latent slack `Lsm·η = 0`),
exact fields (ε = 0) and the agreement kernel, moving cell 0 of
`![true, false]` to `false` AGREES with cell 1 and STRICTLY drops
the energy `0 → −2` — the round theorem fires on a concrete
instance, not just a norm_num identity. -/
example : pairwiseEnergy (fun _ _ => (0:ℝ))
    (attentionK (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2)
    (Function.update yan2 0 false)
    < pairwiseEnergy (fun _ _ => (0:ℝ))
    (attentionK (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2) yan2 := by
  refine alternating_round_nonincreasing (κmax := 1) (fmax := 1)
    (Lsm := 0) (η := 0) (ε := 0)
    (fun _ _ => (0:ℝ))
    (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2
    (fun i j => ⟨by norm_num, le_refl _⟩)
    (fun a b => by unfold fan2; split <;> simp) (by norm_num)
    (fun i j => by simp) yan2 0 false
    (fun _ b => localField (fun _ _ => (0:ℝ))
      (attentionK (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) fan2) yan2 0 b)
    (fun b => by
      unfold localField attentionK attentionCoupling fan2 yan2
      simp)
    (by
      unfold localField attentionK attentionCoupling fan2 yan2
      simp)

end Fixture

end Hagi.Model.EnergyReasoning
