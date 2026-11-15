/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.EnergyReasoning.AttentionCoupling

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
  WITHOUT restarting (the summability input of the R1 design). The
  summable-series statement itself is NOT proven here.

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
