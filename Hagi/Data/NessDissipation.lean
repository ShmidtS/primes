/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Data.DField

set_option linter.style.header false

/-!
# NessDissipation: detailed balance and the entropy-production gap (R174c)

The third module of the thermodynamic layer (§8.8 of
FORMALIZATION_PLAN.md, round R174c). The plan's γ-deficit
reframe: "the unreachable equilibrium as the measure of
unfinished gain" (arXiv:2607.17146: the breakdown of detailed
balance marks a NESS — a nonequilibrium steady state; the
γ-deficit of the growth loop is its dissipation). This module
formalizes the mathematical core of that reframe on a finite
Markov chain:

* the edge flow `flowMap P π i j = π i · P i j` (the
  stationary traffic across the directed edge i → j);

* the ENTROPY PRODUCTION RATE as the KL divergence between
  the forward and reversed edge flows
  `epRate P π = KLdiv (flow P π) (flowBack P π)` — the finite
  Markov-chain form of Σ π_i P_ij log(π_i P_ij / π_j P_ji);

* `detailed_balance_zero_ep` — EQUILIBRIUM IS DISSIPATION-FREE:
  under detailed balance (π_i P_ij = π_j P_ji on every edge)
  the entropy production rate is EXACTLY zero — the loop has
  no unfinished gain; every step of the stationary traffic is
  reversible;

* `ep_zero_implies_db` — THE CONVERSE (NESS characterization,
  finite form): a zero entropy production rate forces
  detailed balance on every edge with positive flow — zero
  dissipation exists ONLY at equilibrium.

Together: detailed balance ⟺ zero entropy production — the
NESS/dissipation dictionary of the γ-deficit, in its exact
finite form. The plan's mapping "γ-deficit ~ dissipation" is
an interpretation; the theorems here carry no claim about
the training loop.
-/

namespace Hagi.Data

open Finset

variable {V : Type} [Fintype V] [Nonempty V]

/-- The stationary edge flow: traffic `π i · P i j` across
the directed edge `i → j` of a Markov transition kernel `P`
with stationary law `π`. -/
noncomputable def flowMap (P : V → V → ℝ) (pi : V → ℝ) (i j : V) : ℝ :=
  pi i * P i j

/-- The reversed edge flow: traffic of the time-reversed
chain across the same directed edge. -/
noncomputable def flowBack (P : V → V → ℝ) (pi : V → ℝ) (i j : V) : ℝ :=
  pi j * P j i

/-- The ENTROPY PRODUCTION RATE of the chain: the KL
divergence between the forward and reversed edge flows —
the finite form of Σ_{i,j} π_i P_ij·log(π_i P_ij / π_j P_ji).
Zero exactly at equilibrium (detailed balance); strictly
positive at any NESS. -/
noncomputable def epRate (P : V → V → ℝ) (pi : V → ℝ) : ℝ :=
  KLdiv (fun e : V × V => flowMap P pi e.1 e.2)
    (fun e : V × V => flowBack P pi e.1 e.2)

/-- **Equilibrium is dissipation-free**: under detailed
balance (`π i · P i j = π j · P j i` on every edge) the
entropy production rate is EXACTLY zero. -/
theorem detailed_balance_zero_ep (P : V → V → ℝ) (pi : V → ℝ)
    (hpos : ∀ i j, 0 < pi i * P i j)
    (hdb : ∀ i j, pi i * P i j = pi j * P j i) :
    epRate P pi = 0 := by
  unfold epRate
  have hzero : (fun e : V × V => flowMap P pi e.1 e.2)
      = (fun e : V × V => flowBack P pi e.1 e.2) := by
    funext e
    unfold flowMap flowBack
    exact hdb e.1 e.2
  rw [hzero]
  unfold KLdiv
  refine Finset.sum_eq_zero fun e _ => ?_
  have hF : 0 < flowMap P pi e.1 e.2 := hpos e.1 e.2
  have hB : 0 < flowBack P pi e.1 e.2 := by
    unfold flowBack
    rw [← hdb e.1 e.2]
    exact hpos e.1 e.2
  unfold flowBack at hB ⊢
  rw [div_self (ne_of_gt hB), Real.log_one, mul_zero]


/-- **Zero dissipation exists ONLY at equilibrium** (the NESS
characterization, finite form): if the entropy production
rate of the chain is zero (with everywhere-positive flows and
stochastic rows), then detailed balance holds on EVERY edge.
Combined with `detailed_balance_zero_ep`: detailed balance ⟺
zero entropy production — the dissipation/equilibrium
dictionary of the γ-deficit, exact on finite chains. -/
theorem ep_zero_implies_db (P : V → V → ℝ) (pi : V → ℝ)
    (hpos : ∀ i j, 0 < pi i * P i j)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hpisum : ∑ i, pi i = 1)
    (hz : epRate P pi = 0) :
    ∀ i j, pi i * P i j = pi j * P j i := by
  classical
  -- both edge flows are probability vectors on V × V
  have hsumF : ∑ e : V × V, flowMap P pi e.1 e.2 = 1 := by
    rw [Fintype.sum_prod_type]
    unfold flowMap
    have hstep : ∀ x : V, ∑ y : V, pi x * P x y = pi x := by
      intro x
      rw [← Finset.mul_sum, hrow x, mul_one]
    rw [Finset.sum_congr rfl (fun x _ => hstep x)]
    exact hpisum
  have hsumB : ∑ e : V × V, flowBack P pi e.1 e.2 = 1 := by
    rw [Fintype.sum_prod_type]
    unfold flowBack
    have hstep : ∀ y : V, ∑ x : V, pi y * P y x = pi y := by
      intro y
      rw [← Finset.mul_sum, hrow y, mul_one]
    rw [Finset.sum_comm (s := (Finset.univ : Finset V))
      (t := (Finset.univ : Finset V))]
    rw [Finset.sum_congr rfl (fun y _ => hstep y)]
    exact hpisum
  have hposF : ∀ e : V × V, 0 < flowMap P pi e.1 e.2 :=
    fun e => hpos e.1 e.2
  have hposB : ∀ e : V × V, 0 < flowBack P pi e.1 e.2 :=
    fun e => hpos e.2 e.1
  have hfl := kl_zero_iff_eq
    (fun e : V × V => flowMap P pi e.1 e.2)
    (fun e : V × V => flowBack P pi e.1 e.2)
    hposF hposB hsumF hsumB hz
  intro i j
  have := hfl (i, j)
  unfold flowMap flowBack at this
  exact this

end Hagi.Data
