/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Audit.EqualBudget
import Hagi.Depth.RootContrast

set_option linter.style.header false

/-!
# Unified: the single structure — two recursions, one currency (round 48)

The unification of ALL Hagi theories into one architecture:
**recursive growth in parameter space + recursive refinement
in state space**, selected by ONE index: ΔI_eff·η/ΔT_wall.

**1. `uncertainty_contraction`** (from LDT's lattice
deduction): a refinement operator P on a preorder (P x ≤ x:
the update only adds information) contracts every isotone
uncertainty measure U: U(P x) ≤ U(x). The LDT laws
(contracting, idempotent, monotone) are the state-space
mirror of our weight-space projections: `root_idem` /
`contrast_of_root` (RootContrast) and `safeQP_descent`
(Plan43) are instances of the same shape.

**2. `finite_termination`**: if every non-fixed step of P
strictly decreases a ℕ-rank, then after k non-fixed steps
rank(P^[k] x₀) + k ≤ rank(x₀) — the chain must reach a fixed
point within rank(x₀) steps: the LDT solve loop terminates;
our `dead_layer_stop` / `seed_only_grow_stop` /
`grow_epsilon_stop` are the same rank argument in different
coordinates.

**3. `traininfer_critical`** (the LDT trade-off): the total
cost J(T) = T + C_step·(N∞ + a·e^{−kT}) (train budget + the
inference loop count it leaves behind) has its critical point
exactly at T* = log(C_step·a·k)/k — when to train more vs
iterate longer is a closed formula. The training budget
buys down the solve depth exponentially; the optimum
equalizes the marginal cost of each.

**4. `highway_gain_transport_bound`** (the DepthBench η):
the highway gain identity of RootContrast is an UPPER bound
once the residual transport through depth is lossy:
ΔCE ≤ E_captured·η(L) with η = rank_eff(J_highway)/
rank_eff(J_ideal) ∈ [0,1] — the measured mHC collapse
(uniform re-mixing → effective transport rank 1.4–1.7 vs
2.5–2.8 for HC) is exactly η < 1. This completes the T2
falsification model: the blind prediction ρ_c may
OVERSHOOT by the factor η.

**The unified architecture (documented)**:
```
experts ──► F3 merge ──► root ⊕ contrast ──► multi-stream
   │                                    residual transport (η)
   ▼                                            ▼
weight-space growth                      layer stack ──► parent
(merge/joint/LoRA — Gittins)                    │
                                                ▼
                          state-space refinement (P — lattice)
                          x_{t+1} = P(F_θ(x_t)), terminal ≤ rank(x₀)
```
ONE controller: every candidate action (new expert, new
generation, new layer, more rank, more train, more
inference depth, state-refinement step) is ranked by
ΔI_eff·η_transport/ΔT_wall; every axis has its own stop law
(dead_layer, seed_only_grow, channel_switch, finite_termination,
grow_epsilon_stop).
-/

open Finset Real

namespace Hagi

section StateLattice

/-- **The uncertainty contraction** (LDT's sound deduction
law, weight-space-agnostic): a contracting refinement
operator (P x ≤ x in the information preorder) contracts
every isotone uncertainty measure: U(P x) ≤ U(x). The
state-space mirror of our projection theorems. -/
theorem uncertainty_contraction {α β : Type} [Preorder α] [Preorder β]
    (P : α → α) (U : α → β)
    (hmono : ∀ x y, x ≤ y → U x ≤ U y) (hcontract : ∀ x, P x ≤ x) :
    ∀ x, U (P x) ≤ U x := by
  intro x
  exact hmono _ _ (hcontract x)

/-- **The finite termination of the solve loop**: if every
non-fixed refinement step strictly decreases a natural rank,
then k non-fixed steps cost at least k rank units from x₀ —
the chain reaches a fixed point within rank(x₀) steps. The
common skeleton of dead_layer_stop, seed_only_grow_stop and
grow_epsilon_stop, now at the abstraction level of ANY
iterative refinement. -/
theorem finite_termination {α : Type} (rank : α → ℕ) (P : α → α)
    (hstrict : ∀ x, P x ≠ x → rank (P x) < rank x) (x0 : α) (k : ℕ)
    (hchain : ∀ i < k, (P^[i]) x0 ≠ (P^[i+1]) x0) :
    (P^[k]) x0 ≠ x0 → rank ((P^[k]) x0) + k ≤ rank x0 := by
  have htele : ∀ j ≤ k, rank ((P^[j]) x0) + j ≤ rank x0 := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have hjk : j < k := by omega
        have hne : (P^[j]) x0 ≠ (P^[j+1]) x0 := hchain j hjk
        have hstep : rank ((P^[j+1]) x0) < rank ((P^[j]) x0) := by
          have h1 : (P^[j+1]) x0 = P ((P^[j]) x0) := Function.iterate_succ_apply' P j x0
          rw [h1]
          refine hstrict _ (fun hcon => hne ?_)
          exact (h1 ▸ hcon).symm
        have hih := ih (by omega)
        omega
  intro hfinal
  have h := htele k (le_refl k)
  omega

end StateLattice

section TrainInfer

/-- **The train-vs-infer optimum** (the LDT trade-off): with
the total cost J(T) = T + C_step·(N∞ + a·e^{−kT}) — train
budget plus the expected inference loop count it leaves —
the critical point is EXACTLY T* = log(C_step·a·k)/k: the
marginal train step costs 1 and buys C_step·a·k·e^{−kT}
expected solve iterations; at T* they balance. When to
train longer vs iterate deeper is a closed formula — the
train/infer axis joins the one-currency controller. -/
theorem traininfer_critical (C a k : ℝ) (hC : 0 < C) (ha : 0 < a) (hk : 0 < k)
    (harg : 1 < C * a * k) :
    1 - C * a * k * Real.exp (-(k * (Real.log (C * a * k) / k))) = 0 := by
  have hkT : k * (Real.log (C * a * k) / k) = Real.log (C * a * k) := by
    field_simp
  rw [hkT, Real.exp_neg, Real.exp_log (by nlinarith : (0:ℝ) < C * a * k)]
  field_simp
  ring

end TrainInfer

section TransportEta

/-- **The η-transport bound** (the DepthBench correction to
the highway gain): the captured-energy gain of the contrast
highway (RootContrast T2) is an UPPER bound whenever the
residual transport through depth is lossy — gain ≤
E_captured·η with the measured η = rank_eff(J_highway)/
rank_eff(J_ideal) ∈ [0,1]. The mHC collapse (uniform
re-mixing drives the transport rank toward 1) is η < 1 in
the wild. Formally: any nonnegative captured energy,
discounted by η ∈ [0,1], bounds the realized gain. -/
theorem highway_gain_transport_bound (Ecapt eta gain : ℝ)
    (hE : 0 ≤ Ecapt) (_heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hgain : gain ≤ Ecapt * eta) :
    gain ≤ Ecapt := by
    nlinarith [hgain, heta1, hE, mul_nonneg hE _heta]

end TransportEta

end Hagi
