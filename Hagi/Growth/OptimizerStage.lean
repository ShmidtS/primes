/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.GainDecomposition

/-!
# OptimizerStage — the optimizer transformation as a separate
conversion stage (source arXiv:2610.02179v1)

The multi-teacher experiment: teacher gradients g₁ ≉ g₂ can
become nearly-identical UPDATES after the optimizer (cosine
> 0.83 with preserved Adam state, ≈ 0 after first-moment
reset; the current teacher-specific displacements themselves
are nearly orthogonal, cos < 0.01). The disagreement chain
must therefore pass through an OPTIMIZER bottleneck:

  E_dev --η_policy--> G_policy --η_opt--> G_update
      --η_state--> G_cap

* `etaOpt` — the optimizer conversion ratio: how much of the
  gradient-space disagreement survives the optimizer
  transformation (measured as update-space disagreement over
  gradient-space disagreement);
* `gain_chain_opt` — the three-stage composition law:
  G_cap = η_state·η_opt·η_policy·E_dev — the multiplicative
  chain, each factor separately measurable;
* `any_stage_kills_gain` — the necessity result extended:
  a nonpositive stage with nonnegative partners kills the
  total gain — the γ = 9× deficit question now has THREE
  separately diagnosable bottlenecks (policy/distill,
  optimizer, consolidation) plus the merge price.

Empirical anchors (flagged, NOT constants of nature —
Qwen3-1.7B-scale measurements): Adam first-moment ≈ aligns
teacher updates (η_opt ↓), momentum-free SGD preserved more
of the disagreement (higher scores DR 39.94 vs 38.91); the
β₁ = 0 / first-moment-reset regime on the consolidation
segment is the indicated experiment.
-/

namespace Hagi

/-- The optimizer conversion ratio: update-space
disagreement over gradient-space disagreement — how much
disagreement the optimizer TRANSPORTS rather than cancels. -/
noncomputable def etaOpt (D_grad D_update : ℝ) : ℝ :=
  D_update / D_grad

/-- **The three-stage chain**: if all three conversions hold
(policy → gradient-space gain → optimizer transport →
state consolidation), the total conversion is the PRODUCT of
three separately measurable factors. -/
theorem gain_chain_opt (E_dev G_policy G_update G_cap
    η_p η_o η_s : ℝ)
    (h1 : G_policy = η_p * E_dev)
    (h2 : G_update = η_o * G_policy)
    (h3 : G_cap = η_s * G_update) :
    G_cap = (η_p * η_o * η_s) * E_dev := by
  rw [h1] at h2
  rw [h2] at h3
  rw [h3]
  ring

/-- **Necessity of every stage (extended)**: a nonpositive
stage with nonnegative partners kills the total gain — the
chain has no bypass through ANY of the three stages; the
γ-deficit localizes to whichever η is small. -/
theorem any_stage_kills_gain (E_dev G_policy G_update G_cap
    η_p η_o η_s : ℝ)
    (hE : 0 ≤ E_dev)
    (h1 : G_policy = η_p * E_dev)
    (h2 : G_update = η_o * G_policy)
    (h3 : G_cap = η_s * G_update)
    (hzero : (η_p ≤ 0 ∧ 0 ≤ η_o ∧ 0 ≤ η_s)
      ∨ (0 ≤ η_p ∧ η_o ≤ 0 ∧ 0 ≤ η_s)
      ∨ (0 ≤ η_p ∧ 0 ≤ η_o ∧ η_s ≤ 0)) :
    G_cap ≤ 0 := by
  have hchain : G_cap = (η_p * η_o * η_s) * E_dev :=
    gain_chain_opt E_dev G_policy G_update G_cap η_p η_o η_s
      h1 h2 h3
  rcases hzero with ⟨hp, ho, hs⟩ | ⟨hp, ho, hs⟩ | ⟨hp, ho, hs⟩
  · have hprod : η_p * η_o * η_s ≤ 0 := by
      nlinarith [mul_nonneg ho hs]
    nlinarith [hchain, hE, hprod]
  · have hprod : η_p * η_o * η_s ≤ 0 := by
      nlinarith [mul_nonneg hp hs]
    nlinarith [hchain, hE, hprod]
  · have hprod : η_p * η_o * η_s ≤ 0 := by
      nlinarith [mul_nonneg hp ho]
    nlinarith [hchain, hE, hprod]

end Hagi
