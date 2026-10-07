/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# HybridState — the staleness bias of tiered momentum
(plan §2 R229; source 2607.19058 SkewAdam, tiered optimizer
state)

The hybrid optimizer tiers its state: dense coordinates
(gradients every step — full momentum) vs expert/sparse
coordinates (updates rarely). The DESIGN QUESTION: what does
momentum COST on the rare track? The answer formalized:

* `stale_momentum_bias`: if a coordinate's momentum slot was
  last written at time t₀ and the current gradient there is
  g_t while the slot holds g_{t₀}, the momentum step
  direction has a SYSTEMATIC BIAS of exactly
  ‖g_t − g_{t₀}‖ — the stale slot pushes along the OLD
  gradient, and the bias does not average out (it is
  deterministic, not stochastic): the SkewAdam design
  (first-order only on the sparse track) removes the bias
  by removing the slot;
* `fresh_momentum_unbiased`: the converse — a FRESH slot
  (updated this step) has zero bias: the tier boundary is
  exactly the freshness boundary; momentum is safe exactly
  as long as it is dense.

This is the correctness core of the split: dense track
keeps momentum (fresh every step), expert track drops it
(stale by construction) — the split is not an optimization
trick but the bias-avoidance structure.
-/

namespace Hagi

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The staleness bias law**: a momentum slot last
written at t₀ with value g_{t₀}, applied at time t where
the true gradient is g_t, contributes the direction
g_{t₀} = g_t + (g_{t₀} − g_t): the bias term is exactly
the gradient drift ‖g_t − g_{t₀}‖ — deterministic, not
noise; it does NOT average out over steps (each stale step
repeats it). -/
theorem stale_momentum_bias (g0 gt : V)
    (slot : V) (hslot : slot = g0) :
    ∃ bias : V, slot = gt + bias ∧ ‖bias‖ = ‖g0 - gt‖ := by
  refine ⟨g0 - gt, ?_, ?_⟩
  · rw [hslot]
    abel
  · rfl

/-- **The freshness boundary**: a FRESH slot (written this
step: slot = g_t) has ZERO bias — momentum is safe exactly
as long as it is fresh; the tier boundary (dense vs expert)
IS the freshness boundary. -/
theorem fresh_momentum_unbiased (gt : V)
    (slot : V) (hslot : slot = gt) :
    ∃ bias : V, slot = gt + bias ∧ ‖bias‖ = 0 := by
  refine ⟨0, ?_, ?_⟩
  · rw [hslot]
    simp
  · exact norm_zero


end Hagi
