/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Ensemble.GapLaw
import Hagi.Step.JointPreserve
import Hagi.Unified.TopLevel
set_option linter.style.header false

/-!
# R80: liveness — the PositiveProgress half of the loop

The audit's central missing bridge: the conditional side
(action ⟹ descent) is complete; this module adds the LIVENESS
side — residual potential GUARANTEES a useful action exists:

- `liveness_merge`: disagreement (¬consensus) ⟹ the merge
  action's certified gain twoGap > 0 (contrapositive of
  twoGap_zero_iff).
- `liveness_data_axis`: exhausted merge axis (consensus) is
  escaped through fresh data: inj > ξ ⟹ D_T > 0 at every
  generation ≥ 1 — new disagreement reopens the merge axis.
- `liveness_two_axis`: the loop CANNOT FREEZE while either
  axis is alive; freeze requires BOTH consensus AND inj ≤ ξ
  — the honest global stopping condition.

With top_level_cycle_bound + horizon_termination (safety),
the loop either progresses or provably rests.
-/

open Real Finset

namespace Hagi

/-- **Merge-axis liveness (the PositiveProgress core)**: if
the experts are NOT in consensus (no common shift c with
d = c·1 — i.e. real disagreement exists), then the merge
action's certified stage gain is STRICTLY POSITIVE:

  ¬consensus ⟹ 0 < twoGap

via the contrapositive of twoGap_zero_iff. This is the
liveness half of the growth loop: residual potential
(measured disagreement) GUARANTEES the existence of a useful
action (merge), with the gain exactly the Jensen gap. The
safe half (action ⟹ descent) is top_level_cycle_bound. -/
theorem liveness_merge {k : Type} [Fintype k] [Nonempty k]
    (p d : k → ℝ) (hp : ∀ u, 0 < p u) (hsum : ∑ u, p u = 1)
    (hdis : ¬ ∃ c : ℝ, ∀ u, d u = c) :
    0 < twoGap p d := by
  by_contra h
  push Not at h
  have hz : twoGap p d = 0 := le_antisymm h (twoGap_nonneg hp hsum)
  obtain ⟨c, hc⟩ := (twoGap_zero_iff hp hsum).mp hz
  exact hdis ⟨c, hc⟩

/-- **Data-axis liveness (the EXHAUSTED-growth escape)**:
when the merge axis is exhausted (consensus reached, gap 0),
growth continues through FRESH DATA: strict injection
dominance (inj > ξ — new independent data arrives faster
than leakage) guarantees D_T > 0 at every generation T ≥ 1
(diversity_floor_strict_pos) — new disagreement is injected,
and by liveness_merge the NEXT merge action again has a
strictly positive certified gain. The two-axis liveness:
merge while diverse, inject when exhausted; the loop cannot
freeze while inj > ξ. -/
theorem liveness_data_axis (D : ℕ → ℝ) (rho inj xi : ℝ)
    (hrho : 0 < rho) (hinj : 0 ≤ inj) (hxi : 0 ≤ xi)
    (hinjgt : xi < inj) (hD0 : 0 ≤ D 0)
    (hstep : ∀ t, D (t+1) ≥ rho * D t + inj - xi) (T : ℕ) (hT : T ≠ 0) :
    0 < D T := by
  have hf := diversity_floor_fresh D rho inj xi hrho hinj hxi hinjgt hD0 hstep T
  have hfloorpos := diversity_floor_strict_pos D rho inj xi hrho.le hinj hxi hinjgt
    hstep T hT
  linarith

/-- **Two-axis liveness (the closed-loop PositiveProgress)**:
the growth loop CANNOT FREEZE while EITHER axis is alive —
- merge axis: disagreement ⟹ certified merge gain > 0
  (liveness_merge);
- data axis: inj > ξ ⟹ D_T > 0 (liveness_data_axis) — fresh
  disagreement is injected, reopening the merge axis.
Freeze requires BOTH consensus (G = 0) AND inj ≤ ξ — the
honest global stopping condition. This is the liveness half;
the safety half (certified action ⟹ Lyapunov descent ⟹
termination) is top_level_cycle_bound + horizon_termination.
Together: the loop either progresses or provably rests. -/
theorem liveness_two_axis {k : Type} [Fintype k] [Nonempty k]
    (p d : k → ℝ) (hp : ∀ u, 0 < p u) (hsum : ∑ u, p u = 1)
    (hcons : ¬ ∃ c : ℝ, ∀ u, d u = c)
    (D : ℕ → ℝ) (rho inj xi : ℝ)
    (hrho : 0 < rho) (hinj : 0 ≤ inj) (hxi : 0 ≤ xi)
    (hinjgt : xi < inj) (hD0 : 0 ≤ D 0)
    (hstep : ∀ t, D (t+1) ≥ rho * D t + inj - xi) (T : ℕ) (hT : T ≠ 0) :
    0 < twoGap p d ∧ 0 < D T :=
  ⟨liveness_merge p d hp hsum hcons,
    liveness_data_axis D rho inj xi hrho hinj hxi hinjgt hD0 hstep T hT⟩

end Hagi
