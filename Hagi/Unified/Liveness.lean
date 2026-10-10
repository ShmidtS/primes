/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Ensemble.GapLaw
import Hagi.Step.JointPreserve
set_option linter.style.header false

/-!
# Liveness — existence of a useful action

* `liveness_merge`: non-consensus implies `0 < twoGap p d`
  (contrapositive of `twoGap_zero_iff`).
* `liveness_data_axis`: with injection dominance
  `xi < inj` and `D (t+1) ≥ rho * D t + inj − xi`, one has
  `0 < D T` for every `T ≠ 0`.
* `liveness_two_axis`: both conclusions together; freezing
  requires consensus and `inj ≤ xi`.
-/

open Real Finset

namespace Hagi.Unified

/-- If the deviations `d` are not all equal to a common
constant (non-consensus), then `0 < twoGap p d`, by the
contrapositive of `twoGap_zero_iff`. -/
theorem liveness_merge {k : Type} [Fintype k] [Nonempty k]
    (p d : k → ℝ) (hp : ∀ u, 0 < p u) (hsum : ∑ u, p u = 1)
    (hdis : ¬ ∃ c : ℝ, ∀ u, d u = c) :
    0 < twoGap p d := by
  by_contra h
  push Not at h
  have hz : twoGap p d = 0 := le_antisymm h (twoGap_nonneg hp hsum)
  obtain ⟨c, hc⟩ := (twoGap_zero_iff hp hsum).mp hz
  exact hdis ⟨c, hc⟩

/-- If `0 < rho`, `0 ≤ inj`, `0 ≤ xi`, `xi < inj`, `0 ≤ D 0`,
and `D (t+1) ≥ rho * D t + inj − xi` for all `t`, then
`0 < D T` for every `T ≠ 0`. -/
theorem liveness_data_axis (D : ℕ → ℝ) (rho inj xi : ℝ)
    (hrho : 0 < rho) (hinj : 0 ≤ inj) (hxi : 0 ≤ xi)
    (hinjgt : xi < inj) (hD0 : 0 ≤ D 0)
    (hstep : ∀ t, D (t+1) ≥ rho * D t + inj - xi) (T : ℕ) (hT : T ≠ 0) :
    0 < D T := by
  have hf := diversity_floor_fresh D rho inj xi hrho hinj hxi hinjgt hD0 hstep T
  have hfloorpos := diversity_floor_strict_pos D rho inj xi hrho.le hinj hxi hinjgt
    hstep T hT
  linarith

/-- Combines `liveness_merge` and `liveness_data_axis`: under
non-consensus and injection dominance, both `0 < twoGap p d`
and `0 < D T` (for `T ≠ 0`). -/
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

end Hagi.Unified

namespace Hagi
export Hagi.Unified (liveness_merge liveness_data_axis liveness_two_axis)
end Hagi
