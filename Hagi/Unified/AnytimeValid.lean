/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Core.Concat
import Hagi.Foundations.Recurrence
set_option linter.style.header false

/-!
# The merge stage and the anytime-validity budget

* `merge_stage_linked`: the token-weighted CE of the merged
  logits is bounded by the experts' mean CE (aggregation of
  `ensemble_ce_le_mean_general` over tokens with nonnegative
  weights `w` summing to 1).
* `anytime_valid_budget`: a false-alarm schedule decaying
  geometrically (`delta n = delta0 * rho ^ n`, `rho < 1`) has
  total mass at most `delta0 / (1 - rho)` over any horizon
  `T`. The e-process/Ville form is in
  `Hagi.Unified.AnytimeMartingale`; the unbounded-horizon form
  remains open.
-/

open Finset Real

namespace Hagi

/-! ## The merge stage linked to the Concat law -/

/-- For nonnegative weights `w` summing to 1, the token-weighted
CE of the averaged logits is at most the weighted mean of the
experts' per-token CEs (aggregation of
`ensemble_ce_le_mean_general`). -/
theorem merge_stage_linked {k : Type} [Fintype k] [Nonempty k] {N : ℕ} [NeZero N]
    (z : Fin N → k → ℝ) (w : k → ℝ)
    (hw : ∀ t, 0 ≤ w t) (_hwsum : ∑ t, w t = 1) :
    ∑ t, w t * ceOneHot t (fun v => (∑ a, z a v) / N)
      ≤ ∑ t, w t * ((∑ a, ceOneHot t (z a)) / N) := by
  refine Finset.sum_le_sum (fun t _ => ?_)
  exact mul_le_mul_of_nonneg_left (ensemble_ce_le_mean_general t z) (hw t)

/-- The aggregate merge gap is nonnegative:
`0 ≤ ∑ t, w t * (∑ a, ceOneHot t (z a)) / N - ∑ t, w t * ceOneHot t (fun v => (∑ a, z a v) / N)`.
Strictness needs a token-level gap lower bound and is not
claimed. -/
theorem merge_stage_linked_nonneg {k : Type} [Fintype k] [Nonempty k] {N : ℕ} [NeZero N]
    (z : Fin N → k → ℝ) (w : k → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hwsum : ∑ t, w t = 1) :
    0 ≤ ∑ t, w t * ((∑ a, ceOneHot t (z a)) / N)
        - ∑ t, w t * ceOneHot t (fun v => (∑ a, z a v) / N) := by
  have h := merge_stage_linked z w hw hwsum
  linarith

/-! ## Anytime validity: the union-of-geometric skeleton -/

/-- If `0 ≤ delta0`, `0 ≤ rho < 1`, and
`delta n = delta0 * rho ^ n`, then for every horizon `T`:
`∑ n < T, delta n ≤ delta0 / (1 - rho)`. -/
theorem anytime_valid_budget (delta0 rho : ℝ) (T : ℕ)
    (hdelta0 : 0 ≤ delta0) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (delta : ℕ → ℝ) (hdecay : ∀ n, delta n = delta0 * rho ^ n) :
    ∑ n ∈ Finset.range T, delta n ≤ delta0 / (1 - rho) := by
  have hgeom := Hagi.Foundations.geom_sum_le_inv rho T hrho hrho1
  rw [Finset.sum_congr rfl (fun n _ => hdecay n)]
  calc ∑ n ∈ Finset.range T, delta0 * rho ^ n
      = delta0 * ∑ n ∈ Finset.range T, rho ^ n := by
        rw [← Finset.mul_sum]
    _ ≤ delta0 * (1 / (1 - rho)) := mul_le_mul_of_nonneg_left hgeom hdelta0
    _ = delta0 / (1 - rho) := by field_simp

end Hagi