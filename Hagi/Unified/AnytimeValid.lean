/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.GrowthState
import Hagi.Core.Concat
import Hagi.Dynamics.Contraction
set_option linter.style.header false

/-!
# R63: the merge stage linked + anytime-validity skeleton

Continuing the round-62 program (unity at the Lean level):

* `merge_stage_linked`: the merge stage's hypothesis is no
  longer a free inequality — E(merged) ≤ mean(E(experts)) is
  the token-level CE law `ensemble_ce_le_mean_general` of
  `Hagi.Core.Concat` (the merged CE at the 1/N head is at
  most the experts' mean CE), aggregated over tokens with
  nonnegative weights. Only the token-aggregation (dataset
  measure) is h_emp_.
* `anytime_valid_budget`: the e-process skeleton for the
  controller — if every controller decision uses a test with
  a SUPERMARTINGALE-type budget (the per-decision false-alarm
  mass decays geometrically by an h_emp_ factor), the total
  false-alarm mass across ANY number of sequential decisions
  is bounded by the geometric sum: anytime validity by the
  union-of-geometric bound. The Ville-martingale form for
  BOUNDED stopping times and finite horizons is now proven in
  `Hagi.Unified.AnytimeMartingale` (R93:
  `eprocess_stopped_budget`, `ville_supermartingale`,
  `ville_anytime_false_alarm`); the unbounded-horizon form
  (sup over all t ∈ ℕ) remains open.
-/

open Finset Real

namespace Hagi

/-! ## The merge stage linked to the Concat law -/

/-- **The merge stage linked (round-62 item 1)**: the merged
model's energy — the token-weighted CE with the merged
logits — is bounded by the experts' mean energy. The token
law is `ensemble_ce_le_mean_general` (PROVEN); the
aggregation weights w (the dataset measure) are the only
empirical input (h_emp_w: nonnegative, sum 1). The merge
stage of MacroCycle now rests on the Concat interpolation
law instead of a free inequality. -/
theorem merge_stage_linked {k : Type} [Fintype k] [Nonempty k] {N : ℕ} [NeZero N]
    (z : Fin N → k → ℝ) (w : k → ℝ)
    (hw : ∀ t, 0 ≤ w t) (_hwsum : ∑ t, w t = 1) :
    ∑ t, w t * ceOneHot t (fun v => (∑ a, z a v) / N)
      ≤ ∑ t, w t * ((∑ a, ceOneHot t (z a)) / N) := by
  refine Finset.sum_le_sum (fun t _ => ?_)
  exact mul_le_mul_of_nonneg_left (ensemble_ce_le_mean_general t z) (hw t)

/-- **The strict-decrease merge case**: if the experts
disagree at a token with positive measure (the per-token gap
G_t > 0 on a set of tokens of positive weight), the linked
bound is strict there; the aggregate gap Σ w_t·G_t ≥ 0 with
equality only at consensus a.e. The nonneg direction (the
aggregate never increases the certificate) is the usable
theorem; strictness needs the token-level gap lower bound —
honest boundary. -/
theorem merge_stage_linked_nonneg {k : Type} [Fintype k] [Nonempty k] {N : ℕ} [NeZero N]
    (z : Fin N → k → ℝ) (w : k → ℝ)
    (hw : ∀ t, 0 ≤ w t) (hwsum : ∑ t, w t = 1) :
    0 ≤ ∑ t, w t * ((∑ a, ceOneHot t (z a)) / N)
        - ∑ t, w t * ceOneHot t (fun v => (∑ a, z a v) / N) := by
  have h := merge_stage_linked z w hw hwsum
  linarith

/-! ## Anytime validity: the union-of-geometric skeleton -/

/-- **The controller's false-alarm budget (anytime-valid
skeleton, round-62 'most underrated item')**: if the
controller makes sequential decisions, the n-th decision's
monitor passing with confidence 1−δₙ (false-alarm mass δₙ),
and the per-decision masses decay geometrically
δₙ = δ₀·ρⁿ with ρ < 1 (an h_emp_ schedule — e.g. fixed
sample-size growth), then the TOTAL false-alarm mass over
ANY horizon T is at most δ₀/(1−ρ) — uniformly in T
(anytime validity). Every controller verdict in the growth
loop (admit, skip, stop) inherits this bound; no multiple-
testing correction is needed beyond the geometric schedule.

**Honest boundary**: the full e-process/Ville form
(E[L_τ] ≤ 1 for arbitrary stopping times) is open; this is
the union bound under the geometric schedule. -/
theorem anytime_valid_budget (delta0 rho : ℝ) (T : ℕ)
    (hdelta0 : 0 ≤ delta0) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (delta : ℕ → ℝ) (hdecay : ∀ n, delta n = delta0 * rho ^ n) :
    ∑ n ∈ Finset.range T, delta n ≤ delta0 / (1 - rho) := by
  have hgeom := geom_sum_le_inv rho hrho hrho1 T
  have hgeom := Hagi.geom_sum_le_inv rho hrho hrho1 T
  rw [Finset.sum_congr rfl (fun n _ => hdecay n)]
  calc ∑ n ∈ Finset.range T, delta0 * rho ^ n
      = delta0 * ∑ n ∈ Finset.range T, rho ^ n := by
        rw [← Finset.mul_sum]
    _ ≤ delta0 * (1 / (1 - rho)) := mul_le_mul_of_nonneg_left hgeom hdelta0
    _ = delta0 / (1 - rho) := by field_simp

end Hagi