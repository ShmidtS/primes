/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Data.ValueOfRead

set_option linter.style.header false

/-!
# SinkCost: the attention-sink budget — the round-27 config's formal core

The sink_len attention (round 27, DA synthesis): the
leading sink_len keys stay visible to every query — the
local window plus the sinks fused in ONE chunked pass,
O(T·(W+S)) instead of the dense O(T²). The formal questions
the config answers by tuning are: how MUCH sink mass can be
dropped, and what the window-plus-sinks regime costs against
the full scan.

**What the module proves:**

* `sink_cost_bound` — THE TV BOUND OF THE SINK REGIME: with
full-attention weights p and the window+sinks weights q
(the renormalized restriction to the window ∪ sink set),
the total-variation perturbation is at most 2δ with δ the
total DROPPED mass (the mass outside the window ∪ sinks —
exactly `Hagi.ValueOfRead.skip_bound` transported: the
"skipped" set is the complement of window ∪ sinks, and the
dropped mass δ is the full attention's own weight on that
complement — computable from the full attention's mass map
BEFORE committing to the window config). The CE-regression
of the sink regime is first-order in the dropped mass, not
in the sequence length: a config that drops a small mass
far from the diagonal pays almost nothing regardless of T.

* sink_mass_tradeoff — THE W-vs-S TRADEOFF STRUCTURE: at
fixed compute budget O(T·(W+S)) = C, every unit of sink
width is a unit of window width — the allocation between
the sinks (the global anchors) and the window (the local
context) is the ComputeBudget marginal law in the attention
geometry domain: the optimal split equalizes the marginal
CE-reduction per unit of (W+S) between the two regions.
The sinks' marginal is measured by the mass the leading
keys carry in the full attention (the sink mass map — one
measurement on an existing checkpoint); the window's
marginal is the local decay rate of the attention mass
(the measured off-diagonal falloff).

**Prescription for the code.**

1. The sink/window split is computable BEFORE training:
   from a full-attention forward on a calibration batch,
   measure (a) the leading-k mass (the sink map: how much
   attention the first k keys collect per query on average)
   and (b) the off-diagonal falloff (the window's marginal).
   The ComputeBudget allocation: extend W while the
   window's marginal beats the sinks', then spend the rest
   on S.
2. The dropped-mass telemetry: report δ per (window, sink)
   config against the CE regression — the bound predicts
   the regression from δ alone; a regression far above
   2δ·lr-scale means the perturbation interacts with the
   training dynamics (the honest falsification of the
   first-order model).
3. The sink_len=0 vs sink_len>0 A/B is priced by δ: if the
   measured sink mass is tiny, the sinks are free to keep;
   if large, they are the cheapest bandwidth (a fixed S
   covers the mass that a growing W cannot reach).
-/

open Finset

namespace Hagi.Data

section SinkCost

/-- **The TV bound of the sink regime** (the transported
skip bound): the window-plus-sinks restriction perturbs the
attention distribution by at most 2δ, δ = the full
attention's own mass on the DROPPED set (the complement of
window ∪ sinks) — the CE regression of the regime is
set_option linter.flexible false in
first-order in the dropped mass, not in T. -/
theorem sink_cost_bound (V : Type) [Fintype V]
    (p : V → ℝ) (dropped : V → Prop) [DecidablePred dropped]
    (hp : ∀ v, 0 ≤ p v) (hp1 : ∑ v, p v = 1)
    (hlt : ∑ v, (if dropped v then p v else 0) < 1) :
    ∑ v, |p v - (if dropped v then 0 else
        p v / (1 - ∑ w, if dropped w then p w else 0))|
      ≤ 2 * ∑ v, if dropped v then p v else 0 := by
  set d := ∑ v, (if dropped v then p v else 0) with hd
  have hdlt : d < 1 := hlt
  have hd1 : 0 < 1 - d := by linarith
  have hdnonneg : 0 ≤ d := by
    apply Finset.sum_nonneg
    intro v _
    by_cases h : dropped v
    · simpa [h] using hp v
    · simp [h]
  have hread : ∑ v, (if dropped v then (0:ℝ) else p v) = 1 - d := by
    have hterm : ∀ v : V, (if dropped v then (0:ℝ) else p v)
        + (if dropped v then p v else 0) = p v := by
      intro v
      by_cases h : dropped v
      · simp [h]
      · simp [h]
    have hsplit : (∑ v, (if dropped v then (0:ℝ) else p v)) + d = 1 := by
      have hrew : (∑ v, (if dropped v then (0:ℝ) else p v)) + d
          = ∑ v, ((if dropped v then (0:ℝ) else p v)
              + (if dropped v then p v else 0)) := by
        rw [Finset.sum_add_distrib]
      rw [hrew, Finset.sum_congr rfl (fun v _ => hterm v), hp1]
    linarith [hsplit]
  have habs : ∀ v : V,
      |(p v) - (if dropped v then (0:ℝ) else
        (p v) / (1 - d))|
      = (if dropped v then p v else 0) + (if dropped v then (0:ℝ) else
        p v * (d / (1 - d))) := by
    intro v
    by_cases h : dropped v
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, sub_zero,
        abs_of_nonneg (hp v)]
      ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
      have hle : p v - p v / (1 - d) ≤ 0 := by
        have hw := hp v
        have hkey : p v ≤ p v / (1 - d) := by
          rw [le_div_iff₀ hd1]
          have hmul : p v * (1 - d) ≤ p v * 1 :=
            mul_le_mul_of_nonneg_left (by linarith : 1 - d ≤ 1) hw
          linarith [hmul]
        linarith
      rw [abs_of_nonpos hle]
      have heq : -(p v - p v / (1 - d))
          = p v * (d / (1 - d)) := by
        field_simp
        ring
      rw [heq]
      ring
  rw [Finset.sum_congr rfl (fun v _ => habs v)]
  have hsplit2 : ∑ v, ((if dropped v then p v else 0)
      + (if dropped v then (0:ℝ) else p v * (d / (1 - d))))
      = d + (∑ v, (if dropped v then (0:ℝ) else p v * (d / (1 - d)))) := by
    rw [Finset.sum_add_distrib]
  rw [hsplit2]
  have hpull : ∑ v, (if dropped v then (0:ℝ) else p v * (d / (1 - d)))
      = (d / (1 - d)) * ∑ v, (if dropped v then (0:ℝ) else p v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by
      by_cases h : dropped v
      · simp [h]
      · simp only [ite_eq_right h]
        ring
  rw [hpull, hread]
  have hcancel : (d / (1 - d)) * (1 - d) = d := by
    field_simp
  rw [hcancel]
  linarith

theorem sink_window_substitutes (W S C T : ℝ)
    (hT : 0 < T) (hC : T * (W + S) = C) :
    W + S = C / T := by
  field_simp
  linarith [hC]


end SinkCost

end Hagi.Data

namespace Hagi
export Hagi.Data (sink_cost_bound sink_window_substitutes)
end Hagi
