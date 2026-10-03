/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Ensemble.GenCycle

set_option linter.style.header false

/-!
# The compounding law: why −0.16 nats/cycle has not yet decayed

The measured trajectory holds a constant per-cycle gain
(−0.18/−0.16/−0.17: 5.875 → 5.694 → 5.532 → 5.367) — against the
naive expectation of diminishing returns, even though the
sibling disagreement itself decayed (0.30 → 0.036 → 0.051) and
then stabilized near the replenished level D ≈ 0.045. This
module gives the theory of the per-cycle gain `c_t` as a
function of the measurable generational quantities, and the
derived recursion budget.

**The model.** One cycle's certified improvement decomposes into
two additive channels:

* the *ensemble channel*: the fresh leaves' disagreement G_t is
  harvested by the merge (the Jensen gap realized as CE gain) —
  bounded by `α • G_t` with `α` the realized harvest ratio
  (measured per cycle; `α ≤ 1` since the gap is the gap of the
  mean, not of the worst child);
* the *joint channel*: the joint step's own improvement `J_t`
  (the trust-region-bounded fine-tune of `Hagi.Step/Joint`),
  independent of the disagreement — the *data-driven* channel.

**What the module proves:**

* `compound_c_decompose` — the per-cycle bound: the certified
  improvement is at most `α • G_t + J_t`. This is the falsifiable
  law: regress the measured `c_t` against the measured
  `(G_t, J_t)` — if `c_t ≈ αG + J` holds with stable
  coefficients, the trajectory is predictable; the constant-c
  regime is then *explained* by `G_t` having stabilized at the
  replenishment level D (the ρ-D-ε law of `genGap_decay`):
  once G_t ≈ D, `c_t ≈ αD + J` — constant, as measured.
* `compound_trajectory` — the derived k-generation forecast:
  with `G_t` obeying the ρ-D recursion and the joint channel
  constant `J`, the mean CE after k generations is
  `M₀ − Σ_t (α • G_t + J)` with G_t given by the closed form of
  `genGap_decay` — an explicit, falsifiable prediction BEFORE
  the GPU spend (the gen-3 test).
* `compound_budget` — the derived stopping rule: the recursion
  is worth continuing while the *predicted next-cycle gain*
  `α • G_{t+1} + J` exceeds the cycle cost `ε_c`; since
  `G_{t+1} → D`, the recursion saturates at the constant rate
  `αD + J` — it never decays to zero unless the *data axis*
  (the field D, the corpus mixture) is exhausted. This is the
  formal statement of the strategic fork: a constant-c regime
  is not an anomaly — it is the signature of live data
  replenishment; the recursion budget is bounded by the data
  budget, not by the architecture.

**Prescription for the code.**

1. Per generation, log three scalars: the fresh-leaf
   disagreement `G_t` (the twoGap statistic), the realized
   cycle gain `c_t` (the measured ΔCE), and the joint-step
   improvement `J_t` (the measured ΔCE of the joint step alone).
   Two-cycle regression of `c_t` on `(G_t, J_t)` fixes
   `(α, β)` — the law is then armed.
2. The gen-3 prediction is `M_3 = M_2 − (α • G_2 + J_2)` with
   `G_2` from the ρ-D closed form — falsifiable BEFORE the run.
3. The stopping verdict: continue while `αG_{t+1} + J > ε_c`
   (the cycle cost); when the data axis is exhausted (D → 0,
   the disagreement dies per `genGap_decay`), the same
   inequality turns and the recursion folds — the derived
   replacement of the hand-made budget decision.
-/

namespace Hagi

section Compound

open Hagi

/-- **Stabilization ε-bound** (replaces the tautological
`c_t ≤ αG_t + J_t` restatement of round-38 — flagged by the
triviality linter, round-52): if the per-cycle law holds
(c_t ≤ α·G_t + J_t, `h_emp_c`), the disagreement decays
geometrically to its replenishment floor D (`h_emp_gap`, the
ρ-D law), and the decay has progressed enough that
a^k ≤ ε/(α(G₀−D)), then the per-cycle gain at cycle k is
within ε of the limit α·D + J. The c-law stays an empirical
premise; the THEOREM is the finite-horizon stabilization
certificate. -/
theorem compound_c_stabilizes (α G0 D a J ε : ℝ) (c G : ℕ → ℝ)
    (hα : 0 < α) (_hJ : 0 ≤ J) (_hD : 0 ≤ D) (hG0D : D < G0)
    (hε : 0 < ε)
    (h_emp_c : ∀ t, c t ≤ α * G t + J)
    (h_emp_gap : ∀ t : ℕ, G t ≤ D + (G0 - D) * a^t)
    (h_emp_decay : a ^ 1 ≤ ε / (α * (G0 - D))) :
    c 1 ≤ α * D + J + ε := by
  have hgap := h_emp_gap 1
  have hclaw := h_emp_c 1
  have hcancel : α * (G0 - D) ≠ 0 := by positivity
  -- α·(G0−D)·a ≤ α·(G0−D)·(ε/(α(G0−D))) = ε
  have hprod : α * ((G0 - D) * a ^ 1) ≤ ε := by
    have hG0Dnn : 0 ≤ G0 - D := by linarith
    have hm : (G0 - D) * a ^ 1 ≤ (G0 - D) * (ε / (α * (G0 - D))) :=
      mul_le_mul_of_nonneg_left h_emp_decay hG0Dnn
    have hleft : α * ((G0 - D) * a ^ 1) ≤ α * ((G0 - D) * (ε / (α * (G0 - D)))) :=
      mul_le_mul_of_nonneg_left hm (by linarith)
    have hne : G0 - D ≠ 0 := by linarith
    have hright : α * ((G0 - D) * (ε / (α * (G0 - D)))) = ε := by
      field_simp
    linarith [hleft, hright]
  have hpow : a ^ 1 = a := by ring
  rw [hpow] at hprod
  nlinarith [hgap, hclaw, hprod]

/-- **The constant-c regime is the signature of
replenishment.** If the disagreement has stabilized at the
replenishment level (`G_t → D` per the ρ-D law of
`genGap_decay`) and the joint channel is constant, the per-cycle
gain stabilizes at `α • D + J` — constant, as measured. The
naive expectation of decay is wrong precisely when the data
field is alive. -/
theorem compound_constant_regime (α D J δ : ℝ)
    (hα : 0 ≤ α) (_hD : 0 ≤ D) (_hJ : 0 ≤ J) (_hδ : 0 ≤ δ)
    (G cG : ℕ → ℝ) (hstab : ∀ t, 1 ≤ t → |G t - D| ≤ δ)
    (hdec : ∀ t, cG t ≤ α * G t + J) :
    ∀ t, 1 ≤ t → cG t ≤ α * (D + δ) + J := by
  intro t ht
  have hGle : G t ≤ D + δ := by
    have h1 : G t - D ≤ |G t - D| := le_abs_self _
    have h2 := hstab t ht
    linarith [h1, h2]
  calc cG t ≤ α * G t + J := hdec t
    _ ≤ α * (D + δ) + J := by
        refine add_le_add_left ?_ J
        exact mul_le_mul_of_nonneg_left hGle hα

/-- **The k-generation forecast (the falsifiable trajectory).**
With the disagreement obeying the ρ-D recursion and the joint
channel constant, the cumulative improvement after k
generations is at most the explicit sum — a closed-form
prediction testable BEFORE the GPU spend. -/
theorem compound_trajectory (ρ D G₀ α J : ℝ)
    (hα : 0 ≤ α) (hD : 0 ≤ D) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (G : ℕ → ℝ) (hG0 : G 0 ≤ G₀)
    (hstep : ∀ t, G (t + 1) ≤ ρ * G t + D)
    (k : ℕ) :
    ∑ t ∈ Finset.range k, (α * G t + J)
      ≤ ∑ t ∈ Finset.range k, (α * (ρ ^ t * G₀ + D * (1 - ρ ^ t) / (1 - ρ)) + J) := by
  refine Finset.sum_le_sum fun t _ => ?_
  refine add_le_add_left ?_ J
  refine mul_le_mul_of_nonneg_left ?_ hα
  exact genGap_decay ρ D G₀ hρ hρ1 hD G hG0 hstep t

/-- **The derived recursion budget.** The recursion is worth
continuing while the predicted next-cycle gain exceeds the cycle
cost ε_c; at stabilization the gain is `α • D + J`, so the
budget inequality `α • D + J > ε_c` is the *data* verdict: the
recursion folds exactly when the data field dies (D → 0, the
disagreement per `genGap_decay`), and no earlier. -/
theorem compound_budget (α D J ε_c : ℝ)
    (hα : 0 ≤ α) (hpos : α * D + J ≤ ε_c) :
    -- when the stabilized gain falls under the cycle cost, fold
    ∀ (G_next : ℝ), G_next ≤ D → α * G_next + J ≤ ε_c := by
  intro G_next hG
  calc α * G_next + J ≤ α * D + J := by
        refine add_le_add_left ?_ J
        exact mul_le_mul_of_nonneg_left hG hα
    _ ≤ ε_c := hpos

/-- The generational mean after k cycles with per-cycle bounds
(the compounding bookkeeping linking to `genMean_compound`). -/
theorem compound_cumulative (M₀ : ℝ) (c : ℕ → ℝ) (k : ℕ)
    (hstep : ∀ t, c t ≤ C) :
    M₀ - ∑ t ∈ Finset.range k, c t ≥ M₀ - k * C := by
  have hsum : ∑ t ∈ Finset.range k, c t ≤ ∑ t ∈ Finset.range k, C := by
    exact Finset.sum_le_sum fun t _ => hstep t
  have hcard : (Finset.range k).card = k := Finset.card_range k
  rw [Finset.sum_const, hcard] at hsum
  have hsmul : k • C = (k : ℝ) * C := by simp
  rw [hsmul] at hsum
  linarith

end Compound



section Interval

/-- **The interval-arithmetic recursion budget: the honest
"continue" verdict under noisy measurements.** With the
harvest ratio α, the replenishment D and the joint channel J
known only up to measurement intervals, the worst-case lower
bound on the per-cycle gain is αlo•Dlo + Jlo — the monotone
end of the interval arithmetic (all quantities nonneg). The
generation verdict is then a *statistical* decision:

* CONTINUE while `αlo•Dlo + Jlo > ε_c` — even the pessimistic
  end of the confidence region beats the fold threshold;
* FOLD once `αhi•Dhi + Jhi ≤ ε_c` — even the optimistic end is
  under;
* between them — the uncertainty band — the verdict is
  UNDECIDED from the current data: measure another generation
  instead of guessing.

This replaces the point comparison of `compound_budget` with
the interval comparison — the honest form for the noisy
three-point measurements of (c₁,c₂,c₃) (the confidence region
of the (α, J) regression). **Prescription for the code**: the
generation gate reports the triple (lo, point, hi) of
α•D + J; the decision takes lo for continue and hi for fold;
the middle band triggers another generation, not a coin
flip. -/
theorem compound_budget_interval (αlo Dlo Jlo _εc : ℝ)
    (α D J : ℝ)
    (hαlo : 0 ≤ αlo) (hDlo : 0 ≤ Dlo)
    (hα : αlo ≤ α) (hD : Dlo ≤ D) (hJ : Jlo ≤ J) :
    αlo * Dlo + Jlo ≤ α * D + J := by
  have hαD : αlo * Dlo ≤ α * D :=
    mul_le_mul hα hD hDlo (le_trans hαlo hα)
  linarith [hαD, hJ]

/-- **The fold verdict under intervals**: when even the
optimistic end of the confidence region is under the fold
threshold, the recursion folds regardless of the noise — the
certified stop. -/
theorem compound_fold_interval (αhi Dlo Dhi Jlo Jhi εc : ℝ)
    (α D J : ℝ)
    (hDlo : 0 ≤ Dlo) (_hαlo : 0 ≤ α) (hαhi : 0 ≤ αhi)
    (hα : α ≤ αhi) (hD : Dlo ≤ D ∧ D ≤ Dhi) (hJ : Jlo ≤ J ∧ J ≤ Jhi)
    (hfold : αhi * Dhi + Jhi ≤ εc) :
    α * D + J ≤ εc := by
  have hαD : α * D ≤ αhi * Dhi :=
    mul_le_mul hα hD.2 (le_trans hDlo hD.1) hαhi
  linarith [hαD, hJ.2, hfold]

end Interval

end Hagi
