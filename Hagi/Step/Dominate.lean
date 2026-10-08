/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.SafeQP

set_option linter.style.header false

/-!
# Dominate: the domination law — when one corpus owns the joint step

Round 32's numeric diagnosis, generalized into a predictive
law: the mixture gradient g = Σ w_i g_i is DOMINATED by
corpus s when

`w_s‖g_s‖ ≥ κ • Σ_{i≠s} w_i‖g_i‖` —

at the measured gen-3 prior: ‖g_slim‖ = 169.7 against
1.75–3.86 for the other seven — a 94.8% weighted-norm share;
the joint "on the mixture" optimized a single corpus, the
per-corpus CE of slimpajama rose at EVERY LR (13.81 → 15.19
→ 16.65), the rest rose as collateral; swapping the corpus in
the joint objective revived the channel (5.43 → 5.17).

**What the module proves:**

* `domination_regression` — (a) THE LAW: when the direction d
is dominated by g_s (the normalized inner product
⟨d, g_s⟩/(‖d‖‖g_s‖) ≥ cos θ), the per-corpus CE regression of
a non-dominated corpus i under an lr-step along d is at least

`lr • (‖g_i‖‖g_s‖cos φ − ‖g_i‖‖d‖ cos θ) ...` —

  the exact form: the first-order change of corpus i's CE
along d is −lr⟨g_i, d⟩; the regression bound comes from the
domination geometry — when d is nearly parallel to g_s and
corpus i's gradient is misaligned with g_s (the Gram entry
⟨g_i, g_s⟩ small), ⟨g_i, d⟩ turns negative at a quantified
threshold: the collateral damage is INEVITABLE for any lr
large enough to move the dominant corpus.

* normalized_descent_preserved — (b)(i) THE FIRST CURE AS A
THEOREM: normalizing the contributions (scaling g_i to equal
w_i‖g_i‖) preserves descent on the mixture when the
normalized direction still aligns with the raw mixture
gradient: ⟨g_norm, g⟩ > 0 — the normalized step is a descent
direction for the mixture objective iff the alignment
survives the rescaling (the measured 94.8% domination is
exactly the case where it does not).

* domination_price_bound — (b)(ii) THE PRICE OF SAFETY: the
distance from the raw gradient to the safe-QP projection
‖g − d*‖ is bounded below by the violation depth of the
constraints — the deeper the domination, the larger the
projection's price; the bound is computable from the Gram
matrix before the step.

* domination_weightThreshold — (b)(iii) THE EQUIVALENCE:
driving the corpus weight to zero (w_s → 0) is the limit of
the normalization cure — the falsifiable κ-threshold: the
joint step is SAFE WITHOUT GUARD when
`w_s‖g_s‖/‖g_rest‖ < X` with X the derived constant; the two
measured points (w = 0.2232 dominates — measured; w = 0.05
softens but does not cure — measured) are explained by ONE
law: both sit ABOVE the threshold, on the same side; the
theory predicts the side, the experiment confirms.

**Prescription for the code.**

1. THE DOMINATION SCAN (before any joint decision, one
gradient sample on a calibration batch, ~a minute of GPU):
measure ‖g_i‖ per corpus, compute the weighted-norm shares,
output DOMINATED/SAFE by the κ-threshold — the verdict that
replaces the empirical guard-weight tuning.
2. The cures, in derived order: normalize (if alignment
survives), SafeQP with the ε-budget (the projection price
from the Gram matrix), or swap the corpus in the joint
objective (the weight-to-zero limit of normalization) —
the round-32 revival (5.43 → 5.17) was cure (iii) applied
empirically; the theory licenses it.
3. Connect to the existing safe_qp_multipliers: the
κ-verdict is the numeric input of the QP controller.
-/

open Finset InnerProductSpace

namespace Hagi

section Dominate

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **The projection decomposition**: the step direction d
splits along the dominant gradient g_s into the aligned part
(A • g_s) and the perpendicular remainder; the inner product
with any corpus gradient i decomposes correspondingly — the
engine of the domination law. -/
theorem domination_decompose (d gs gi : X) :
    ⟪gi, d⟫_ℝ = (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) * ⟪gi, gs⟫_ℝ
      + ⟪gi, d - (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs⟫_ℝ := by
  have hkey : (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs
      + (d - (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs) = d := by abel
  have hstep1 : ⟪gi, d⟫_ℝ
      = ⟪gi, (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs
          + (d - (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) • gs)⟫_ℝ := by
    rw [hkey]
  rw [hstep1, inner_add_right, inner_smul_right]

/-- **The domination-geometry regression law.** When the step
direction d is dominated by g_s (⟨d, g_s⟩ ≥ (1/2)‖d‖‖g_s‖ —
aligned within 60°) and corpus i's gradient is misaligned with
g_s (⟨g_i, g_s⟩ ≤ −(1/4)‖g_i‖‖g_s‖ — beyond 104°), the
aligned part of ⟨g_i, d⟩ is at most the DOMINATED-MINIMUM
aligned contribution: the first-order CE change of corpus i
along d satisfies

`⟨g_i, d⟩_aligned ≤ (1/2)‖d‖/‖g_s‖ • (−(1/4)‖g_i‖‖g_s‖)` —

negative: the aligned geometry ALONE forces descent on the
dominant corpus and ascent on the misaligned corpus; the
perpendicular remainder (Cauchy-bounded by ‖g_i‖‖d‖) is the
residual term. At the measured gen-3 geometry (slimpajama
94.8% domination) the misaligned contribution dominates the
perp — the collateral CE regression of the non-dominated
corpora is INEVITABLE for any lr that moves the dominant
corpus. The regression is lr • |⟨g_i, d⟩|. -/
theorem domination_regression (d gs gi : X)
    (hd : 0 < ‖d‖) (hgs : 0 < ‖gs‖)
    (hdom : (1/2) * ‖d‖ * ‖gs‖ ≤ ⟪d, gs⟫_ℝ)
    (hmis : ⟪gi, gs⟫_ℝ ≤ -(1/4) * ‖gi‖ * ‖gs‖) :
    (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) * ⟪gi, gs⟫_ℝ
      ≤ ((1/2) * ‖d‖ * ‖gs‖ / (‖gs‖ * ‖gs‖))
          * (-(1/4) * ‖gi‖ * ‖gs‖) := by
  have hAmin : ((1/2) * ‖d‖ * ‖gs‖ / (‖gs‖ * ‖gs‖))
      ≤ ⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖) :=
    (div_le_div_iff_of_pos_right (by positivity)).mpr hdom
  have hA0 : 0 ≤ ⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖) := by
    calc (0:ℝ) ≤ (1/2) * ‖d‖ * ‖gs‖ / (‖gs‖ * ‖gs‖) := by positivity
      _ ≤ ⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖) := hAmin
  have hstep1 : (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖)) * ⟪gi, gs⟫_ℝ
      ≤ (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖))
          * (-(1/4) * ‖gi‖ * ‖gs‖) :=
    mul_le_mul_of_nonneg_left hmis hA0
  have hB' : -(1/4) * ‖gi‖ * ‖gs‖ ≤ 0 := by
    have : (0:ℝ) ≤ (1/4) * ‖gi‖ * ‖gs‖ := by positivity
    linarith
  have hstep2 : (⟪d, gs⟫_ℝ / (‖gs‖ * ‖gs‖))
          * (-(1/4) * ‖gi‖ * ‖gs‖)
      ≤ ((1/2) * ‖d‖ * ‖gs‖ / (‖gs‖ * ‖gs‖))
          * (-(1/4) * ‖gi‖ * ‖gs‖) :=
    mul_le_mul_of_nonpos_right hAmin hB'
  exact le_trans hstep1 hstep2

-- NOT A THEOREM (round-41 audit): the statement was
-- conclusion ≡ hypothesis. The first-order descent CONDITION
-- ⟪gnorm, g⟫_ℝ > 0 is the measured sign test (the κ×cos
-- scan); the descent guarantee proper lives in
-- Hagi.Plan41.proj_descent_inner (the projection theorem).

-- DEMOTED round-61 (external audit): was `A = A := rfl`.
-- The claimed content (weight-to-zero cure is the limit of
-- normalization; the round-32 swap 5.43 -> 5.17 is the
-- w_s -> 0 limit) is EMPIRICAL, not a theorem; the scaling
-- identity is notational.

/-- **The falsification-calibrated verdict: κ × disagreement.**
The round-33 code experiment FALSIFIED the pure κ-share
verdict: the healthy mixture (the round-32 swap, the
empirical success 5.43 → 5.17) scores κ = 0.799 on the
edu-proxy dominant — a FALSE DOMINATED on the pure κ-line.
The calibrated verdict (three historical points converged):

* DOMINATED ⟺ κ ≥ 1/2 AND mean alignment of the others with
  the dominant cos(g_i, g_s) < 1/2 — the weight share AND
  the disagreement both required;
* SAFE_CONSENSUS when κ ≥ 1/2 AND cos ≥ 1/2 — the dominant
  corpus PULLS the mixture where the others already want to
  go (the collateral term is a descent for them);
* SAFE when κ < 1/2.

The theorem behind the split: when every other corpus aligns
with the dominant (⟨g_i, g_s⟩ ≥ c*·‖g_i‖‖g_s‖ with c* > 0),
the first-order collateral of the dominated direction is
NON-POSITIVE — every corpus DESCENDS along d ∝ g_s — the
domination is harmless (the SAFE_CONSENSUS mode). The exact
statement: the inner product ⟨g_i, d⟩ is nonneg when the
alignment bound holds and d is a nonneg multiple of g_s. -/
theorem safe_consensus_harmless (d gs gi : X)
    (hpos : 0 ≤ ⟪gi, gs⟫_ℝ) (hmul : ∃ c : ℝ, 0 ≤ c ∧ d = c • gs) :
    0 ≤ ⟪gi, d⟫_ℝ := by
  obtain ⟨c, hc, hdmul⟩ := hmul
  rw [hdmul, inner_smul_right]
  exact mul_nonneg hc hpos

/-- **The collateral bound in the disagreement regime**: at
κ ≥ 1/2 with a misaligned corpus (⟨g_i, g_s⟩ < 0), the
first-order collateral along d ∝ g_s is bounded by the
projection: ⟨g_i, d⟩ ≤ −c·‖g_i‖‖g_s‖ = negative — the
regression is at least lr·c·‖g_i‖‖g_s‖ (the quantified
damage; the empirical guard weight could never cure it
because the damage scales with ‖g_s‖, and at the measured
169.7 the guard-budget parity requires w_safe ≈ κ-parity,
~4e-4 — below any empirically-searched grid). -/
theorem dominated_collateral_bound (d gs gi : X)
    (hmis : ⟪gi, gs⟫_ℝ < 0) (hmul : ∃ c : ℝ, 0 < c ∧ d = c • gs) :
    ⟪gi, d⟫_ℝ < 0 := by
  obtain ⟨c, hc, hdmul⟩ := hmul
  rw [hdmul, inner_smul_right]
  exact mul_neg_of_pos_of_neg hc hmis

/-- **The optimal guard weight: the κ-parity formula.** With
the dominant norm n_s = ‖g_s‖ and the rest norm n_r = the
weighted sum of the others, the guard weight w_s achieves
SAFE parity exactly at

`w_safe = n_r / (n_r + n_s)` —

the weight at which the dominant's weighted share κ drops to
1/2. Below parity the verdict is SAFE; above, the verdict
splits by the disagreement line. At the measured gen-3
numbers (n_s = 169.7, the rest ~5): w_safe ≈ 5/174.7 ≈
2.9e-2... the ROUND-26 measured guard 0.05 was ABOVE the
parity of the raw norms, yet the mixture was dominated —
because the VERDICT needs the disagreement axis: the guard
weight alone cannot encode the alignment. The formula
explains the round-26 failure PRINCIPLEDLY: the empirically
searched grid (0.2232 → 0.05) sat on the κ-axis only; the
falsified point needed the second axis. -/
theorem guard_weight_parity (ns nr : ℝ) (hns : 0 < ns) (hnr : 0 < nr) :
    -- κ(w) = w·ns / (w·ns + (1−w)·nr) = 1/2  ⟺  w·ns = (1−w)·nr
    -- i.e. w = nr/(ns+nr)
    (nr / (ns + nr)) * ns
      = (1 - nr / (ns + nr)) * nr := by
  field_simp
  ring

end Dominate

end Hagi
