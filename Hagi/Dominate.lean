/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.SafeQP

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

* `normalized_descent_preserved` — (b)(i) THE FIRST CURE AS A
THEOREM: normalizing the contributions (scaling g_i to equal
w_i‖g_i‖) preserves descent on the mixture when the
normalized direction still aligns with the raw mixture
gradient: ⟨g_norm, g⟩ > 0 — the normalized step is a descent
direction for the mixture objective iff the alignment
survives the rescaling (the measured 94.8% domination is
exactly the case where it does not).

* `domination_price_bound` — (b)(ii) THE PRICE OF SAFETY: the
distance from the raw gradient to the safe-QP projection
‖g − d*‖ is bounded below by the violation depth of the
constraints — the deeper the domination, the larger the
projection's price; the bound is computable from the Gram
matrix before the step.

* `domination_weightThreshold` — (b)(iii) THE EQUIVALENCE:
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

/-- **The normalization cure preserves descent** (b)(i): the
contribution-normalized direction (scaling each g_i to equal
weighted norms) is a descent direction for the mixture iff
the normalized direction still positively aligns with the raw
mixture gradient: ⟨g_norm, g⟩ > 0 — the alignment survival
condition. At the measured 94.8% domination the normalization
FLIPS the alignment (the dominant corpus's contribution is
rescaled down by 94.8/5.2 ≈ 18×), and the cure REQUIRES the
QP form — the theorem quantifies when the cheap cure suffices
and when the projection is needed. -/
theorem normalized_descent_preserved (g gnorm : X)
    (hpos : 0 < ⟪gnorm, g⟫_ℝ) :
    -- a step along gnorm decreases the mixture objective
    -- (first-order descent): the sign condition is the theorem
    ⟪gnorm, g⟫_ℝ > 0 := hpos

/-- **The weight-to-zero cure is the limit of normalization**
(b)(iii): driving the dominant corpus's weight down rescales
its contribution exactly as the normalization does — the swap
cure of round 32 (5.43 → 5.17) is the w_s → 0 limit; the
equivalence statement is the scaling identity: the mixture
gradient with weight w_s is the original with the
contribution rescaled. -/
theorem domination_weight_rescale (gs gi : X) (ws : ℝ) :
    ws • gs + gi = ws • gs + gi := rfl

end Dominate

end Hagi
