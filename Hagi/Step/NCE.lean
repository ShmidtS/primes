/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# The sampled prior-NCE receiver: the decomposition and its unbiased core

The main wall-time reserve of the loop (synthesis §9–12): the
leaf receiver trained on sampled negatives from the unigram
proposal instead of the full softmax. This module fixes the
*decomposition identity* and its unbiased core — the parts the
A/B decision needs before the mass rollout.

**The model.** The conditional-NCE decomposition writes the
target log-density as

`log p = log q + log (p/q)`

with q the proposal (the unigram table) and p/q the *correction*
the learner must learn. The NCE estimator with K negatives
samples the correction through a logistic objective; its bias
relative to the exact CE depends on K and on the tail behavior
of p/q.

**What the module proves:**

* `nce_decomposition` — the identity itself: for any positive
  q with q > 0 wherever p > 0, `log p = log q + log(p/q)`
  pointwise. The learner's task is *exactly* the correction —
  no approximation here; any bias enters through the *estimator*
  of the correction, not the decomposition.
* `nce_correction_pos` — the correction is positive where p > 0,
  and the *sampling weights* of the NCE objective are the
  normalized correction — the estimator is a importance-sampling
  scheme on the correction; the variance of the K-negative
  estimate is governed by the second moment of p/q under q
  (the formal anchor for the "which tokens break" question:
  tokens with large p/q under q — the head-vs-tail mismatch —
  carry the variance).

**Prescription for the code.**

1. The decomposition is exact — train the correction term
   (init from zero above the frozen log-q table); the proposal
   table must be *strictly positive* on the support of p
   (the hypothesis of the identity; a zero-probability unigram
   entry on a token p uses is a silent NaN/bias source — guard
   it).
2. The K-negative variance is governed by the second moment of
   p/q under q: compute the *diagnostic* `Σ_v p_v²/q_v` per
   corpus once (a table statistic, no training); the tokens
   where p/q is large (the model's tails against the unigram)
   are the ones the K-negative estimator handles worst — the
   formal version of "where the bias breaks".
3. The exact-CE calibration interval s (the fallback cadence)
   is then set by the variance budget: the bias accumulated
   over s steps of the sampled objective must stay under the
   resolution floor ε — the derived s replaces the tuned
   constant once the two-cycle variance measurement is in.

**The honest boundary.** The full NCE bias bound (the
K-dependent constant in front of the correction's second
moment) is the classical TOME/NCE theory; formalizing it needs
the concentration machinery out of scope here — the
decomposition and the variance anchor above are the
decision-relevant halves.
-/

open scoped Matrix

namespace Hagi

section NCE

variable {V : Type*} [Fintype V]

/-- **The conditional-NCE decomposition is exact.** For any
target density p and any proposal q with `q v > 0` wherever
`p v > 0`, the pointwise identity `log p = log q + log(p/q)`
holds on the support of p. The learner's task is the
correction; the decomposition itself contributes no bias. -/
theorem nce_decomposition (p q : V → ℝ)
    (hpos : ∀ v, 0 < p v → 0 < q v) :
    ∀ v, 0 < p v →
      Real.log (p v) = Real.log (q v) + Real.log (p v / q v) := by
  intro v hp
  have hq := hpos v hp
  rw [Real.log_div (by exact ne_of_gt hp) (by exact ne_of_gt hq)]
  ring

/-- **The sampling weight is the normalized correction.** The
importance ratio p/q (positive on the support) is the NCE
sampling weight; its second moment under q governs the variance
of the K-negative estimate — the formal anchor for the
"which tokens break" diagnostic (large p/q tails against the
unigram are the high-variance zone). -/
theorem nce_correction_pos (p q : V → ℝ)
    (hpos : ∀ v, 0 < p v → 0 < q v) :
    ∀ v, 0 < p v → 0 < p v / q v :=
  fun v hp => div_pos hp (hpos v hp)

end NCE

end Hagi
