# PROPOSAL: Smoothness telemetry for the first layer W1 (S_batch, gamma star)

**Status: theory implemented in primes (C684–C685); code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Written by the primes agent (C685;
modules `Hagi/Theory/FirstLayerLip.lean`, `Hagi/Theory/FirstLayerLipBatch.lean`).
Self-contained: no primes-repo context needed. All Lean anchors are proved and
frozen in primes (freeze identity 9249 after C685). This document is a proposal
only: primes does not edit HAGI_v2 code (user-push).

**Changed algorithm: NO. Guards: NO.** The proposal adds two telemetry values
and two derived numbers next to the learning rate. Nothing in the update
changes; an optional warning is the only behaviour that can differ, and it
only logs.

## (a) Context (one line)

Read-only @ca52eb4: the growth-block layer applies the update to `W1 : dim ×
hidden` (hagi/lm.py:586, block `blk["Wo"]`), the loss is the batch mean
cross-entropy `ce(reduction="mean")` (hagi/lm.py:299), and the Adam learning
rate is a constant (`3e-3` guarded, `1e-3` otherwise) that is never compared
with any curvature number.

## (b) What is proved (and what it assumes)

For the first layer `W1 : ι → δ → ℝ` with the read-out `wo`, the relu block
`relu(W1ᵀx + b)ᵀ wo`, and the batch objective `Σ_t CE_{y t}` over inputs
`x t`:

- `w1CE_descent_lemma` (Hagi/Theory/FirstLayerLip.lean:258), one input:
  `CE(V1) ≤ CE(W1) + ⟨∇CE, Δ⟩ + S/2·‖Δ‖_F²`, `S = ‖wo‖_F²·‖x‖₂²`.
- `w1BatchCE_descent_lemma` (Hagi/Theory/FirstLayerLipBatch.lean:113), batch
  (C685): the same for the batch sum with
  `S_batch = ‖wo‖_F²·Σ_t ‖x t‖₂²` and the batch direction
  `D_batch = Σ_t g_t ⊗ x_t` (`w1BatchDescentDir` = minus `w1BatchGradR`,
  `w1BatchDescentDir_eq`, :70).
- `S_batch_le_max` (:86): `S_batch ≤ B·‖wo‖_F²·max_t ‖x t‖₂²`, `B = |τ|`.
- `w1BatchCE_drop_of_step` (:186), `w1BatchCE_optimal_step_drop` (:218):
  step `W1 + γ•D_batch` ⇒ drop ≥ `nlDrop γ S_batch ‖D_batch‖_F`,
  `γ*_batch = 1/S_batch`, drop `‖D_batch‖²/(2S_batch)`.
- `w1MeanCE_optimal_step_drop` (:247), the form of the code (mean CE):
  `S_mean = S_batch/B`, `γ*_mean = B/S_batch`,
  drop `‖D_batch/B‖²/(2·S_batch/B)`.

Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound`.

Premises the code does not check: the activation masks of every input are the
same before and after the step (the theorems hold inside one activation
region, there is no global smoothness across the relu kink); the direction is
the plain batch gradient (the code applies Muon/Adam to the momentum `m1`).

## (c) Telemetry (minimal diff, `lm.py` around :299 and :586)

Two numbers per step, both cheap reductions:

```python
# per block, lm.py:586 (`Wo` is the block read-out)
wo_frob_sq = float((blk["Wo"] ** 2).sum())
# per batch, `a` is the layer input of the batch
x_l2_sq_max = float((a ** 2).sum(-1).max())
```

and the derived values logged next to the actual learning rate `lr`:

```python
x_l2_sq_sum = float((a ** 2).sum(-1).sum())       # Σ_t ‖x t‖₂²
S_batch = wo_frob_sq * x_l2_sq_sum                # sum loss
gamma_star = 1.0 / S_batch                        # sum loss, plain GD
gamma_star_mean = B / S_batch                     # mean loss (lm.py:299)
```

Theory: `S_batch` is the proved smoothness constant of the batch sum
(`w1BatchCE_descent_lemma`); `x_l2_sq_max` gives the bound
`B·wo_frob_sq·x_l2_sq_max` (`S_batch_le_max`). With these two values logged,
`γ* = 1/S_batch` stops being a formula and becomes a DERIVED number
(`docs/DERIVED-CONFIG.md`, row «Adam lr»).

Optional warning (telemetry, not a gate): `warn` if `lr > 2 / S_mean`
with `S_mean = S_batch / B`. Theory: `nl_coef_nonneg`
(Hagi/Theory/NegativeTransfer.lean:246) — for `0 < γ ≤ 2/L` the guaranteed
drop `nlDrop γ L G = γG² − Lγ²G²/2` is non-negative, for `γ > 2/L` it is
negative, so the step is outside the proved descent zone. The warning applies
to a plain gradient step; the Adam step is normalised, so the comparison is a
diagnostic, not a certificate (see (f) 2).

## (d) What this gives (and what it costs)

Gives: the learning rate of the block is logged next to the only proved
reference step size of that block; the gap `lr / gamma_star_mean` is a number
per step instead of an unmeasured honest gap.

Costs: two reductions and four scalars per step per block; no change to the
update.

## (e) Validation criterion (loop-5 style)

Log per step `wo_frob_sq`, `x_l2_sq_sum`, `x_l2_sq_max`, `S_batch`,
`gamma_star`, `gamma_star_mean`, `lr`. Accept the port iff on a full run:
every logged `S_batch` satisfies `wo_frob_sq·x_l2_sq_sum ≤ B·wo_frob_sq·x_l2_sq_max`
(`S_batch_le_max`); `gamma_star_mean = B / S_batch` to float precision; the
numbers are finite and positive whenever the batch is non-empty and `wo ≠ 0`.

## (f) Honest limits

- (1) The descent theorems need equal activation masks along the step; the
  code does not check it, and the constant is not valid across the kink.
- (2) The code's direction is the Muon/Adam step on `m1`, not the plain
  batch gradient `D_batch`; `γ*` is the reference of a plain gradient step.
- (3) The Adam step is normalised (`m̂/√v̂`); the warning threshold `2/S_mean`
  compares a step size of a different object.
- (4) `wo` and `x` move every step: `S_batch` is a per-step number, not a
  schedule; no theorem here says `lr` should equal `γ*`.
- (5) Float soundness: the theory is exact arithmetic; the code is float32.
- (6) Anchors are frozen in primes; re-verify before port.
