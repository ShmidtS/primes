# PROPOSAL: reset the Adam timestep and moments per domain (Adam-Rel)

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module
`Hagi/Step/AdamRel.lean`. Self-contained. All Lean anchors are proved and
frozen in primes; primes does not edit HAGI_v2 code.

**Changed algorithm: YES — two lines.** At the start of training a new
domain reset `self.step_count = 0` and zero `v_m`, `v_v`.

## Context

`optimal_lm.py:151` initialises `step_count = 0` once per model;
`unified.py` trains domain after domain on the same optimizer state, so the
bias correction `1 − β^ts` (optimal_lm.py:211–212) is ≈ 1 and `v_v` carries
the previous domain's gradient scale. A new domain with a larger gradient
scale gets a step oversized by `s/√v₀`.

## What is proved

- `rel_reset_exact` (Hagi/Step/AdamRel.lean): after the reset the first
  step has bias-corrected second moment exactly `s²`.
- `rel_vhat_ge_global` (AdamRel.lean): whenever the scale grew (`v₀ ≤ s²`)
  the reset moment is at least the stale one — the global-timestep step is
  the larger.
- `adamFactor_scale_inv` (Hagi/Step/AdamSNR.lean): Adam is scale-invariant
  once `v` has caught up; the reset is what makes it catch up in one step.

Literature: Adam-Rel (Ellis et al., NeurIPS 2024) — nonstationary gradient
magnitude with a global timestep produces oversized updates; resetting the
timestep removes them. AdaShift (Zhou et al. 2018) — the same mechanism via
`g_t`/`v_t` correlation.

## Minimal diff

```python
# at the start of train_optimal for a NEW domain (not for resumed epochs)
self.step_count = 0
self.v_m = [t.zeros_like(p) for p in self.vecs]
self.v_v = [t.zeros_like(p) for p in self.vecs]
```

Resetting only `step_count` keeps the first moment (momentum carry-over) and
still removes the bias-correction lag; resetting the moments too is the
conservative Adam-Rel choice.
