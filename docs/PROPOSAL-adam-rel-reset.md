# PROPOSAL: reset the Adam timestep and moments per domain (Adam-Rel)

**Status: `PROPOSAL-index.md` (single source of truth).**

For: the HAGI_v2 implementation agent. Module
`Hagi/Step/AdamRel.lean`. Self-contained. All Lean anchors are proved and
frozen in primes; primes does not edit HAGI_v2 code.

**Changed algorithm: YES — two lines.** At the start of training a new
domain reset `self.step_count = 0` and zero `v_m`, `v_v`.

## Context

`HybridMuonAdamW.__init__` (optimal_lm.py:151–159) initialises `step_count`,
`v_m`, `v_v`, `ema`; `train_optimal` constructs it anew per call
(optimal_lm.py:573) and no caller passes `opt_override`. Every domain
therefore starts with `ts = 0` and zero moments — the Adam-Rel reset by
construction. What was missing is only the certificate that this is the
right thing (and a guard against a future `opt_override` across domains).

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

## Interaction with the EMA schedule

`step_count` also drives the EMA rate `d_t = min(0.99, (1+t)/(10+t))`
(optimal_lm.py:216). Resetting `step_count` restarts that schedule at
`d ≈ 0.1`, so the EMA of the new domain would mix the previous domain's
weights with a share of up to 90% for its first ~100 steps
(`ema_stale_decay`, Hagi/Step/AdamDirection.lean). At the capped `d = 0.99`
the stale share is `< 1%` after ~460 steps instead. **Reset a separate Adam
timestep, not `step_count`** — irrelevant today because the whole optimizer
(including `ema`) is rebuilt, but binding if `opt_override` is ever shared
across domains.

## Regression guard (suggested test)

```python
def test_optimizer_is_per_domain():
    m = HagiOptimalLM(...)
    r1 = m.train_optimal(d1, epochs=1); opt1 = m._last_opt
    r2 = m.train_optimal(d2, epochs=1); opt2 = m._last_opt
    assert opt2 is not opt1 and opt2.step_count >= 1
```

