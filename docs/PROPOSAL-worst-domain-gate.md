# PROPOSAL 26: worst-domain rollback gate on by default

**Status: theory already in primes (`Hagi/Unified/TailGate.lean`); code-side
pending in HAGI_v2 (`hagi/selfdev/unified.py`, `HAGI_WORST_GATE`).**

## Context

The rollback gate in `unified.py` fires when the mean CE over old windows grows
by more than 25 % (`old_ce_post > 1.25·old_ce_pre`). `TailGate.mean_le_not_imp_max_le`
(primes) says this does **not** bound any single domain: with `n` old domains a
gain of `−g` on one can hide a loss of `+g·(n−1)` on another. The working tree
adds `_worst_domain_growth` / `_worst_exceeds` with `WORST_TOL_ROLLBACK = 0.25`
but keeps the feature behind `HAGI_WORST_GATE` (default `"0"`).

## What is proved

- `TailGate.max_le_imp_mean_le`: if the worst domain grows by at most `tol`,
  the mean grows by at most `tol` — the worst gate implies the mean gate, so
  switching on cannot admit a step the current gate rejects.
- `TailGate.mean_le_not_imp_max_le`: the converse fails — the current default
  admits steps that degrade a single domain arbitrarily.

## Minimal diff

```python
WORST_GATE = os.environ.get("HAGI_WORST_GATE", "1") == "1"   # was "0"
```

Log `worst_growth` / `worst_name` on every rollback so false positives can be
attributed to a domain. If the rollback rate rises by more than a few percent,
tune `HAGI_WORST_TOL_ROLLBACK` (0.25 → 0.30) rather than disabling the gate:
the mean gate is strictly weaker and the asymmetry is the whole point of
`ValWindows`-based continual learning.

## Addendum to PROPOSAL 25

`gauge_balance` rebalances SwiGLU and BigramSkip but **not the MLA factor**
`W_kv_down · [W_uk, W_uv]` (`optimal_lm.py`). Same one-liner:
`c = sqrt(‖W_kv_down[i]‖ / ‖W_uk[:, i]‖² + ‖W_uv[:, i]‖²)^{1/2}` per latent
index `i`; the rank-1 gauge `GaugeBalance.rank1_gauge` applies unchanged.
