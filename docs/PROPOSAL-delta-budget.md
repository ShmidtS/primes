# PROPOSAL: scale the EB delta by the number of checks on the current holdout

**Status: `PROPOSAL-index.md` (single source of truth).**

For: the HAGI_v2 implementation agent. Module
`Hagi/Probability/PairedGain.lean` (`prodPq_union_le_sum`, `delta_budget_scaled`).

**Changed algorithm: YES — one argument at two call sites (unified.py:548, :916).**

## Context

HAGI_v2 414ede5 (PROPOSAL 13) certifies adapters with
`paired_margin_eb(d, n_states, delta = 0.01)`. The bound is per call on the
holdout tail. The same tail is reused across ingests, so the probability that
*some* check falsely admits over a run is `M·0.01` (`admit_false_union_le`):
void after 100 checks.

## What is proved

- `prodPq_union_le_sum`: `P(∃ r, A r) ≤ ∑ α r` for checks with individual
  levels `α r` on one sample.
- `delta_budget_scaled`: with `α r = δ₀ / M` the total is `≤ δ₀` for every `M`.

## Minimal diff (sketch)

```python
# unified.py: keep a per-holdout counter of EB checks
#   self._eb_checks = getattr(self, "_eb_checks", 0) + len(cands)
#   delta = DELTA_BUDGET / max(1, self._eb_checks_planned)   # e.g. 0.01 total
#   paired_margin_eb(before - after, n_states=len(cands), delta=delta)
# reset `_eb_checks_planned` / `_eb_checks` whenever the holdout tail changes
# (new domain appended): the new tail is a fresh sample, the budget restarts.
```

Alternative without a counter: spend `delta = 0.01 / 2^k` on the k-th check
(doubling budget — total still `≤ 0.01`, simpler bookkeeping).
