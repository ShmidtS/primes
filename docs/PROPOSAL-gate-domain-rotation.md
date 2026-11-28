# PROPOSAL 34: rotate the capped old-domain set of the rollback gate

**Status: cost model in primes (`PairedGain.budget_split_radius_bounds`: `radius(W/m)` costs
√m in noise, m in bias); coverage consequence via `TailGate` (gate only sees the
measured domains). Code-side: `OLD_GATE_DOMAINS` / `OLD_GATE_WINDOWS = 2048` in
`hagi/selfdev/unified.py` (working tree, uncommitted).**

## Context

The gate now measures at most `m` old domains (`rng(11)`: trained domains first,
then random untrained ones). `_worst_domain_growth` compares pre/post by name and
honestly returns `(None, None)` on a layout change, so the worst gate is exact
**for the measured set** — and blind for the excluded domains, exactly as
`TailGate.mean_le_not_imp_max_le` warns at the set level: a domain that is never
measured cannot trigger a rollback. With `OLD_GATE_DOMAINS = m` the radius per
domain is `radius(W/m)` (≥ √m·noise, ≤ m·bias), so the cap buys cost and sells
coverage.

## Minimal, trajectory-neutral diff

Rotate the measured set across steps so that every old domain is measured at
least once every `⌈n/m⌉` steps, and keep the *last* measured growth per domain:

```python
def _old_domains_ce_vec(self, exclude, max_domains=None):
    ...
    limit = ...
    if limit < len(names):                               # capped: rotate, do not fix
        names = names[1:] + names[:1] if self._gate_rot else names   # advance by one
        self._gate_rot = (self._gate_rot + 1) % len(names)
    ...
```

and in `_worst_exceeds` use `max(last_growth[d] for d in measured_now ∪ stale)`
with a staleness bound (`≤ ⌈n/m⌉` steps); a stale growth older than that is
treated as "unknown" → `mean_gate_blind = True` in the ledger, never as 0.

Regression test: with `n = 12` old domains and `m = 4`, after 3 steps every
domain has been measured at least once (set coverage), and a synthetic +0.3 CE
jump on domain #11 is caught within 3 steps (today: never, it is untrained and
sorted last).
