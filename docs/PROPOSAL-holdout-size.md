# PROPOSAL: holdout slice large enough for a non-trivial growth-gate certificate

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module
`Hagi/Theory/HoldoutGateTwoWay.lean`, namespace
`Hagi.Theory.HoldoutGateTwoWay`; consolidated as clause (14)
of `hagi_master_v34`, `Hagi/Theory/MasterTheoremV3.lean`.
Self-contained: no primes-repo context needed. PRIORITY: MEDIUM — the
gate certificate already exists (`holdout_gate_two_way_delta`); this
proposal is about the SAMPLE SIZE the code must hold for it to say
something non-vacuous. This document is a proposal only: primes does
not edit HAGI_v2 code (user-push).

## (a) Context

The growth gate (`hagi/unified.py:504-581`) keeps a grown
block iff `holdoutMean(new) < holdoutMean(old) - 1e-4`, where the
holdout is the first ≤ 512 windows of the last 10% of the fresh
domain (fixed slice, both sides on the same windows). The two-way
certificate: IF the slice is an iid sample of size `k`
and `|Θ| ≤ N` states were scored on it, THEN with probability
≥ 1 − δ every accepted candidate satisfies
`popMean(new) ≤ popMean(old) + 2ε − margin` whenever
`log(2N/δ) ≤ 2k(ε/B)²`. At `k = 512` the bound is near-vacuous.
This proposal states the `k` the certificate needs.

## (b) The Lean anchor and the budget formula

`holdout_gate_two_way_delta` (Hagi/Theory/HoldoutGateTwoWay.lean:109):

- carrier: finite population `Ω`, loss `ℓ : Θ → Ω → ℝ` with
  `0 ≤ ℓ θ ω ≤ B` (`hℓ`), `k > 0` iid draws `Fin k → Ω`,
  candidate `cand : (Fin k → Ω) → Θ` MAY depend on the sample
  (that is the peeking);
- hypotheses: `|Θ| ≤ N` (`hcardΘ`), `0 < δ`, and the budget
  `Real.log (2 * N / delta) ≤ 2 * k * (eps / B) ^ 2` (`hbudget`);
- conclusion: `1 − δ ≤ P[ holdMean(cand) ≤ holdMean(old) − margin →
  popMean(cand) ≤ popMean(old) + 2ε − margin ]`.

Solving the budget for `k` (the requirement this proposal adds):

    k ≥ ln(2N / δ) / (2 · (ε/B)²)

with `N` = number of block states scored on the holdout slice
(`N ≥ 2 + number of checkpoint evaluations` — choosing the
best state by holdout CE is peeking over hypotheses).

## (c) Numbers (ε = 0.05·B, δ = 0.05)

| N | k required (ceiling) | code holds | ε that k = 512 does certify | 2ε |
|---|---|---|---|---|
| 2 (old + one candidate, no peeking) | ln(40/0.05)/0.005 = 876.4 → **877** | ≤ 512 | 0.0654·B | 0.131·B |
| 10 (working figure for |Θ|) | ln(400/0.05)/0.005 = 1198.3 → **1199** | ≤ 512 | 0.0765·B | 0.153·B |

So at `k ≤ 512` the certificate is "population risk of the accepted
block is no worse than old by more than ≈ 0.13–0.15·B with
probability 0.95" — near-vacuous. Interpolation: with
`k = 512` the 5% budget is met only at ε/B ≈ 0.065 (N = 2) /
0.076 (N = 10); at `k = 1200` it is met at ε/B = 0.05 (N = 10) and
at ε/B ≈ 0.0427 (N = 2).

## (d) Minimal change (proposal, not run)

Either one of, in order of preference:

1. **Holdout ≥ 1200 windows.** In `_maybe_grow` replace the cap
   `512` by `1200` (and make sure the fresh-domain tail supplies
   them: `n − cut ≥ 1200`, else the gate runs in the degraded mode
   of item 3). Cost: 2.3× more forward passes per gate verdict —
   one verdict per growth event, not per batch.
2. **Reduce |Θ| — peek less often.** The best-state pick at
   unified.py:563-567 runs every 50 batches; moving it to every
   200 or 500 batches divides the checkpoint count in `N` by 4–10,
   and `k` grows only logarithmically in `N`, so this is the
   cheaper lever ONLY when the checkpoint count dominates `N`.
   For `N = 10 → N = 2` the requirement drops from 1199 to 877.
3. **Report the ε.** If neither is done, log the ε the
   current `k` certifies: `eps_cert = B · sqrt(ln(2N/δ) / (2k))`,
   so the gate's guarantee is stated, not implied.

A five-line logging patch for item 3 (no behaviour change):

```python
import math
def _holdout_cert_eps(B, N, k, delta=0.05):
    """ε with which holdout_gate_two_way_delta holds for this slice."""
    return B * math.sqrt(math.log(2 * N / delta) / (2 * k))
# in _maybe_grow, next to the gate verdict:
#   ledger.note("holdout_cert_eps", _holdout_cert_eps(B=ce_max,
#                N=2 + n_checkpoints, k=len(holdout_idx)))
```

`ce_max` is not known in closed form for CE; use the largest
holdout CE seen on the slice as a conservative `B` (it only appears
as ε/B, so the figure is per-unit-loss).

## (e) What this buys

The growth gate gets a NON-TRIVIAL guarantee: "the accepted block's
population risk is no worse than the old one by more than 2ε − margin
with probability ≥ 1 − δ", with 2ε = 0.10·B at k = 1200, N = 10,
ε = 0.05·B instead of ≈ 0.15·B today. Every accepted growth then
carries a number a reader can compare with the measured gain.

## (f) Validation criterion

Log `holdout_cert_eps` for every gate verdict; assert
`2·eps_cert ≤ 0.10·B` on at least one growth event after item 1
(or assert the logged value equals the formula's value to 1e-12 —
the criterion is the log line, not the threshold).

## (g) Limits

- iid holdout is a MODEL: the code's slice is contiguous and
  overlapping windows of one domain tail. The formula bounds the
  iid deviation; serial correlation makes the TRUE effective k
  smaller. Nothing here is proved about overlapping windows.
- CE is not bounded by a known `B`; `hℓ` is a hypothesis the code
  does not check. The numbers are per-unit-loss (ε/B).
- `N` for the code is a count of evaluated states, not of `Θ` as
  a Lean type; if more states are scored than counted, `hcardΘ`
  fails silently.
- The link from `holdout_gate_two_way_delta` to `CommitGate.gen`
  is not formalised; this proposal does not close it.
- Lean does NOT prove the table in (c): `k ≥ 877 / 1199` are
  computed from the budget inequality in Python (rounded up); a
  Lean witness checks one instance (`ln 400 ≤ 2·1200·0.05²`,
  Mathlib `log_two_lt_d9`, `log_five_lt_d9`).
- Anchors are frozen in primes; re-verify before port.
