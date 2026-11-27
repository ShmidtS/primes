# PROPOSAL: empirical-Bernstein radius for the paired-gain gate

**Status: theory implemented in primes; the EB gate itself (`paired_margin_eb`, trunk_ops.py:220) is already in HAGI_v2 and certified exactly by `radius` / `admit_false_le` / `admit_false_union_le`; two `paired_gain` call sites remain (unified.py:548, :916).**

For: the HAGI_v2 implementation agent. Module
`Hagi/Probability/PairedGain.lean`. Self-contained. All Lean anchors are
proved and frozen in primes; primes does not edit HAGI_v2 code.

**Changed algorithm: YES — one function (`paired_gain`).** The lower bound
`mean(d) − 2.4·SE` is replaced by `mean(d) − radius(σ̂², b, n, α)` with a
clipped range `b`.

## Context

`paired_gain` (trunk_ops.py:209–217) is documented as "an empirical filter,
not a formal certificate": `z·SE` with a fixed `z = 2.4` is the normal
approximation; no finite-sample guarantee, `SE = 0` for `n = 1`.
`paired_margin_eb` (trunk_ops.py:220–) is the certified replacement already
used by the repair loop (unified.py:663, 847, 868) — its formula is exactly
`radius` and its `n_states` is exactly the union bound of
`admit_false_union_le`. Remaining `paired_gain` call sites:

- unified.py:548 — adapter admission (`ADAPTER_MIN_GAIN = 0.005`,
  `ADAPTER_VAL_WINDOWS = 4096`); candidates `cands` are scored on the same
  windows, so `n_states = len(cands)`;
- unified.py:916 — adapter check (`paired_gain(base, after)[1] > 0.005`),
  single candidate, `n_states = 1`.

## What is proved

- `radius` (Hagi/Probability/PairedGain.lean:35):
  `r = √(2σ̂²·ln(2/α)/n) + 2b·ln(2/α)/n`.
- `diffX_sum` (PairedGain.lean:43), `centX_sum` (PairedGain.lean:83): the sample
  mean of the paired differences is exactly the EB statistics.
- `admit_false_le` (PairedGain.lean:53): under the null of zero true gain,
  `P[mean − r > g₀] ≤ α` for any `n`.
- `admit_false_le_shifted` (PairedGain.lean:94): the same when the true gain
  is merely `≤ g₀` — covers every gate threshold, not only zero.

## Numbers (n = 4096, α = 0.01, L = ln 200 ≈ 5.3)

| σ̂ (nat) | b (nat) | EB radius | `2.4·SE` (code) |
|---|---|---|---|
| 1.0 | 4.0 | 0.061 | 0.038 |
| 1.0 | 2.0 | 0.056 | 0.038 |
| 0.3 | 2.0 | 0.033 | 0.011 |

The EB radius is ≈1.5–3× wider than the normal heuristic — the price of a
guarantee. It shrinks with `n` (`radius_anti`): at `n → 4n` the additive term
drops 4×, the square-root term 2× (`radius_quarter_add`, `_sqrt`). With the
EB gate `ADAPTER_VAL_WINDOWS = 1024` keeps the radius at 0.11 nat (σ̂ = 1,
b = 4) — still far below a typical gain of 0.1–0.5 nat — and cuts the
validation phase 4× (57 s → 3 s at 4096 → 1024). Clipping the differences to `b = 2` nat (CE of a byte model rarely
differs by more) costs almost nothing; a heavy-tailed sample makes the
heuristic under-estimate while EB uses the measured variance.

## Clipping the range (optional, certified)

`paired_margin_eb` uses `b = max|d|` — the full sample range, so one large
CE difference inflates the additive term `2bL/n`. Clipping `d` to `[-c, c]`
is safe: `clip_abs_le` (`|clip| ≤ c`), `clip_sub_abs_le_tail`
(`|clip c x − x| ≤ (|x| − c)₊`), `mean_clip_bias_le`
(`|mean d − mean clip c d| ≤ mean (|d| − c)₊`, Hagi/Probability/PairedGain.lean).
At `n = 4096`, `α = 0.01`, `σ̂ = 1`: `b = 4 → r = 0.061`, `c = 2 → r = 0.056`
(−8%), with a bias equal to the mean exceedance of `|d|` over 2 nat — zero
unless the paired CE differences have a tail beyond 2 nat.

## Minimal diff

```python
# unified.py:548 (adapter admission, K = len(cands) candidates)
gain = before.mean() - after.mean()
if gain > paired_margin_eb(before - after, n_states=len(cands), delta=0.01): ...
# unified.py:916 (single candidate)
return ad if (base - after).mean() > paired_margin_eb(base - after, n_states=1, delta=0.01) else None
```

`paired_gain` stays for logging only. Thresholds `0.005` are kept as the
`gain > eps` comparison, so the change is one call per site.

> CE numbers quoted from HAGI_v2 commits before `d90720a` were measured
> with the certified path training `epochs // 10` (see
> `Hagi/Unified/TrainBudget.lean`); the bounds above do not depend on the
> training budget, the empirical margins may change at full length.
