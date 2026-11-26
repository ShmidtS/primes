# PROPOSAL: empirical-Bernstein radius for the paired-gain gate

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module
`Hagi/Probability/PairedGain.lean`. Self-contained. All Lean anchors are
proved and frozen in primes; primes does not edit HAGI_v2 code.

**Changed algorithm: YES — one function (`paired_gain`).** The lower bound
`mean(d) − 2.4·SE` is replaced by `mean(d) − radius(σ̂², b, n, α)` with a
clipped range `b`.

## Context

`hagi/base/trunk_ops.py::paired_gain` (trunk_ops.py:209–217) is documented as
"an empirical filter, not a formal certificate": `z·SE` with a fixed
`z = 2.4` is the normal approximation; it has no finite-sample guarantee and
`SE = 0` for `n = 1`. It gates the adapter (`ADAPTER_MIN_GAIN = 0.005`,
`ADAPTER_VAL_WINDOWS = 4096`), the fibre (`FIBER_MIN_GAIN = 0.01`) and the
growth blocks of `selfdev/unified.py`.

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
guarantee. Clipping the differences to `b = 2` nat (CE of a byte model rarely
differs by more) costs almost nothing; a heavy-tailed sample makes the
heuristic under-estimate while EB uses the measured variance.

## Minimal diff

```python
def paired_gain(before, after, alpha: float = 0.01, b: float = 2.0):
    d = np.clip(np.asarray(before) - np.asarray(after), -b, b)
    n = len(d)
    if n == 0 or not np.isfinite(d).all():
        raise ValueError("paired losses must be finite and non-empty")
    L = np.log(2 / alpha)
    r = np.sqrt(2 * d.var() * L / n) + 2 * b * L / n
    return float(d.mean()), float(d.mean() - r)
```

`z` is dropped; `alpha` replaces it. The gate thresholds stay unchanged.
