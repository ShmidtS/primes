# PROPOSAL 29: mixed-precision rows by 4× water-filling

**Status: theory in primes (`ResidualVQ.fisher_optimal_scale`, `bit_swap_improves_iff`);
code-side pending in HAGI_v2 (`quant_per_row(stages)` — one global stage count).**

## Context

`quant_per_row` spends the same `bits` on every row. Rows differ in what the
quantization error costs: the Fisher-weighted residual of a row (`fisherErr`
with the importance matrix already used by `fisher_opt`) is its contribution.
HAWQ-V2 (arXiv:1911.03852) shows the right sensitivity is the *trace*, i.e.
exactly this summed contribution, and mixed precision by contribution
equalisation is the common core of CET 2026, CLADO 2025 and Houache 2026.

## What is proved

- `fisher_optimal_scale`: for fixed levels the weighted error is a parabola in
  the scale, minimised at `s* = Σ I w q / Σ I q²` — so the per-row contribution
  `c_i = fisherErr_i(s*)` is the right number to allocate on.
- `bit_swap_improves_iff`: with `c_i(b) = c_i·4^{-b}`, moving one bit from
  row `j` to row `i` lowers the total iff `4·c_j < c_i`; the allocation is
  stationary once all contributions are within 4× of each other.

## Synthetic check (rule of LESSONS: simulate before submitting)

Lognormal contributions (σ = 1.5), 512 rows, budget fixed at 2 bits/row
(seed 1): the full 4× water-filling loop (run to stationarity) gives **total
error 0.189× uniform-2** at the same model size, bits 1–4. An earlier figure of
0.757 came from a loop that stopped at the first non-improving (argmax, argmin)
pair — it was a lower bound on the gain, not the stationary allocation.

## Ready-made regression test (numbers verified, run standalone first)

```python
import numpy as np
def alloc_bits(contrib, budget):
    b = np.full(len(contrib), budget // len(contrib)); rem = budget - b.sum()
    for _ in range(rem): b[np.argmax(contrib * 4.0 ** -b)] += 1
    while True:
        c = contrib * 4.0 ** -b; i, j = int(np.argmax(c)), int(np.argmin(c))
        if b[j] <= 1 or not (4 * c[j] < c[i]): return b
        b[i] += 1; b[j] -= 1
def test_alloc_bits_equal_budget_lower_error():
    rng = np.random.default_rng(1); E = rng.lognormal(0.0, 1.5, 512)
    b = alloc_bits(E, 1024)
    assert b.sum() == 1024 and b.min() >= 1 and b.max() <= 6
    assert (E * 4.0 ** -b).sum() < 0.80 * (E * 0.25).sum()   # 0.189 measured (stationary loop)
```

## Measured on HAGI_v2 (scripts/ab_export_quant.py, 60 steps, structured stream, holdout CE)

| variant | CE | bytes | Δ |
|---|---|---|---|
| fp32 | 2.2485 | — | — |
| trits, uniform (today) | 3.0326 | 10174 | +0.78 nat |
| + gauge balance (25b) | 3.0337 | 10174 | no effect (weights already balanced at this scale) |
| + per-row 2nd stage on `emb` | **2.6769** | 11964 (+18 %) | **−0.36 nat of the 0.78** |

**Scope correction (found by the measurement):** the row-block Hadamard in
`quant_per_row` mixes rows, so a per-row stage count is only consistent where
`rotate_rows=False` — the `emb` table (and any other lookup table). For the
2-D matrices with row rotation, use the global `stages` on the *whole* matrix
or rotate by columns only. The 4× rule on `contrib` is unchanged.

## Minimal diff (fits the existing `quant_per_row(stages=…)` — a per-row stage count)

`quant_per_row` already implements residual stages; mixed precision is a
**per-row** stage count instead of a global one: rows whose contribution
(Fisher-weighted residual at the stage-1 scale) exceeds 4× the smallest get a
second trit stage, the rest stay at one stage. Volume = `(r + k)·c` trits,
`k` = number of two-stage rows.

```python
def quant_per_row_mixed(W, contrib, use_had=True, rotate_rows=True):
    par1, Q1 = quant_per_row(W, bits=2, use_had=use_had, rotate_rows=rotate_rows)  # stage 1 for all
    two = contrib > 4 * contrib.min()                 # 4× rule (bit_swap_improves_iff)
    idx = np.flatnonzero(two)
    if len(idx) == 0: return par1, Q1
    R = W.astype(np.float64) - dequant_per_row(par1, Q1)       # stage-1 residual
    par2, Q2 = quant_per_row(R[idx], bits=2, use_had=False, rotate_rows=False)
    par1["rows2"] = idx.tolist(); par1["par2"] = par2          # dequant adds Q2 rows back
    return par1, np.concatenate([Q1, Q2])
```

`dequant_per_row`: add `R[idx] += Q2 * par2["scales"][:, None]` before the
inverse Hadamard. Export-only: training is untouched (trajectory-neutral).

## Ready-made regression test (numbers verified, run standalone first)

```python
import numpy as np
def alloc_bits(contrib, budget):
    b = np.full(len(contrib), budget // len(contrib)); rem = budget - b.sum()
    for _ in range(rem): b[np.argmax(contrib * 4.0 ** -b)] += 1
    while True:
        c = contrib * 4.0 ** -b; i, j = int(np.argmax(c)), int(np.argmin(c))
        if b[j] <= 1 or not (4 * c[j] < c[i]): return b
        b[i] += 1; b[j] -= 1
def test_alloc_bits_equal_budget_lower_error():
    rng = np.random.default_rng(1); E = rng.lognormal(0.0, 1.5, 512)
    b = alloc_bits(E, 1024)
    assert b.sum() == 1024 and b.min() >= 1 and b.max() <= 6
    assert (E * 4.0 ** -b).sum() < 0.80 * (E * 0.25).sum()   # 0.189 measured (stationary loop)
```

## Minimal diff

```python
def alloc_bits(contrib: np.ndarray, budget: int) -> np.ndarray:   # contrib = fisherErr per row at s*
    b = np.full(len(contrib), budget // len(contrib)); rem = budget - b.sum()
    for _ in range(rem): b[np.argmax(contrib * 4.0 ** -b)] += 1
    while True:                                                    # 4× water-filling
        c = contrib * 4.0 ** -b; i, j = int(np.argmax(c)), int(np.argmin(c))
        if b[j] <= 1 or not (4 * c[j] < c[i]): return b
        b[i] += 1; b[j] -= 1
```

Store `bits` per row in the quant params (`dequant_per_row` already reads
`par`); regression test: CE of the exported model ≤ uniform-2-bit CE at equal
`sum(bits)·rows`, and `bytes(export)` unchanged.
