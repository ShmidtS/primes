# PROPOSAL: validation windows must not overlap (`step >= k`) for the EB gate

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module
`Hagi/Data/ValWindows.lean`. Self-contained. All Lean anchors are proved and
frozen in primes; primes does not edit HAGI_v2 code.

**Changed algorithm: YES — one expression.** In `_old_domains_ce_vec`
(unified.py:1084) use `step = max(k, n // 256)` instead of `max(1, n // 256)`.

## Context

`paired_margin_eb` / `admit_false_le` (Hagi/Probability/PairedGain.lean) bound
the mean of **independent** paired differences. The window grid starts at
`0, step, 2·step, …` with `step = max 1 (n // 256)` and window length
`k = seq_len` (64). Whenever `step < k` consecutive windows share bytes, the
differences are positively dependent and the EB radius is under-estimated.

## What is proved

- `covers` / `adjacent_disjoint_iff` (Hagi/Data/ValWindows.lean): adjacent
  windows share no byte iff `k ≤ step`.
- `indep_threshold` (ValWindows.lean): with the current rule independence
  needs `256·k ≤ n` — at `k = 64`, `n ≥ 16384` bytes per domain. Shorter
  domains (the book has many) silently get overlapping windows.
- `radius_anti` (PairedGain.lean): the EB radius grows as `n` shrinks — the
  honest price of fewer windows, which the gate pays once the step is `≥ k`.

## Minimal diff

```python
step = max(k, n // 256)   # was max(1, n // 256): windows never overlap
```

Cost: for a 4 KiB domain `n ≈ 4096`, `step = 64` gives `64` windows instead
of `256` (radius ×2 by `radius_quarter_sqrt`); correctness of the bound is
restored for every domain length.
