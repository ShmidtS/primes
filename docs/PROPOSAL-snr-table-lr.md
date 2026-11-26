# PROPOSAL: clipped g-SNR learning rate for byte tables (half the optimizer state)

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module
`Hagi/Step/AdamSNR.lean`. Self-contained. All Lean anchors are proved and
frozen in primes; primes does not edit HAGI_v2 code.

**Changed algorithm: YES — optimizer choice for `self.vecs`/tables.**
The AdamW state `v_m`, `v_v` on byte tables (a row per byte) is replaced by a
fixed per-row learning rate `lr·min(SNR_row, 1)` measured over a warmup of
`W` steps.

## Context

`optimal_lm.py:209–212`: AdamW on every table row, `v_v[idx]` is one float per
weight — one third of the optimizer state. SGD-SaI (Xu et al. 2024,
arXiv 2412.11768) drops the second moment by scaling the learning rate with
the gradient SNR at initialisation and matches AdamW on Transformers.

## What is proved

- `adamFactor_eq_snr_scale` (Hagi/Step/AdamSNR.lean): for a stationary
  gradient with mean `μ` and std `σ` the Adam multiplier is
  `(μ/σ)/√(1+(μ/σ)²)` — the SaI factor `μ/σ` times `1/√(1+SNR²)`.
- `adamFactor_abs_le_one`: `|adamFactor| ≤ 1` — Adam saturates at high SNR.
- `adamFactor_snr_le`: at low SNR (`|μ| ≤ εσ`) the Adam factor is `≤ ε` —
  first-order agreement with SaI.

- `adam_le_clipped` (AdamSNR.lean): the clipped factor `min(SNR, 1)` is never
  below the Adam factor — the clipped-SaI step never under-steps Adam.
- `clipped_le_sqrt2_adam` (AdamSNR.lean): at `SNR ≤ 1` it exceeds Adam by at
  most `√2`.
- `clipped_le_sqrt2_adam_high` (AdamSNR.lean): the same at `SNR ≥ 1`.

Consequently the plain SaI factor `μ/σ` overshoots Adam by `√(1+SNR²)` at
high SNR (frequent bytes); the clipped factor stays within `√2` at low SNR
and saturates like Adam at high SNR. The `√2` upper bound at `SNR ≥ 1` is
not proved in primes (honest gap: Adam ≥ `1/√2` there).

## Minimal diff (sketch)

```python
# warmup W steps: accumulate per row s1 += g, s2 += g*g, cnt += 1
snr = (s1 / cnt).abs() / ((s2 / cnt - (s1 / cnt) ** 2).sqrt() + 1e-8)
row_lr = lr * torch.clamp(snr, max=1.0)          # clipped g-SNR rate
# afterwards: p -= row_lr * g (SGD-M on the table only), no v_m/v_v
```

Memory: `-2·|table|` floats for `v_m`, `v_v`, `+2·|table|` during the
warmup only. Matrices keep Muon (`lr_muon`), which has no second moment.

> CE numbers quoted from HAGI_v2 commits before `d90720a` were measured
> with the certified path training `epochs // 10` (see
> `Hagi/Unified/TrainBudget.lean`); the bounds above do not depend on the
> training budget, the empirical margins may change at full length.
