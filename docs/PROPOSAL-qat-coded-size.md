# PROPOSAL 37 — QAT with a coded-size term on the cool-down

**Status:** `PROPOSAL-index.md` (single source of truth).

Source: cmix-neif-2.0 §4.3 (96 QAT epochs with a coded-size-of-weights term as the
learning-rate cool-down). Theory: `Hagi/Information/CodedSizeQAT.lean`.

## What

During the last `cool` steps of `train_optimal` add

    loss = CE + lam · Σ_rows H(hist of levels of W_row / scale_row),

with a differentiable proxy for the level histogram (softmax over the 2-bit levels
`{-3,-1,1,3}·s_row` at temperature 0.25). Default off.

## Why (proved)

- `prefixCode_ge_entropy`: Kraft `Σ e^{-ℓ_j} ≤ 1` ⇒ `E[ℓ] ≥ H(p)` (Jensen on log).
  The level entropy is an honest lower bound on coded bytes, so the term
  minimises a real bound, not a proxy for its own sake.
- `diffEntropyNormal_mono`: for `N(0,σ²)` the entropy is `log σ + ½log 2πe`,
  increasing in `σ` — the `−H` penalty is a range penalty, the same direction as
  gauge balance (`GaugeBalance.stock_balance_min`) but derived from volume.
  `FisherRowScore.rowFisherScore_isotropic` says where it is free: the RMS-
  normalised internal inputs make the Fisher score ∝ ‖e‖², so shrinking σ costs
  no quantisation accuracy there.

## Measured (`scripts/ab_qat_codedsize.py`, 60 steps, cool = 20, toy domain)

| lam | CE fp32 | CE quantised | export bytes | coded-bytes lower bound (2-bit H) |
|---|---:|---:|---:|---:|
| 0 | 2.2485 | 3.0326 | 10174 | 218 B |
| 3e-3 | 2.2421 | 3.0298 | 10174 | 205 B (−6 %) |
| 1e-2 | 2.2497 | **3.0232** | 10174 | **202 B (−7.3 %)** |

The ceiling is low at 2 bits (H ≤ 2 bits/weight, 4 levels); the term matters at
3–4 bits and for the entropy-coded container. Quantised CE also improves
(−0.01 nat at lam = 1e-2): flatter level histograms are also better-centred
for the stage-one quantiser.

## Patch (train_optimal, trajectory-neutral until enabled)

```python
QAT_CODED_LAM = float(os.environ.get("HAGI_QAT_CODED_LAM", "0"))   # 1e-2 = on
QAT_CODED_COOL = int(os.environ.get("HAGI_QAT_CODED_COOL", "20"))  # last N steps
LEVELS = t.tensor([-3., -1., 1., 3.])
def coded_entropy(W, tau=0.25):
    s = W.abs().amax(1, keepdim=True).clamp_min(1e-8) / 3.0
    p = t.softmax(-((W / s).unsqueeze(-1) - LEVELS.to(W.device)).abs() / tau, -1)
    m = p.mean(1); return -(m * (m + 1e-12).log()).sum()
# in the step loop:
if QAT_CODED_LAM > 0 and step >= total - QAT_CODED_COOL:
    loss = loss + QAT_CODED_LAM * sum(coded_entropy(p) for p in matrix_params)
```

## Test

```python
def test_qat_coded_size_lowers_entropy_bound_not_ce():
    assert bytes_a == bytes_b
    assert H_bound_b < H_bound_a            # measured 218 → 202 B
    assert ce_fp32_b <= ce_fp32_a + 0.01    # measured +0.001
```
