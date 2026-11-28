# PROPOSAL 29c — Fisher-weighted row selection for the emb stage two

**Status:** `PROPOSAL-index.md` (single source of truth).

Change: in `quantize_model` (hagi/models/optimal_lm.py, commit 1b55ac4) rank the
emb rows for the second stage by `p_i·‖res_i‖²` instead of `‖res_i‖²`, where `p_i`
is the token frequency in the training data. Same bytes, same code path, same
stage-two quantizer — only the score changes.

## Why (proved in primes, `Hagi/Budget/ResidualVQ.lean`)

- `topk_residual_is_optimal`: for any non-negative per-row score `c`, taking
  the top-k by `c` maximises the removed score among all sets of ≤ k rows. So
  the question is only *which* score is the loss.
- `ceShift`, `hasDerivAt_ceShift_zero`: the CE shift from perturbing one logit
  is `log(p·e^d + 1 − p) − q·d`, slope `p − q`; averaged over labels the
  first order vanishes and what remains is the Fisher term `½·p·(1 − p)·d²`.
  A row the model rarely predicts cannot buy CE at any residual norm.
- Measured (`scripts/ab_rows2_kstar.py`, 60 steps, toy domain, real
  EMB_ROWS2 code path): corr(ΔCE per block, Σ‖res‖²) = 0.008 — the norm score
  is MSE-optimal but CE-blind.

## A/B at equal bytes (measured, same script)

| k | CE, score ‖res‖² (code) | CE, score p·‖res‖² | gain | overlap |
|---|---|---|---|---|
| 32 | 2.9123 | 2.6509 | −0.2614 nat | 9/32 |
| 64 | 2.7319 | 2.6559 | −0.0760 | 32/64 |
| 128 | 2.6809 | 2.6560 | −0.0249 | 70/128 |

Reference points: k = 0 → 3.0326; k = 256 (all rows, norm score) → 2.6472.
**32 Fisher-scored rows (320 B) reach what 256 norm-scored rows (2560 B)
reach: 8× fewer stage-two bytes for the same export CE.**

## Patch

```python
# hagi/models/optimal_lm.py
EMB_FISHER = int(os.environ.get("HAGI_EMB_FISHER", "0"))  # 1 = rank emb rows by token_freq·‖res‖²

def quantize_model(model, bits=4, use_had=True, token_freq=None):
    ...
        if name == "emb" and EMB_ROWS2 > 0:
            res = W - dequant_per_row(par, Q); contrib = (res.astype(np.float64) ** 2).sum(axis=1)
            if EMB_FISHER and token_freq is not None:  # CE buys only rows the model predicts
                contrib = contrib * token_freq[:W.shape[0]]
            rows2 = np.argsort(-contrib)[:min(EMB_ROWS2, W.shape[0])]
    ...
# caller: token_freq = np.bincount(np.frombuffer(data, np.uint8), minlength=256) / len(data)
```

Trajectory-neutral (export-time only); default off until the code agent measures
on its domain.

## Test

```python
def test_emb_rows2_fisher_beats_norm_at_equal_bytes():
    m = _toy_model(); x, y = _heldout(); emb = m.emb.detach().clone(); FREQ = _token_freq()
    OM.EMB_ROWS2 = 32
    OM.EMB_FISHER = 0; qA, nA = OM.quantize_model(m, bits=2, use_had=False, token_freq=FREQ)
    OM.EMB_FISHER = 1; qB, nB = OM.quantize_model(m, bits=2, use_had=False, token_freq=FREQ)
    OM.EMB_FISHER = 0; OM.EMB_ROWS2 = 0
    assert nA == nB, "score must not change bytes"          # same export size
    OM.dequantize_into(m, qA); cA = ce(m, x, y); m.emb.data.copy_(emb)
    OM.dequantize_into(m, qB); cB = ce(m, x, y); m.emb.data.copy_(emb)
    assert cB < cA, f"Fisher score did not lower CE: {cB:.4f} vs {cA:.4f}"  # measured −0.26 nat
```
Note the MSE of the dequantised emb may be *worse* with the Fisher score — the
objective is CE, not weight MSE; the test must therefore assert on CE.
