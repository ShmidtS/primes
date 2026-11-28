# PROPOSAL 29d — Fisher-scored stage-two rows for every matrix (not only emb)

**Status:** `PROPOSAL-index.md` (single source of truth).

Generalises 29c (emb only, LIVE a1a3c53/1984f43) to all 2-D weights. The code
already has what it needs: `forward_seq(…, capture)` records the input of every
matrix (`capture[id(W)]`).

## Theory (`Hagi/Probability/FisherRowScore.lean`)

- `rowFisherScore X e = (1/B)·Σ_b (e·x_b)²` — the CE price of an error row is
  the mean square of the output error it causes, not `‖e‖²`.
- `rowFisherScore_eq_zero`: an error along a direction the batch never excites
  is free.
- `rowFisherScore_diag`: for uncorrelated inputs it is `Σ_j G_jj·e_j²`.
- With `c i := rowFisherScore X e_i`, `ResidualVQ.topk_residual_is_optimal`
  applies verbatim: top-k by `c` is the exact optimum for that score.
- emb is the diagonal special case (`G_jj = p_j(1 − p_j)`, `ceShift`).

## Measured (`scripts/ab_fisher_rows.py`, 60 steps, toy domain, equal bytes)

| scope | k | CE by ‖res‖² | CE by Fisher | gain |
|---|---:|---:|---:|---:|
| internal matrices (24×24 each), k = 8 | 8 | 2.4801 | 2.4451 | **−0.035 nat** |
| internal matrices, k = 4 | 4 | 2.5020 | 2.4819 | **−0.020 nat** |
| internal matrices, k = 32 (= all rows) | 32 | 2.3194 | 2.3194 | 0 (selection is moot) |
| emb (29c, live book) | 32 | — | — | −0.55 nat |

Smaller than emb because the internal matrices are 24 rows wide and their
inputs are RMS-normalised (G ≈ I); the gain grows with width and with
input anisotropy.

## Patch (export-time, trajectory-neutral)

```python
def quantize_model(model, bits=4, use_had=True, row_score=None, inputs=None):
    ...  # after par, Q for matrix `name`:
    if STAGE2_ALL and inputs is not None and name in inputs and STAGE2_ROWS.get(name, 0) > 0:
        R = W - dequant_per_row(par, Q); X = inputs[name]                    # (N, in) float64
        contrib = ((R @ X.T) ** 2).mean(1)                                   # rowFisherScore
        idx = np.argsort(-contrib)[:STAGE2_ROWS[name]]                        # top-k by c
        ...  # same stage-two code as emb
# caller: cap = {}; model.forward_seq(x_batch, capture=cap); inputs = {n: cap[id(p)] for n, p in named params}
```

Default off until the code agent measures on its domains; the number of rows
per matrix comes from `choose_emb_rows2`-style sweep (`sweep_ge_argmin`).

## Test

```python
def test_fisher_rows_beat_norm_at_equal_bytes_internal():
    assert bytes_fisher == bytes_norm
    assert ce_fisher < ce_norm            # measured −0.035 nat at k = 8
```
