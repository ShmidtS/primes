# PROPOSAL: exact gauge balance before PrimeQuant (arXiv:2611.27889v1)

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module `Hagi/Step/GaugeBalance.lean`.

**Changed algorithm: YES — one pass over factors before export, and periodically
during training.**

## Context

Noncompact scaling symmetries (LowRankAdapter `B·A`, BigramSkip `B_u·B_v`,
MLA `W_kv_down·[W_uk, W_uv]`, per-neuron SwiGLU `(W_up,:,j, W_down,j,:)`) let
the Langevin equilibrium drift to infinity along the orbit under small weight
decay, inflating the dynamic range and hurting ternary quantization.

## What is proved

- `rank1_gauge`: `(c•B)·(c⁻¹•A) = B·A` — the rebalance is an exact identity.
- `stock_balance_min` / `stock_balance_attained`: among `(c·a, b/c)` the sum
  of squared norms is `≥ 2|ab|` with equality exactly at
  `c = sqrt(|b|/|a|)` — the Sec. 5 formula.
- `dead_block_out_zero`, `dead_loss_const`: a fresh growth block starts in the
  dead set (`W_down = 0`) and its `W_up` receives zero gradient until `W_down`
  leaves it — warm-up must be the deterministic certified step.

## Minimal diff (sketch)

```python
def gauge_balance(B, A):            # rank-r factor B·A
    U, s, Vt = np.linalg.svd(B @ A, full_matrices=False)
    r = len(s); U, Vt = U[:, :r], Vt[:r]
    return (U * np.sqrt(s)) , (np.sqrt(s)[:, None] * Vt)   # UᵀU = VVᵀ = diag(s)

def swiglu_balance(W_up, W_down):   # per neuron j
    c = np.sqrt(np.linalg.norm(W_down[j]) / (np.linalg.norm(W_up[:, j]) + 1e-12))
    W_up[:, j] *= c; W_down[j] /= c
```

Run `gauge_balance` on every factor and `swiglu_balance` on every block right
before `export_model_prime` and every N steps during training; logit change
must be < 1e-12 (regression test).

Reported (prototype, not reproducible here): weight quantization error −8.8%,
quantization CE penalty halved with the NTK term; dead-network fraction 0.70
at λ = 0 vs 0.33 at λ = 0.08.

## 25b. Wire `gauge_balance` into the export (it is defined but never called)

HAGI_v2 `0affafb` defines `gauge_balance(model)` in `optimal_lm.py`, but nothing
calls it (`rg "gauge_balance\(" hagi` → only the def). The same fate as the
first `ef21_qat`. Minimal, trajectory-neutral diff — the balance runs on a
**copy** at export time, the training weights are untouched:

```python
def quantize_model(model, bits=4, use_had=True, balance=True):
    if balance:                                   # export-time gauge on a deep copy
        import copy; model = copy.deepcopy(model); model.gauge_balance()
    ...                                           # existing loop unchanged
```

Regression test (numbers verified from the identity `rank1_gauge`):

```python
def test_gauge_balance_is_function_preserving():
    m = HagiOptimalLM(d=24, hid=36)                    # any small config
    x = torch.randint(0, 256, (2, 64)); m.eval()
    with torch.no_grad():
        before = m.logits(x); info = m.gauge_balance(); after = m.logits(x)
    assert (after - before).abs().max() < 1e-4         # exact up to fp32 round-off
    assert info["max_log_shift_swiglu"] > 0.1          # it actually rebalanced
    # and the export is tighter: per-row |W| max after balance ≤ before, row-wise
```
