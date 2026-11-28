# PROPOSAL 27: asymmetric initialisation of grown blocks

**Status: theory in primes (`GaugeBalance.pairGrad_u_zero_at_d0`, `pairGrad_u_at_eps`);
code-side pending in HAGI_v2 (`grow_depth`, `optimal_lm.py:749`).**

## Context

`grow_depth` adds a SwiGLU block with `W_down = zeros` (identity at step 0,
FirstLayerGrad). `GaugeBalance.dead_loss_const` and `pairGrad_u_zero_at_d0`
show that in this state the loss is **constant in `W_up`**: the upper matrix
receives zero gradient until `W_down` leaves zero. The block is in the dead set
`D` of arXiv:2611.27889 (Theorem 2) and escapes only via `W_down`'s own
gradient, which is itself proportional to `W_up · x`.

## What is proved

- `pairGrad_u_at_eps`: with `d = ε ≠ 0`, `∂L/∂u |_{u=0} = −ε·x·y` — nonzero
  whenever `x·y ≠ 0`; the block is trainable from the first step.
- The function changes by `ε·u·x = 0` at `u = 0`: **asymmetry costs nothing at
  step 0** if the *lower* matrix is perturbed and the upper one is kept at zero.
  (Lu–Shin–Su 2020, arXiv:2007.06192 §5: randomised asymmetric initialisation.)

## Ready-made regression test (verified standalone: out0 = 0, ‖∂L/∂W_up‖ = 0.063 > 0)

```python
import numpy as np
def test_asym_init_trains_from_step_zero():
    rng = np.random.default_rng(0); d, h = 24, 8
    x = rng.standard_normal(d); y = rng.standard_normal(d)
    W_up = np.zeros((h, d)); W_down = 1e-3 * rng.choice([-1.0, 1.0], size=(d, h))
    out0 = W_down @ (W_up @ x)                       # identity at step 0
    g_up = np.outer(W_down.T @ (out0 - y), x)        # ∂L/∂W_up at W_up = 0
    assert np.abs(out0).max() == 0.0                 # function unchanged at step 0
    assert np.linalg.norm(g_up) > 0.0                # but the upper matrix trains
    # with W_down = 0 the same gradient is exactly 0 (dead_loss_const)
    assert np.linalg.norm(np.outer(np.zeros((d, h)).T @ (0 - y), x)) == 0.0
```

## Minimal diff

```python
# in grow_depth: W_down = zeros → W_down = ε · sign-noise; W_up = zeros (unchanged)
t.nn.Parameter(HAGI_GROW_EPS * t.randn(model.hidden, model.dim).sign())   # ε = 1e-3
```

Output at step 0 is still zero (`W_up = 0`), so the identity is preserved; the
gradient w.r.t. `W_up` is now `−ε·x·y` instead of `0`. Regression test: after
one optimizer step on a fresh block, `‖ΔW_up‖ > 0`.

## Also applies to `grow_width` (HAGI_v2 optimal_lm.py:703)

`grow_width` pads every matrix with zeros (`out = zeros(...); out[:r0, :c0] = p`),
so a new `emb` row (new byte id) and the new rows/columns of `W_down`/`W_up`
start in the dead set: the new embedding row receives gradient only through the
*old* columns it multiplies, and the new `W_down` columns are multiplied by zero
`W_up` rows — the same `pairGrad_u_zero_at_d0` situation. The prototype's
`grow_width_exact` (`emb_new = 0`, `W_down_new_to_old = eps·sign`,
`W_bi_old_to_new = eps·sign`) is the fix: keep the new embedding row at zero
(it must not fire for unseen bytes), but initialise the *new-to-old* and
*old-to-new* cross blocks of `W_down` with `eps·sign` so the new coordinates are
trainable from the first step while the function is unchanged (`rank1_gauge`;
output change `O(eps²·η)` after one step, `asym_step_output_quad`).

```python
# in grow_width, after the zero padding of W_down (shape d1 × h1):
W_down = pad(W_down, d1, h1)
W_down[d0:, :h0] = HAGI_GROW_EPS * t.sign(t.randn(d1 - d0, h0))     # new-to-old
W_down[:d0, h0:] = HAGI_GROW_EPS * t.sign(t.randn(d0, h1 - h0))     # old-to-new
```

Test: as for depth — after one step, `‖ΔW_up[new rows]‖ > 0` and the logits on
an old byte are unchanged at step 0 (`< 1e-5`).

## Measured on HAGI_v2 (scripts/ab_grow_init.py, 150 + 150 steps, two seeds)

| eps | seed | CE before grow | CE after 150 steps | first-step ‖∂L/∂W_up‖ |
|---|---|---|---|---|
| 0 | 0 | 1.7097 | 1.9466 | **0.0000** |
| 0 | 1 | 1.5076 | 1.5026 | **0.0000** |
| 1e-3 | 0 | 1.7097 | 1.9467 | 0.0003 |
| 1e-3 | 1 | 1.5076 | 1.5025 | 0.0003 |

The theory is confirmed exactly (zero gradient at `W_down = 0`, non-zero at
`eps`), **but the CE outcome is indistinguishable**: `W_down` leaves zero through
its own gradient (it multiplies `W_up·x ≠ 0`), so `W_up` unfreezes after a few
steps anyway, and 150 steps are enough to wash out the head start. At this scale
PROPOSAL 27 is a no-op; it would matter only when the growth step is followed by
very few training steps (quick adaptation) or when `W_down`'s own gradient is
gated (e.g. protected by GPM).

Control run (`grow=False`, same 150 extra steps, no growth): seed 0 also goes
1.7097 → 1.9466, seed 1 1.5076 → 1.5026 — **identical to the grown runs**. So
(i) `grow_depth` is bit-for-bit CE-neutral (the zero-init block is an exact
identity, `dead_block_out_zero`), and (ii) the seed-0 "degradation" is a
property of the 300-step schedule on this stream (overfitting of the batch-16
schedule), not of growth. No code-side issue here.
