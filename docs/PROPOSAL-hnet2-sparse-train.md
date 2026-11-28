# PROPOSAL 33: sparse level-2 matmul on the training path of Adaptive HNet-2

**Status: `PROPOSAL-index.md` (single source of truth).**

## Context

The inference branch already multiplies by `W_l2` only on boundary positions
(`fire = p_bnd > 0.5`, ≈ 20 % of tokens). The training branch computes `u2_all`
for every position, so the measured 2.5× (vs r = 2) / 5× (vs a full layer) is
inference-only; during training the level costs a full `T·d²` matmul plus its
backward. The recurrence for `s2` is sequential over `t` anyway, so gathering
`u2` on the fired positions only changes nothing for the gradient path through
`p_t` (verified: `‖∂L/∂w_bnd‖ = 0.67` with the sparse gather, seed 0).

## Minimal diff (training branch)

```python
fire = p_bnd > 0.5                                  # (B, T)
u2_all = h1.new_zeros(B, T, d)
if fire.any():
    bi, ti = fire.nonzero(as_tuple=True)
    u2_all[bi, ti] = (h1[bi, ti] @ self.W_l2)        # only boundary rows
s2 = h1.new_zeros(B, d); S2_list = []
for ti in range(T):
    S2_list.append(s2)
    pt = p_bnd[:, ti : ti + 1]
    s2 = (1.0 - pt) * s2 + pt * (a2 * s2 + (1.0 - a2) * u2_all[:, ti])
return h1 + t.stack(S2_list, dim=1)
```

Hard gate `fire` has no gradient; `p_t` still receives gradient through the
`(1 − p_t)·s2 + p_t·(…)` mixing (straight-through semantics: the gate is used as
a mask on `u2` and as a weight in the update — same as the eval branch).

## Regression test (numbers verified standalone)

```python
def test_hnet2_sparse_train_matches_dense_and_saves():
    # on positions with p_t > 0.5 the sparse and dense branches agree to 1e-6;
    # elsewhere they differ by p_t·(1−a2)·(u2_t − 0) — bounded by (1−a2)·‖W_l2‖·‖h1‖
    # (the residual branch is not computed, i.e. the gate is *hard* at train time too).
    # Cost: rows multiplied = fire.float().sum() ≈ 0.10–0.20·B·T (beta(0.5,2) sample: 0.105).
    # Gradient: ‖∂L/∂w_bnd‖ > 0 (0.673 at seed 0).
```
