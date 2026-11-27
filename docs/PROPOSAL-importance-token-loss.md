# PROPOSAL 28: importance-weighted token loss (q ∝ |ℓ_b|)

**Status: theory in primes (`ResidualMasking.masked_importance_unbiased`,
`covered_propensity_le`, `covered_window_propensity_zero`); code-side pending
in HAGI_v2 (`optimal_lm.py:637`, full-mean CE over all T positions).**

## Context

Today (line 637) `loss = CE(forward_seq(bx).reshape(-1, V), by.reshape(-1))` —
a uniform mean over all `B·T` positions. Every position costs the same backward
FLOPs, yet `gradCE_zero_of_onehot` shows positions whose prediction is one-hot
correct contribute exactly zero gradient. Chen 2020 (MAPNet, arXiv:2008.05333)
decomposes the gradient variance into a data term and a selection term and shows
the optimal proposal over positions is proportional to the gradient norm;
`|ℓ_b|` is its cheap surrogate (loss magnitude ≈ ‖∂ℓ/∂logits‖ for CE).

## What is proved

- `masked_importance_unbiased`: the estimator `Σ_b m_b·ℓ_b / q_b` with
  `P(m_b = 1) = q_b > 0` is unbiased for `Σ_b ℓ_b`.
- `covered_propensity_le`: positions already covered (`ℓ_b = 0`) can be given
  the minimal propensity without biasing — they contribute nothing.
- `covered_window_propensity_zero`: a fully covered window gets propensity 0
  and costs no backward at all.

## Minimal diff

```python
# before line 637 (state_carry branch); reuse previous-step per-position CE
lg = self.forward_seq(bx, state=state).reshape(-1, self.VOCAB)          # logits
ce = t.nn.functional.cross_entropy(lg, by.reshape(-1), reduction="none") # per position
q = ce.detach().abs() + 1e-3                                               # |ℓ_b| proposal
q = (q / q.mean()).clamp(max=4.0)                                          # cap: E[q] = 1
m = (t.rand_like(q) < q).float()                                           # Bernoulli draw
loss = ((ce * m) / q).mean()                                               # unbiased, ≤ backward on ~B·T
```

Cap `4.0` bounds the variance (importance weight `1/q ≥ 0.25`); positions with
`q ≈ 0` (covered) are almost never drawn — the masking saving of
`masked_saving_frac` is recovered *for free* without a separate boost path.
Regression test: on a batch where half the positions have `ℓ_b = 0`, the
expected `‖∇‖` matches the full-mean gradient within 5 % over 32 seeds, and
the backward cost drops by ≈ masked fraction.
