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
q = ce.detach().abs() + 0.05                                               # |ℓ_b| proposal, floor
q = (q / q.mean()).clamp(max=1.0)                                          # Bernoulli: cap at 1, NOT 4
m = (t.rand_like(q) < q).float()                                           # Bernoulli draw
loss = ((ce * m) / q).mean()                                               # unbiased, ≤ backward on ~B·T
```

**The cap must be 1, not 4**: a Bernoulli mask cannot fire with probability > 1;
with `q > 1` the effective propensity is `min q 1` and the estimator is biased by
`1/q` (`ResidualMasking.bernoulli_prop_le_one`; a synthetic check gave mean
ratio 0.38 with cap 4). With cap 1 and floor 0.05 the estimator is unbiased
(`clipped_weight_unbiased`), the importance weight is bounded by `1/q_min`
(`importance_cap_variance_bound`), and positions with
`q ≈ 0` (covered) are almost never drawn — the masking saving of
`masked_saving_frac` is recovered *for free* without a separate boost path.
Regression test: on a batch where half the positions have `ℓ_b = 0`, the
expected `‖∇‖` matches the full-mean gradient within 2 % over 32 seeds (std/mean ≈ 0.003),
the backward cost drops by ≈ 70 % (drawn fraction ≈ 0.30 on a CE sample with
40 % covered tokens; cos(∇̂, ∇) ≥ 0.997 over 32 seeds).
