# PROPOSAL: residual masking + importance batch sampling in train_optimal

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Modules
`Hagi/Theory/ResidualMasking.lean`, `Hagi/Probability/MirrorHedgeMWU.lean`
(`selectedLoss_optimalPropensity_mse`, `..._le`, `..._eq_of_mse_eq`).

**Changed algorithm: YES — two local edits in `train_optimal` (optimal_lm.py).**

## Context

`HagiOptimalLM.train_optimal` trains every position with a uniform window
draw; the ExactBypass-covered positions (p = 1) already contribute CE = 0 and
zero logit gradient (`gradCE_zero_of_onehot`), but their features are still
pushed through the backward pass. The batch is drawn uniformly, although the
variance-minimising propensity is `q_b ∝ |ℓ_b|` (`selectedLoss_optimalPropensity_mse`).

## What is proved

- `gradCE p y c = p c − 1[c = y]`; at one-hot probabilities every gradient is
  0 ⇒ zeroing gradients on covered positions is an identity, not an
  approximation (`ResidualMasking.lean`).
- `masked_saving_frac`: the fraction of gradient work saved is `(N − cov)/N`.
- `selectedLoss_optimalPropensity_mse`/`_le`/`_eq_of_mse_eq`: the unbiased
  estimator `g_b / q_b` has minimal variance exactly at `q ∝ |ℓ_b|`;
  `MSE* = B⁻²((Σ‖g_b‖)² − ‖Σ g_b‖²)`.

## Minimal diff (sketch)

```python
# train_optimal, before the backward pass:
#   mask = (bypass_p >= 1 - 1e-6)           # covered by ExactBypass
#   loss_per_pos = loss_per_pos * (~mask)   # residual masking: gradient 0 anyway
# batch draw:
#   w = np.abs(loss_per_window) + eps        # |ℓ_b| from the previous pass
#   q = w / w.sum()                          # optimal propensity
#   idx = rng.choice(n_windows, size=B, p=q); loss = (loss_b / q[idx]).mean()
```

Honest boundary: the propensity is optimal for the loss magnitudes of the
*previous* pass (stale by one step); the variance bound holds for the current
`ℓ_b` only through the MWU guarantee (`MirrorHedgeMWU`), not pointwise.
