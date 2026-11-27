# PROPOSAL: archiver — arithmetic coder on a Hedge mixture (model + PPM-3 + zlib)

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module
`Hagi/Information/MixtureCoding.lean`.

**Changed algorithm: YES — `hagi/models/archiver.py` (mixing stage).**

## Context

`archiver.py` feeds the arithmetic coder the model's probabilities alone and
loses ~25% to `zlib -9` on typical streams. Mixture coding with Hedge weights
is never worse than the best expert by more than `log K + regret` nats/symbol.

## What is proved

- `mixCE_le_best_regret`: `-log Σ w_k p_k ≤ CE_j - log w_j` for every expert
  with `w_j > 0`.
- `hedge_negLogW_le`: Hedge weights `w_k = e^{-L_k}/Z` give
  `-log w_j ≤ (L_j - m) + log K`, so the mixture's CE is within `log K` nats of
  the best expert's cumulative loss (regret via `MirrorHedge.mwu_sqrt_bound`).

## Minimal diff (sketch)

```python
# archiver.py: experts = [model_next_prob, ppm3_next_prob, zlib_byte_prob]
# L[k] += -log(p_k[y]) per symbol; w = softmax(-L)  (Hedge, eta = 1)
# p_mix = sum(w[k] * p_k); arithmetic/range coder on p_mix (exact_roundtrip)
```

zlib as an expert: use its LZ77 literal/match probabilities (or a byte-level
order-0 fallback); no lock-in — weights adapt per stream.
