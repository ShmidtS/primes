# PROPOSAL 36 — Hidden-state kNN memory with a self-calibrated weight (SEMCACHE for HAGI)

**Status:** `PROPOSAL-index.md` (single source of truth).

Source: cmix-neif-2.0 §4.1 (Wölk, Hutter Prize 2026; −730 KB S = 0.77 %), theory in
primes `Hagi/Information/SemCache.lean`, measurement `scripts/ab_semcache_probe.py`
on the real `HagiOptimalLM.forward_seq(…, capture)` states.

## What

A decoder-side memory of `(hidden state, next byte)` pairs over the already
coded stream. Where the model is unsure, the `K` nearest past states (cosine)
vote for the next byte; the vote `q` is mixed into the model's `p` with weight
`λ_t·s`, where `s` is the best cosine and `λ_t` is **calibrated on the stream**:

    λ_t = λ · max(acc_kNN − acc_model, 0) over the last N verified positions

Zero parameters, zero archive bytes (the decoder rebuilds the memory from the
bytes it has already decoded — it is a function of the stream).

## Why (proved)

- `SemCache.false_ce`: a wrong neighbour costs exactly `−log(1 − λ·s)` nat.
- `SemCache.true_ce_lower`: a right one gives `p' y ≥ λ·s·q y`.
- `SemCache.worse_never_helps`: if `q y ≤ p y` the mix cannot beat the model —
  so the weight must vanish whenever the neighbours are not better than the
  model. Similarity alone does not do that (measured: max-cosine 0.93 at the
  99 % quantile on random bytes vs 0.996 on the periodic domain — overlapping).

## Measured (60 steps, k = 32 context, K = 8, λ = 0.3)

| domain | CE model | fixed λ·s | cosine gate τ = 0.9 | calibrated, N = 16 |
|---|---:|---:|---:|---:|
| periodic template | 4.6367 | 3.4591 (−1.18) | 4.0796 (−0.56) | **3.8777 (−0.76)** |
| Zipf bytes | 4.7785 | 4.8873 (+0.11) | 4.8217 (+0.04) | **4.7785 (0.0000)** |
| random bytes | 5.9905 | 6.1245 (+0.13) | 5.9978 (+0.01) | **5.9905 (0.0000)** |

The calibrated rule keeps 64 % of the periodic-domain gain and is exactly
neutral where the memory has nothing to say. HAGI's domains are template-like
(census, code, logs) — the expected case is the first row.

## Minimal patch (unified.py / optimal_lm.py, inference only)

```python
SEM_K, SEM_LAM, SEM_N = 8, 0.3, 16
def semcache_mix(p, h, mem, hist):            # mem: list of (h_norm, byte); hist: last N (knn_ok, model_ok)
    if len(mem) < SEM_K: return p
    Hm = np.stack([k for k, _ in mem]); hn = h - Hm.mean(0); Hn = Hm - Hm.mean(0)
    sim = (Hn / np.linalg.norm(Hn, axis=1, keepdims=True)) @ (hn / np.linalg.norm(hn))
    idx = np.argsort(-sim)[:SEM_K]; s = float(sim[idx].max())
    w = np.exp(sim[idx] / 0.02); w /= w.sum(); q = np.zeros(256)
    for j, wj in zip(idx, w): q[mem[j][1]] += wj
    acc = lambda v: float(np.mean(v)) if v else 0.0
    lam = SEM_LAM * max(acc([a for a, _ in hist[-SEM_N:]]) - acc([b for _, b in hist[-SEM_N:]]), 0.0) * s
    hist.append((int(np.argmax(q)) == y_true, int(np.argmax(p)) == y_true))   # decoder-side: y_true is known
    mem.append((h, y_true))
    return (1 - lam) * p + lam * q
```

Trajectory-neutral (inference/export path only); default off until the code
agent measures on its domains.

## Test

```python
def test_semcache_calibrated_never_hurts_and_helps_on_templates():
    m = _toy_model(); cap = {}; lg = m.forward_seq(X, capture=cap).detach()
    P = softmax; H = cap[-1]; y = Y                     # as in ab_semcache_probe.py
    assert ce_calibrated(ZIPF_BYTES) == ce_model(ZIPF_BYTES)       # exactly neutral (measured 0.0000)
    assert ce_calibrated(TEMPLATE_BYTES) < ce_model(TEMPLATE_BYTES) - 0.3   # measured −0.76
```
