# PROPOSAL 35: certified worst-domain gate (radius with α/n) instead of a point threshold

**Status: theory in primes (`PairedGain.worst_gate_false_rollback_le`: P(false rollback) ≤ n·α;
`radius`, `radius_anti`, `clamped_budget_radius_le`; Hoeffding in `Hagi.Ensemble.Hoeffding`).
Code-side: `_worst_exceeds` in `hagi/selfdev/unified.py` compares the point growth
`grow > WORST_TOL_ROLLBACK` with no radius; `ca8bb9a` fixed the false rollbacks by
raising the window budget 2048 → 32768 (16× gate cost).**

## Why the point threshold fails at scale

The per-domain mean over `w` windows has noise `σ/√w`; the code's measurement
(0.16 nat at w = 16) gives σ ≈ 0.64. One-sided `P(mean > 0.25)` per domain is
0.059 at w = 16 and ≈ 0 at w = 237; over 138 domains (`worst_gate_false_rollback_le`)
the probability that *some* domain trips by noise is **≈ 1.0** at w = 16 —
exactly the observed false rollbacks — and ≈ 0 at w = 237.

## Minimal, trajectory-neutral diff

Use the radius the code already has (`paired_margin_eb`) with Bonferroni over the
measured domains, and compare the *certified* growth:

```python
def _worst_exceeds(self, pre_layout, source):
    ...                                                    # unchanged: per-domain diff vectors
    n_dom = len(n_pre)
    r = paired_margin_eb(diff, n_states=n_dom)             # α/n_dom inside: L = ln(2·n_dom/0.05)
    return grow - r > self.WORST_TOL_ROLLBACK               # was: grow > tol
```

Then `HAGI_OLD_GATE_WINDOWS` can go back to 2048 (or 4096): the radius at
w = 16 is 0.16, so `grow − r > 0.25` requires a true growth > 0.41 — no false
rollbacks at the old budget; at 32768 the gate sees true growths > 0.29.

## Regression test (numbers verified standalone)

```python
def test_worst_gate_certified_no_false_rollback():
    # synthetic: 138 domains, zero true growth, per-window noise σ = 0.64, w = 16
    rng = np.random.default_rng(0); trips = 0
    for _ in range(50):
        for d in range(138):
            grow = rng.normal(0, 0.64, 16).mean()            # zero true growth, noise only
            r = paired_margin_eb(np.zeros(16) - rng.normal(0, 0.64, 16), n_states=138)
            trips += (grow - r > 0.25)
    assert trips == 0          # point threshold: ~138 × 0.059 × 50 ≈ 400 false trips
```
