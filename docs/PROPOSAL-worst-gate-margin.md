# PROPOSAL 35: certified worst-domain gate (radius with α/n) instead of a point threshold

**Status: `PROPOSAL-index.md` (single source of truth).**

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

## Measured with the real `paired_margin_eb` (σ = 0.64, 138 domains, 40 trials)

| w | radius (α/138) | point-threshold false trips / 5520 | certified trips |
|---|---|---|---|
| 16 | **2.088** | 319 (5.8 %) | 0 |
| 64 | 0.779 | 7 | 0 |
| 128 | 0.509 | 0 | 0 |
| 237 | 0.322 | 0 | 0 |

The point threshold fails exactly as predicted, and the certified gate never
trips on noise. **But** with Bonferroni over 138 domains and only 16 windows the
bias term `2·b·L/n` dominates (L = ln(2·138/0.05) ≈ 8.6, b = max|x|): the radius
is 2.09 nat, so a *true* growth would have to exceed 2.34 to roll back — the
gate becomes blind in the other direction. The certified form is therefore only
usable from w ≈ 64 (radius 0.78 → true growth > 1.0) and comfortable from
w ≈ 128 (0.51 → 0.76).

**Revised recommendation:** keep `HAGI_OLD_GATE_WINDOWS` such that w ≥ 128
(budget 32768 at n = 138 is right) *and* switch the comparison to
`grow − paired_margin_eb(diff, n_states=min(n_dom, 16)) > tol`; capping the
Bonferroni count at 16 trades a provable ≤ 16·α for a usable radius
(`worst_gate_false_rollback_le` with m = 16). The point threshold at w = 237 is
already noise-free in this simulation; the certified comparison is what keeps it
so when the domain count grows.

## Code-side (working tree, cycle 132): `HAGI_WORST_GATE_MARGIN` with `WORST_GATE_BONF = 16`

Radii with the real `paired_margin_eb`, σ = 0.64: w = 128 → 0.344 (Bonferroni 16)
vs 0.425 (138); w = 237 → 0.287 vs 0.355. At the 32768 budget (w = 237 at n = 138)
the certified gate rolls back on a *certified* growth > 0.25 + 0.29 = 0.54 with a
false-rollback bound of 16·α (`worst_gate_false_rollback_le`, m = 16), while the
point threshold trips on noise at 5.8 % per domain at w = 16. The switch is
currently off by default (`HAGI_WORST_GATE_MARGIN=0`); turning it on is
trajectory-neutral (rollback-time only) and should pass the same persistence-style
test as 26/3c19a8c: zero true growth ⇒ zero rollbacks over 40 trials.
