# PROPOSAL: equalise residual forgetting, not sqrt-share, when splitting repair bytes

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module
`Hagi/Unified/RepairShare.lean`. Self-contained.

**Changed algorithm: YES — one line in `_repair_bytes` (unified.py:1024).**
Replace the share `∝ √Δ` by the share that equalises the residual
`Δ_i·(1 − c√x_i)` across domains (water-filling on residuals).

## Context

The repair gate is minimax (`WORST_TOL` on the worst domain,
`TailGate.max_le_imp_mean_le`). The byte share `∝ √Δ` is a heuristic between
proportional and minimax; it is not the minimax optimum.

## What is proved

- `resid c Δ x = Δ·(1 − c√x)` — residual increase after share `x`.
- `sqrt_share_not_minimax` (Hagi/Unified/RepairShare.lean): `Δ₁ = 4`,
  `Δ₂ = 1`, `c = 1/2`: the `√Δ` share gives `x₁ = 2/3` and residuals
  `4(1 − ½√(2/3)) ≠ 1(1 − ½√(1/3))`; the minimax optimum is `x₁ = 1`.

## Minimal diff (sketch)

```python
# share x_i solves Δ_i (1 - c sqrt(x_i)) = r, x_i = (1 - r/Δ_i)^2 / c^2, sum x_i = 1
# bisection on r in (0, min Δ): monotone in r → unique root; domains with
# Δ_i <= r get x_i = 0 (already below the residual of the worst).
```

`c` is a calibration constant (the CE drop per unit `√share` measured on the
last repair round); the water-filling is a one-dimensional bisection.

## Existence certificate (proved)

`water_filling_exists` (Hagi/Unified/RepairShare.lean): with `F(r) = ∑ share c Δᵢ r`
and `m = min Δ`, if `F(m) ≤ 1 ≤ F(0) = n/c²` then some `r ∈ [0, m]` has
`F(r) = 1`. `F` is continuous, non-increasing (`share_sum_mono`), strictly
above `F(0)` for `r < 0` (`share_strict_of_neg`), so bisection on `[0, m]`
converges. Feasibility condition on `c`: `∑ᵢ (1 − m/Δᵢ)² ≤ c² ≤ n`.

## After the revert (HAGI_v2 cc1bdd1)

The default went back to `sqrt`. The theory (`water_filling_exists`,
`sqrt_share_not_minimax`) is unchanged: water-filling is the minimax share only
when the per-domain gains `Δ_i` are known; `sqrt` is the robust choice when they
are not, which is the common case before calibration. Re-approval condition, so
the next attempt is not a coin flip: log per-domain repair gain under both
shares for one run and switch the default to `wf` only if the *worst-domain*
CE is not worse than under `sqrt` (`TailGate.max_le_imp_mean_le` — the mean is
not the right score here).
