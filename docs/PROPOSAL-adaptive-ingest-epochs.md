# PROPOSAL: adaptive ingest epochs — stop by the marginal-forgetting rule

**Status: `PROPOSAL-index.md` (single source of truth).**

For: the HAGI_v2 implementation agent. Module
`Hagi/Learning/EpochTradeoff.lean`. Self-contained.

**Changed algorithm: YES — `CYCLE_EPOCHS` becomes a per-ingest stop rule.**

## Context

`neuro_symbolic_cycle.py` (ec80163) fixes `CYCLE_EPOCHS = 4` from a 3-domain
measurement (2 → 4 epochs: same new gain, half the old loss, +68% time).
The optimum depends on the domain: a domain that barely disturbs the old ones
should take fewer epochs; a disruptive one — more.

## What is proved

- `objective E = cost E + lam·oldReg E`, `cost E = c₀ + E·c₁`,
  `oldReg E = R₀(1 − ρ)^E`.
- `objective_delta`: the gain of epoch `E + 1` is
  `lam·R₀·ρ·(1 − ρ)^E − c₁`.
- `objective_delta_mono`: the gain is non-increasing (convex objective).
- `stop_condition`: the first `E` with `lam·R₀·ρ·(1 −ρ)^E ≤ c₁` is globally
  optimal.
- Measurement: `c₁ = 137 s`, `c₀ = 129 s`; forgetting 0.183 → 0.097 over
  2 epochs ⇒ `R₀(1 − ρ)² / R₀ = 0.53`, `(1 − ρ)² ≈ 0.53`, `ρ ≈ 0.27`.

## Minimal diff (sketch)

```python
# in the ingest loop, per epoch e:
#   d_old = mean tail CE of old domains after epoch e  (already computed for the gate)
#   R_e = max(0, d_old - d_old_before_ingest)           # residual forgetting
#   gain = LAM * R_e * RHO - C1                         # marginal value of next epoch
#   if gain <= 0 or e >= CYCLE_EPOCHS_MAX: break
# LAM: nat-equivalent weight of one nat of forgetting (suggested 400 s/nat, i.e.
# 1 nat ≈ 3 epochs), RHO = 0.27, C1 = 137 s measured on the box.
```

Every quantity except `LAM` is measured on the box; `LAM` is the one
policy constant (trade-off between time and forgetting).
