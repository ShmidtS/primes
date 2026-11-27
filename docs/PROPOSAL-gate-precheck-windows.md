# PROPOSAL: skip the certification gate when the window count is provably too small

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module
`Hagi/Probability/PairedGain.lean` (`radius_eventually_le`, `n_suffices`).

**Changed algorithm: YES — a pre-gate on the window count (compute only, no
change to the acceptance rule).**

## Context

`paired_margin_eb` (trunk_ops.py:220) computes `eps = √(2σ²L/n) + 2bL/n` on
`n` windows. After fd040a7 the step is `max(k, n // 256)`, so a chunk shorter
than `256·k` bytes has fewer than 256 windows and a wider radius
(`short_domain_radius_ge`). Building the gate (256 windows, two CE passes)
costs time even when the outcome is already determined by the radius.

## What is proved

- `radius_eventually_le`: for every `ε > 0` there is an explicit
  `N(ε) = max(⌈8σL/ε²⌉+1, ⌈4bL/ε⌉+1)` such that `n ≥ N(ε) ⇒ radius ≤ ε`.
- `n_suffices`: acceptance needs `radius ≤ g − g₀`; hence a gain below the
  radius is never certifiable.
- Worst-case bound with the measured numbers (`b ≈ 4.5 nat`, `σ ≈ b/2`,
  `L = ln 40 ≈ 3.69`, `α = 0.05`): `N(0.1) ≈ 6700` windows, `N(0.5) ≈ 400`.
  A 200 KB chunk (`k = 64`, `step = 781`) carries only 3125 windows: under the
  worst-case `σ²` the old-domain gate at `ε = 0.1` is infeasible; real `σ²`
  is measured on the data and is usually far smaller, so the bound must be
  evaluated per call, not hard-coded.

## Minimal diff (sketch)

```python
# in paired_margin_eb, after computing sig2, b (before building 256 windows):
#   n_avail = number of windows the chunk can actually supply (step = max(k, n//256))
#   if n_avail < N(eps_target) with eps_target = the smallest gain worth admitting:
#       return float("inf")   # provably cannot pass; skip the second CE pass
# N(eps) = max(ceil(8*sig*L/eps**2)+1, ceil(4*b*L/eps)+1), L = log(2/alpha)
```

This only removes work that cannot change the decision; the acceptance rule
(`mean(d) > eps`) is untouched.

## Exact threshold (replaces the sufficient bound)

`radius_le_iff_ge_root` (PairedGain.lean): with
`L = ln(2/alpha)`, `A = sqrt(2*sig*L)`, `B = 2*b*L`,

    t*    = (-A + sqrt(A^2 + 4*B*eps)) / (2*B)
    radius(n) <= eps   <=>   1/sqrt(n) <= t*   <=>   n >= ceil(1/t*^2)

`rootT_is_root` proves `radiusT t* = eps`; the equivalence is necessary and
sufficient, so `ceil(1/t*^2)` is the smallest window count that can ever pass
at this `eps`. Use it instead of `N(eps)` in the pre-gate.

```python
A = (2*sig2*L) ** 0.5; B = 2*b*L
tstar = (-A + (A*A + 4*B*eps)**0.5) / (2*B) if B > 0 else eps / A
n_min = math.ceil(1 / tstar**2) if tstar > 0 else float("inf")
```
