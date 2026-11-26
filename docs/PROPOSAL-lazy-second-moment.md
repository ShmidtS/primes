# PROPOSAL: lazy second moment `v_v` for inactive rows (LazyAdam completion)

**Status: theory implemented in primes; code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Module
`Hagi/Step/LazyAdam.lean`. Self-contained. All Lean anchors are proved and
frozen in primes; primes does not edit HAGI_v2 code.

**Changed algorithm: YES — one line.** `self.v_v[idx].mul_(b2)` decays every
row; the lazy rule decays only the rows touched by the batch.

## Context

`optimal_lm.py:204–212` already applies the lazy rule to weight decay
(`act = (p.grad != 0).any(dim=-1)`, commit 8f9e2ba, CE 1.334 → 1.183) but
still runs `self.v_v[idx].mul_(b2)` and `self.v_m[idx].mul_(b1)` densely on
all rows. A rare byte row (one touch per ~10⁴ steps) therefore has
`v → 0` between touches.

## What is proved

- `touch_den_dense_anti` / `touchStep_dense_mono` (Hagi/Step/LazyAdam.lean):
  with `v_d = β₂^d·v₀` the touch step `lr·g/(√v + ε)` is non-decreasing in
  the staleness `d`; with the lazy rule `v_d = v₀` it is constant.
- `vh_lazy_ge_dense` (LazyAdam.lean): the inequality survives bias
  correction — `β₂^d·v₀/(1 − β₂^t) ≤ v₀/(1 − β₂^t)`.
- `touchStep_le_eps` (LazyAdam.lean): the dense touch step is bounded only
  by `lr/ε`; with `lr ≈ 1e-3`, `ε = 1e-8` that is `1e5·lr`.
- `rowStep_inert_iterate` (LazyAdam.lean): an inactive row with zero Adam
  step is exactly preserved — the lazy weights are consistent with a lazy `v`.

## Numbers

`β₂ = 0.95`, `d = 10⁴` skipped steps: `β₂^{d/2} ≈ 20^{5000}` — the dense
touch step is clipped only by `ε`. Lazy: the step is `lr·g/√v₀`, the same as
for a frequently seen row. The excess per touch is strictly positive
(`touchStep_dense_excess_pos`) and the total excess `T·p·c` grows with the
training budget (`denseExcess_mono`) — at the full `epochs` (after the
`epochs // 10` fix) the lazy second moment matters more than in the short
runs that measured CE 1.334 → 1.183. The first moment is already lazy in effect
(`m` decays but `mh/√vh` stays bounded only through `v`).

## Literature (ask.sciencemadereadable)

STEP (Lu et al. 2023, arXiv 2302.01172): the accuracy drop of SR-STE with Adam
"originates from poorly estimated second moment (variance) in Adam states
given by the masked weights"; the fix is a reliable variance estimate first,
then a fixed variance as precondition. The same failure mode as
`touchStep_dense_mono` for rare rows: `v → 0` between touches, step capped only
by `eps` (`touchStep_le_eps`).

## Minimal diff

```python
self.v_m[idx].mul_(t.where(act, b1, 1.0)).add_((1.0 - b1) * g)
self.v_v[idx].mul_(t.where(act, b2, 1.0)).add_((1.0 - b2) * g * g)
```

with `act` broadcast to the shape of `v_m[idx]` (rows × 1). The bias
correction `1 − β^ts` is unchanged (it is a global counter; `vh_lazy_ge_dense`
shows the lazy value dominates for any `d ≤ ts`).

> CE numbers quoted from HAGI_v2 commits before `d90720a` were measured
> with the certified path training `epochs // 10` (see
> `Hagi/Unified/TrainBudget.lean`); the bounds above do not depend on the
> training budget, the empirical margins may change at full length.
