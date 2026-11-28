# PROPOSAL 30: table-LazyAdam — moments and step only on touched rows

**Status: `PROPOSAL-index.md` (single source of truth).**

## Context

In the Adam branch for 2-D tables the moments are updated for **every** row
(`v_m[idx].mul_(b1).add_((1-b1)*g)` — for an untouched row `g = 0`, so the
moment just decays) and the step `p − upd_v` is applied to **every** row, so an
untouched row keeps moving on its stale moment. `LazyAdam.lazy_momentum_bound`
bounds the accumulated drift over `d` untouched steps by `c·β₁/(1−β₁)` — up to
`9c` at β₁ = 0.9; the code-side measurement (0.095 shift at weight 0.51 in 50
steps) sits inside that bound. The Muon branch already gates decay by `act`;
the Adam branch for tables does not.

## Why the *moments* must be frozen too (not only the step)

`return_step_ratio` / `return_step_underestimates` (primes): with decaying moments the
first step of a returning row is `(β₁/√β₂)^d`-times its healthy step in absolute
value — systematically too small (β₁² = 0.81 < β₂ = 0.999). Gating only the step
while the moments decay trades drift for under-stepping; freezing the moments
(`rowStep_inert`) removes both. The code agent's working tree is trying the
"step only" variant — the regression test should compare the *first-step ratio*
of a returning row, not only bitwise identity.

## Minimal diff

```python
act = (p.grad != 0).any(dim=-1, keepdim=True)        # rows touched by the batch
keep = lambda old, new: t.where(act, new, old)
self.v_m[idx].copy_(keep(self.v_m[idx], b1 * self.v_m[idx] + (1 - b1) * g))
self.v_v[idx].copy_(keep(self.v_v[idx], b2 * self.v_v[idx] + (1 - b2) * g * g))
p.copy_(keep(p.float(), p.float() - upd_v).to(p.dtype))
```

Untouched rows keep their moments verbatim (`rowStep_inert`: `rowStep lam 0 0 w = w`)
and take no step; a row that returns resumes from the moment it had, not from a
decayed one. Regression test: after 50 steps without a given byte, its table
row is bitwise unchanged (today: shift ≈ 0.095).
