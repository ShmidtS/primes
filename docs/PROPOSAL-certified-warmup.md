# PROPOSAL: certified warm-up of a grown block via `_certified_finite_step` (HOLD semantics) instead of plain Adam

**Status: theory implemented in primes (C657/C660/C663/C665); code-side pending in HAGI_v2.**

For: the HAGI_v2 implementation agent. Written by the primes agent
(C644; theory landed in primes, module `Hagi/Theory/FunctionPreservingGrowth.lean`,
namespace `Hagi.Theory.FunctionPreservingGrowth`, section WarmUp).
Self-contained: no primes-repo context needed. All Lean anchors are
proved and frozen in primes. PRIORITY: HIGH — this
closes the only remaining uncertified gap of function-preserving
growth (the h1 premise of C642). This document is a proposal only:
primes does not edit HAGI_v2 code (user-push).

## (a) Context (one line)

Current (hagi/unified.py:423-436 @ca52eb4): after `m.grow()` the new
block is warmed up by bare `torch.optim.Adam` (2 epochs, ≤ ~300
steps/epoch, lr 3e-3, trunk frozen) and kept iff holdout CE did not
get worse. primes C642 proves: IF every warm-up step is certified
(obj decreases by a nonnegative drop) THEN train-objective ≤ fOld
for any gate verdict. That premise is a hypothesis today — nothing
in the warm-up checks it. The codebase already has a certified step:
`ByteLM._certified_finite_step` (hagi/lm.py:826-879 @ca52eb4).

## (b) The code contract and the Lean anchors

Exact contract of `_certified_finite_step(self, ctx, nxt, lr_scale=1.0,
max_backtracks=12) -> float` (hagi/lm.py:826 @ca52eb4; the task's
":793" is the docstring line offset in the pinned listing; the `def`
line is 826 at ca52eb4 and at HEAD):

- Operates on the LIVE trunk params `(emb, W1, b1, W2, b2)` only
  (`q` excluded, wave 233); takes a snapshot.
- Direction: `−∇ CE(full_logits(ctx)[:, -1, :], nxt)` on that batch.
- If `‖d‖² ≤ 1e-24` → return `0.0` (HOLD, params untouched).
- Step size: `eta = lr_scale · 4·A/r2`, `A = ‖d‖²`, `r2` = mean over
  the batch of `range(jvp tangent)²` from one `torch.autograd.functional.jvp`
  (fallback `1.0` if the JVP throws or `r2 ≤ 1e-24`).
- Loop `range(max_backtracks + 1)` = 13 trials: restore snapshot,
  `θ ← θ + eta·d`, compute `logits1`; `upper = finite_displacement_ce_upper(logits0, logits1, nxt)`;
  `drop = −upper`; if `drop > 1e-12` → return `drop` (COMMIT, params
  stay at the trial point); else `eta *= 0.5`.
- After the loop: restore snapshot, return `0.0` (HOLD, exact rollback).
- Caller today: one place, `hagi/lm.py:999` (byte-LM refine loop,
  8 rounds × batches of 32; ledger notes the bounds do NOT telescope
  across batches). NOT called from `unified.py` at all.

What the certification rests on (`finite_displacement_ce_upper`,
hagi/lm.py:235-248): the log-sum-exp range lemma
`CE(z+d) − CE(z) ≤ ⟨softmax(z) − onehot(y), d⟩ + range(d)²/8` applied to the ACTUAL finite logit displacement — no linearity in θ is assumed; the JVP only proposes `eta`.

Lean anchors (all with axioms `[propext, Classical.choice, Quot.sound]`):

- `stepEps` — admission threshold `1e-12`;
- `CertifiedFiniteStep obj θ θ' drop` — the contract as an abstract predicate:
  COMMIT (`stepEps < drop ∧ obj θ' ≤ obj θ − drop`) ∨ HOLD (`θ' = θ ∧ drop = 0`);
- `warmup_h1_of_certified_steps` — every step of the trajectory produced by a certified step ⇒ h1 of C642: `∀ t, obj (θ (t+1)) ≤ obj (θ t) − drop t ∧ 0 ≤ drop t`;
- `warmup_safe_of_certified_steps` — with identity start `obj (θ 0) = fOld` ⇒ `obj (θ n) ≤ fOld` (C642 `warmup_safe`);
- `post_warmup_growth_safe_of_certified_steps` — same through the rollback gate `_maybe_grow`, for BOTH verdicts (C642 `post_warmup_growth_safe_of_certified`);
- `uncertified_step_not_certified` — NEGATIVE: a plain step that grows obj satisfies the contract for no `drop`;
- `batch_drop_not_global` — NEGATIVE: a step certified on a batch objective `obj_b` (drop 1/2) can grow another objective `obj` by 1 — per-batch drops do not telescope onto a different functional.

Why the abstract form differs from the code text: the code returns a float and mutates params; the predicate names the same two exits. `obj θ' ≤ obj θ − drop` is exactly `CE_after ≤ CE_before − drop`, i.e. `drop = −upper` with `upper ≥ CE_after − CE_before`.

## (c) Minimal Python diff (in `hagi/unified.py::_maybe_grow`)

Mechanism copied from `_certified_finite_step`; a complete drop-in
for the Adam loop at unified.py:423-433 (not yet run — a proposal):

```python
from hagi.lm import finite_displacement_ce_upper

def _certified_block_step(m, blk, Xo, yo, eta0, max_backtracks=12):
    """_certified_finite_step mechanism on the NEW block only (trunk
    frozen), certified on the fixed objective CE(Xo, yo). Returns the
    certified drop (> 1e-12 = COMMIT) or 0.0 (HOLD, exact rollback)."""
    import torch as t
    params = [blk["W1"], blk["b1"], blk["Wo"]]
    snap = [q.detach().clone() for q in params]
    with t.no_grad():
        z0 = m.logits(Xo).detach()
    g = t.autograd.grad(t.nn.functional.cross_entropy(m.logits(Xo), yo), params)
    direction = [gi.detach() for gi in g]
    A = float(sum(d.square().sum() for d in direction))
    if A <= 1e-24:
        return 0.0                                   # HOLD
    eta = eta0
    for _ in range(max_backtracks + 1):
        with t.no_grad():
            for q, old in zip(params, snap):
                q.copy_(old)
            for q, d in zip(params, direction):
                q.add_(eta * d)
            z1 = m.logits(Xo).detach()
        drop = -float(finite_displacement_ce_upper(z0, z1, yo))
        if drop > 1e-12:
            return drop                              # COMMIT
        eta *= 0.5
    with t.no_grad():
        for q, old in zip(params, snap):
            q.copy_(old)
    return 0.0                                       # HOLD
```

Caller, replacing `opt = ...; for _ in range(2): ...`:

```python
    # Xo, yo = batch(_np.arange(m.k, min(cut, m.k + 2048)))   # FIXED objective
    # ledger, holds, eta0 = {"commits": 0, "total_drop": 0.0}, 0, 3e-3
    # for _ in range(600):
    #     d = _certified_block_step(m, blk, Xo, yo, eta0)
    #     holds = holds + 1 if d == 0.0 else 0
    #     if d == 0.0 and holds >= 2: break
    #     ledger["commits"] += d > 0.0; ledger["total_drop"] += d
```

Required properties, each mapping to a theorem hypothesis:

1. `z0 = m.logits(Xo).detach()` before the trial move; `z1` after.
2. `upper = finite_displacement_ce_upper(z0, z1, yo)` (import from
   `hagi.lm`); `drop = -upper`.
3. `drop > 1e-12` → COMMIT (keep trial point, return `drop`); else
   `eta *= 0.5`; after 13 trials restore `snap` and return `0.0`.
4. `eta` proposal: the JVP variant needs a functional
   `logits_from_block_params`, which does NOT exist today
   (`_rope_logits_from_params` covers trunk params only, lm.py:806-824);
   the diff starts from `eta0 = 3e-3` and relies on backtracking
   (13 trials = factor down to 1/4096).
5. **Objective**: `(Xo, yo)` must be ONE FIXED training batch-set for the
   whole warm-up — e.g. the first 2048 windows of the 90 % train cut
   (deterministic positions, not `rng.choice`). Batches drawn per step
   from different minibatches give per-batch certificates that do NOT
   telescope (`batch_drop_not_global`; the code itself says so at lm.py:1002-1005).
   Batches resampled per step with `rng.choice` — the current loop —
   do NOT satisfy this.
6. **Loop**: replace the 2-epoch Adam loop by up to N certified steps
   (suggest N = 600, the current bound); stop early when a step HOLDs
   twice in a row (no progress possible along −∇). Return the ledger
   `{"steps", "commits", "total_drop", "obj_start", "obj_end"}`.
7. **Gate unchanged**: keep `after > before → m.blocks.pop()` (holdout).
   The theorem is about train-objective; the holdout gate stays a
   measured, unproven filter on top.

With 1–7, the executed warm-up is literally a `CertifiedFiniteStep`
trajectory with `obj = CE(Xo, yo)`, `θ` = block params, `n` = number
of steps; `h0` holds because `Wo = 0` at step 0 makes the block an
identity (C640/C642 anchors `function_preserving_growth`,
`lmLogits_grow_identity`) so `obj (θ 0) = fOld` on ANY batch.

## (d) What this gives (and what it costs)

Gives:

- obj ≤ fOld is now CERTIFIED, not hypothetical: C642 (`warmup_safe`)
  + C644 (`warmup_h1_of_certified_steps`) on the executed loop, for
  every verdict of the holdout gate.
- A real HOLD semantics: a step that cannot be certified leaves the
  parameters exactly where they were (snapshot restore) — no silent
  ascent as plain Adam can do.
- Ledger drop: the warm-up reports certified drops (sum ≥ 0) that the
  C642 telescope consumes.

Costs (structural, NOT measured in primes — see limits):

- Per trial: one forward on `(Xo, yo)` for `z1`, one for `z0` per step
  (reusable across trials), plus `finite_displacement_ce_upper` (one
  softmax, elementwise). With a JVP `eta` proposal: one extra JVP
  per step (`torch.autograd.functional.jvp`) — the JVP is only a
  step-size heuristic; backtracking alone is sound, so the JVP can be
  skipped at the price of more halving trials.
- Objective must be the fixed `(Xo, yo)` each step; a larger fixed
  set costs proportionally more forward compute per step.

## (e) Validation criterion (loop-5 style)

On every warm-up step log `real_drop = obj_before − obj_after` (float64
re-evaluated on `(Xo, yo)`) next to the returned `drop`. Accept the port iff:

- `real_drop ≥ drop − 1e-6` on EVERY step of a full run;
- HOLD steps leave params bit-identical (`torch.equal` before/after);
- `obj_end ≤ obj_start` for the whole warm-up on every `_maybe_grow`
  call (train objective), independently of the holdout verdict;
- holdout verdict distribution and grow rate reported (expected to
  shift — report honestly, no target).

## (f) Honest limits

- (1) Float soundness: the range lemma is exact-arithmetic; the code
  evaluates it in float32. The validation loop (e) is the runtime
  soundness check — exactly as for the existing `_certified_finite_step`.
- (2) `eta` proposal: the JVP route needs a functional logits-over-
  block-params; absent today, the diff falls back to backtracking from a
  fixed initial `eta`. The theorem is indifferent (it only reads the
  COMMIT/HOLD exits).
- (3) Single objective: the certificate is on `CE(Xo, yo)` only. No
  claim about the full train distribution, holdout, or other batches
  (`batch_drop_not_global`). fOld itself is the same objective at step 0.
- (4) Growth of the FUNCTION is not preserved after step 0 (C640
  verdict unchanged): the theorem bounds train-objective, not function
  distance.
- (5) Holdout gate stays a measured branch — ACCEPT is not a theorem.
- (6) Plain Adam often descends faster per wall-clock than a
  certified step; the proposal trades speed for a proof obligation.
  Whether growth still happens often enough under certified steps is an
  EMPIRICAL question for the HAGI_v2 agent (validation (e)).
- (7) Anchors are frozen in primes; re-verify before port.
