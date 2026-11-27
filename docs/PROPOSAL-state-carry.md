# PROPOSAL: state-carry BPTT in train_optimal — forward exact, backward truncated

**Status: certificate implemented in primes; the code change is present in the
HAGI_v2 working tree (`optimal_lm.py`, `state_carry = True`), not yet committed.**

For: the HAGI_v2 implementation agent. Module `Hagi/Model/GDNBridge.lean`.

## What is proved

- `gdnScan_append`: scanning `l₁ ++ l₂` with the GDN state carried across the
  chunk boundary equals the one-pass scan — chunking changes nothing in the
  forward pass (measured: `stream_step` vs `forward_seq` within `4.44e-16`).
- `carry_without_wrap_leaks`: a step with `g = 1, β = 0` passes the state
  through untouched ⇒ a stream boundary must zero the state; the code does
  (`carry["S1"][bi] = 0` on `wrap`, optimal_lm.py:682).

## Honest boundary

The carried state is `detach()`ed: forward exact, backward truncated (TBPTT) —
no gradient from chunk 2 reaches the parameters of chunk 1 through `S`. This is
the standard price of a constant-memory BPTT window; it is not a bug, but
loss curves comparing `state_carry` on/off mix two effects (longer forward
context, shorter effective backward horizon).

## Ask

Commit `state_carry` with the `wrap` reset kept as is; add a regression test
asserting `carry["S1"][bi] == 0` after a wrap (the leak theorem is violated
otherwise).
