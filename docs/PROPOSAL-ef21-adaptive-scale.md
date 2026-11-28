# PROPOSAL: adaptive scale for the ternary EF21 step

**Status: `PROPOSAL-index.md` (single source of truth).**

For: the HAGI_v2 implementation agent. Module
`Hagi/Optimization/EF21Scale.lean`. Self-contained. All Lean anchors are
proved and frozen in primes; primes does not edit HAGI_v2 code.

**Changed algorithm: YES — one line.** The ternary scale of `_ef21_step`
is recomputed per step instead of being frozen at step 1.

## Context

`hagi/models/lm.py::_ef21_step` (lm.py:1623–1632) freezes
`s* = 0.2·max|m|` at the first call and reuses it for the whole
trajectory. `qTern` keeps only coordinates with `|m i| > s/2`.

## What is proved

- `qTernVec_inner` (Hagi/Optimization/EF21Scale.lean:59): the alignment
  `A = Σ m i · d i` that drives `η = 4A/R'²` equals
  `s · Σ_{|m i| > s/2} |m i|` exactly.
- `qTernVec_freeze` (EF21Scale.lean:90): with `‖m‖_∞ < s/2` the direction is
  zero and `A = 0` — the step is rejected (`A <= 0` branch, lm.py:1642) after
  paying forward + JVP. A frozen `s*` reaches this state whenever the
  gradient norm falls below `s*/2` — i.e. near convergence.
- `qTernVec_inner_ge_adaptive` (EF21Scale.lean:96): with
  `s = ‖m‖_∞/2` the alignment is at least
  `‖m‖_∞/2 · ‖m‖₁ − n·‖m‖_∞²/8` at any gradient level; the kept mass is
  never below `1 − n‖u‖_∞/(4‖u‖₁)` of `‖u‖₁`.
- `qTernVec_certifiedDrop_ge` (EF21Scale.lean:114): the certified drop
  `2A²/R'²` is bounded below by `2·A_min²/R'²` with that `A_min`.

Literature (ask.sciencemadereadable): an optimum-scaled uniform quantizer is
within 0.013 dB of the Lloyd–Max quantizer for Gaussian errors
(Douglas–Meng 1991); steady-state error of quantized LMS is linear in the
scale (Eweda 1992) — the scale must track the signal.

## Minimal diff

```python
# lm.py:1626-1628
-        if self._ef21_s is None:
-            mi_all = t.cat([mi.reshape(-1) for mi in m])
-            self._ef21_s = 0.2 * float(mi_all.abs().max())
+        mi_all = t.cat([mi.reshape(-1) for mi in m])
+        s_max = float(mi_all.abs().max())
+        self._ef21_s = max(s_max / 2.0, 1e-12)   # adaptive: s = ‖m‖_∞/2
```

Telemetry (log every step): `zero_frac = mean(d == 0)`, `s_max`, `A`.

## Validation

- `zero_frac` at the end of training: frozen scale → grows toward 1;
  adaptive → stays `≤ n·s_max/(4‖m‖₁)` (typically 0.1–0.3).
- Accepted-step count strictly increases; `real ≥ certified` drop on every
  accepted step (existing check).
- `holdout` CE unchanged or better; no change in `.hqz` size.

## Limits

The certificate is about the alignment term only: the step is still accepted
only by the measured JVP range (`R'²`) and the exact backtracking. Nothing is
claimed about convergence speed or generalization.
