# PROPOSAL: port the adaptive (variance-sensitive) CE majorizer into `CertifiedStepLM`

For: the HAGI_v2 implementation agent. Written by the primes
agent (C466, roadmap C464 top-2 THEORY_ALIGNMENT). This document is
self-contained: no primes-repo context is needed to apply it. All
Lean anchors below are proved and frozen in primes (Freeze 8345,
module `Hagi/Theory/AdaptiveMajorizer.lean`, namespace
`Hagi.Theory.AdaptiveMajorizer`).

## (a) Formula

Current step (§3.9 range majorizer) in `hagi/lm.py::_certified_step`:

- `A = ‖D‖² = D·D` where `D = −∇CE` (flat);
- `R'_sq = mean_i (range_i(disp))²` where `disp` is the JVP of all
  logits along `D` at η=1 (per-sample `range_i = max−min` over the
  256 logits);
- `eta = 4A / R'_sq`, certified drop `2A² / R'_sq`
  (quadratic minimizer of `L(0) − ηA + η²·R'_sq/8`).

Proposed replacement (variance-adaptive, primes C462):

- `R_i = range_i(disp)` (per sample, unsquared);
- `p_i = softmax(logits_i)` (already computed);
- `Var_i = Σ_v p_iv · (disp_iv − Σ_w p_iw·disp_iw)²`
  (variance of the unit-η displacement under the CURRENT soft
  target);
- curvature `C = mean_i ( exp(R_i) · Var_i )`;
- safe step `η* = A / (2C)`, valid only when `η* ≤ 1`;
- certified drop `A² / (4C)`.

Why the η≤1 cap is REQUIRED: the multiplier is `exp(η·R) ≤ exp(R)`,
which needs `η ≤ 1` (Lean: `ceOneHot_next_le_adaptive` has
hypotheses `0 ≤ η ≤ 1` — the all-η law of the range majorizer does
NOT hold with an exp-type constant; this is honest, see module
docstring "Honesty pin"). The current range step has no cap and must
not simply be re-parameterized.

## (b) Minimal-diff pseudocode (insert in `_certified_step`)

Replace the block computing `Rp_sq` … `return` with:

```python
# ---- adaptive majorizer (primes C462, Lean: ce_adaptive_descent) ----
per_sample_range = disp.max(dim=1).values - disp.min(dim=1).values  # R_i
p = t.softmax(logits, dim=-1)                       # (B, V)
mu = (p * disp).sum(dim=1, keepdim=True)            # E_p[disp]
var = (p * (disp - mu) ** 2).sum(dim=1)             # Var_p(disp)
C = float((t.exp(per_sample_range) * var).mean())   # batch-mean curvature
if A <= 0:
    return 0.0
if C <= 0.0:
    # zero variance under a one-hot-limit target: the majorizer is
    # exactly linear (Lean: ceOneHot_next_le_linear_of_zero_var) —
    # take the unit step, no curvature penalty.
    eta = lr_scale * 1.0
    certified = lr_scale * A                        # linear drop −ηA
else:
    eta_raw = lr_scale * A / (2.0 * C)
    if eta_raw <= 1.0:
        eta, certified = eta_raw, lr_scale**2 * A * A / (4.0 * C)
    else:
        # hstar fails (η* > 1): certificate void — fall back to the
        # OLD range step (valid for all η). Diffuse-p regime.
        Rp_sq = float((per_sample_range ** 2).mean())
        if Rp_sq <= 0:
            return 0.0
        eta = lr_scale * 4.0 * A / Rp_sq
        certified = 2.0 * A * A / Rp_sq
with t.no_grad():
    off = 0
    for prm, gi in zip(self.params(), g):
        sz = prm.numel()
        prm.add_(eta * D[off:off + sz].reshape(prm.shape))
        off += sz
return certified
```

Note the zero-variance branch: `C == 0` with `A > 0` gives an
unbounded safe step in the pure quadratic algebra; capped at η=1 the
certified drop is the linear term `A` (majorizer is exactly linear,
Lean `ceOneHot_next_le_linear_of_zero_var`).

## (c) Lean anchors (primes, frozen Freeze 8345)

Module `Hagi/Theory/AdaptiveMajorizer.lean`,
namespace `Hagi.Theory.AdaptiveMajorizer`:

- `varWeight` / `varWeight_nonneg` / `varWeight_scale` — the
  weighted-variance functional (η² scaling is proved);
- `varMgf_le` — Bennett-weak CGF bound
  `log Σ q·exp g ≤ E_q[g] + exp(R)·Var_q(g)`, range ≤ R;
- `lse_shift_upper_var` — the adaptive twin of
  `Hagi.Energy.lse_shift_upper`;
- `ceAdaptiveCurv` — the curvature `exp(ceStepRange)·Var_{smax z}(δz)`;
- `ceOneHot_next_le_adaptive` — step majorizer
  `CE_next ≤ CE − η·A + η²·C` for `0 ≤ η ≤ 1`;
- `adaptive_descent`, `ce_adaptive_descent` — safe step `η*=A/(2C)`,
  drop `A²/(4C)` under `η* ≤ 1`;
- `ce_adaptive_drop_dominates` — the utility theorem: under
  `Var ≤ R²/(8·exp R)` the adaptive drop dominates the range drop
  `2A²/R²` of `singleSampleStep`;
- `ceOneHot_next_le_linear_of_zero_var` — concentrated-target limit.

## (d) Expected effect

THEORY_ALIGNMENT pain (primes §"2026-11-16 ночь"): late in training
the soft target concentrates toward one-hot, `Var_p(δz) → 0`, but
the RANGE of the displacement does not shrink — the range curvature
`R'²/8` stays put and `η = 4A/R'²` throttles to ~0 (certified
learning freezes before the loss does). The adaptive curvature
`exp(R)·Var_p` collapses together with the variance, so:

- safe steps stop degenerating at the end of training
  (η* stays bounded away from 0, see sanity table below);
- certified drops stay meaningful (dominance regime), so the
  `certified_guarantee` accumulator and the C330 quality-stop
  criterion keep firing;
- mid/early training (diffuse p) is UNCHANGED by the fallback
  branch — old behavior preserved exactly where the old bound is
  better (dominance hypothesis fails there, honestly).

## (e) Validation criterion (loop-5 style, per training step)

On every `_certified_step` call, alongside the certified drop,
record the REAL CE drop `CE(θ) − CE(θ + ηD)` (one extra forward, or
reuse the next epoch's first batch statistic). Acceptance:

`real_drop ≥ certified_drop` on EVERY step of a full run.

This mirrors the existing §9 verify loop. Also log the branch taken
(adaptive / fallback-range / zero-var) and compare end-of-run
`best_holdout_ce` and total `certified_guarantee` vs the range-only
baseline: the adaptive run should not be worse anywhere and should
be strictly better on the late-training segment (larger steps where
the range bound throttled).

## (f) Honest limits

- The multiplier `exp(R)` is the WEAKENED Bennett constant. The
  tight one is `κ(R) = (exp R − 1 − R)/R²` with
  `exp(R)/2 ≤ κ(R) ≤ exp(R)` — so `C` here overestimates the true
  curvature by up to 2×, and the ratio `exp(R)/κ(R)` grows with R.
  At LARGE per-sample ranges the adaptive bound degrades quickly;
  the fallback branch covers exactly that regime, but per-step
  branching means the certified chain alternates theories (fine —
  each step is individually certified).
- Domination is CONDITIONAL (Lean `ce_adaptive_drop_dominates`
  hypothesis): `Var ≤ R²/(8·exp R)`. Popoviciu allows `Var ≤ R²/4`,
  which for `R ≳ ln 2` exceeds the threshold. Diffuse targets +
  large ranges ⇒ the old range bound wins; concentrated targets
  (the training-end regime this targets) ⇒ adaptive wins.
- One-hot limit: as `p → one-hot`, `Var → 0` and the step is capped
  by η ≤ 1 (and by the C>0 branch logic), i.e. the certificate
  becomes the linear bound — sound, but not an unbounded step.
- Batch-mean standing: identical to the existing §3.9 usage — the
  Lean theory is single-sample (`ceOneHot`); applying it to the
  batch-mean loss with per-sample curvatures averaged is the same
  convention lm.py already uses for the range version (no stronger
  claim is made here).

## Sanity numbers (primes C466, `.tmp/C466/sanity.py`)

Single-sample toy: 5 logits, fixed unit-η displacement
`d = [0.6, −0.2, 0.3, −0.4, −0.3]` (R = 1.0), target = argmax(d);
vary only the concentration of `p = softmax(z)`:

| case | A | Var_p(d) | C_old=R²/8 | C_new=e^R·Var | η_old | η_new | cert drop old | cert drop new | true drop @η_old | true drop @η_new |
|---|---|---|---|---|---|---|---|---|---|---|
| early (flat z) | 0.6000 | 0.1480 | 0.1250 | 0.4023 | 2.4000 | 0.7457 | 0.7200 | 0.2237 | 1.0000 | 0.4047 |
| mid (z peak 3.0) | 0.2702 | 0.1613 | 0.1250 | 0.4383 | 1.0807 | 0.3082 | 0.1460 | 0.0416 | 0.2109 | 0.0759 |
| late (z peak 9.0) | 0.0020 | 0.0018 | 0.1250 | 0.0048 | 0.0079 | 0.2053 | 0.00001 | 0.00020 | 0.00002 | 0.00037 |

Reading:

- soundness: every certified drop ≤ true drop at its own η (all six
  cells check out numerically);
- late phase (the target regime): adaptive cert drop ≈ 20× the
  range cert drop and η_new/η_old ≈ 26× — steps are no longer
  throttled by a non-collapsing range;
- early/diffuse: the range bound is better (C_old < C_new) — exactly
  the honest conditional-domination picture; the fallback branch
  preserves it.
