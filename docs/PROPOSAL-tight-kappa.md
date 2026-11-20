# PROPOSAL: tight Bennett-κ update of the adaptive CE majorizer in `CertifiedStepLM`

For: the HAGI_v2 implementation agent. Written by the primes agent
(C480; theory landed in primes C471). SUPERSEDES the multiplier of
`docs/PROPOSAL-adaptive-majorizer.md` (C466) — everything else in
C466 (η≤1 cap, fallback branches, zero-variance branch, validation
loop) carries over unchanged. Self-contained: no primes-repo
context needed. All Lean anchors are proved and frozen in primes
(Freeze 8462, module `Hagi/Theory/AdaptiveMajorizer.lean`, namespace
`Hagi.Theory.AdaptiveMajorizer`).

## (a) Context (one line)

Current: C466 proposes curvature `C = e^R · Var_p(δz)` with the
WEAKENED Bennett multiplier `e^R`; primes C471 proved the TIGHT
multiplier family, so the C466 curvature overestimates by the
factor `e^R / κ(R)` — 2.77× at R=0.5, 3.79× at R=1, 6.73× at R=2 —
for free.

## (b) Formulas and Lean anchors (primes, Freeze 8462)

Tight Bennett constant and its laws (all in
`Hagi.Theory.AdaptiveMajorizer`):

- `kappa R = (Real.exp R - 1 - R) / R ^ 2` — the definition;
- `kappa_mono` — κ is nondecreasing on (0, ∞);
- `kappa_ge_half` — `1/2 ≤ κ R` for `R > 0`;
- `kappa_le_expR` — `κ R ≤ e^R` (comparison theorem: the tight
  multiplier always dominates-loses to the C466 one).

Tight majorizer family (C471):

- `varMgf_le_tight` — tight CGF bound
  `log Σ q·exp g ≤ E_q[g] + κ(R)·Var_q(g)` (range ≤ R);
- `lse_shift_upper_var_tight` — tight twin of
  `lse_shift_upper_var`;
- `ceAdaptiveCurvTight` — curvature `C_tight = κ(R) · Var_p(δz)`
  with `R = ceStepRange`, `p = softmax(logits)`;
- `ceOneHot_next_le_adaptive_tight` — step majorizer
  `CE_next ≤ CE − η·A + η²·C_tight` for `0 ≤ η ≤ 1` (cap still
  mandatory — `kappa_mono` replaces exp-monotonicity, the all-η
  law still does NOT hold);
- `ce_adaptive_descent_tight` — safe step `η* = A/(2·C_tight)`,
  certified drop `A²/(4·C_tight)` under `C_tight > 0, A ≥ 0,
  A/(2·C_tight) ≤ 1`;
- `ce_adaptive_curv_le_range_tight` — dominance premise
  `Var ≤ R²/(8·κ R)`: WEAKER than the C466 premise `R²/(8·e^R)`
  (since `kappa_le_expR`), so the tight version dominates on a
  STRICTLY LARGER regime;
- `ce_adaptive_drop_dominates_tight` — utility theorem: the tight
  adaptive drop dominates the range drop `2A²/R²`;
- `ceOneHot_next_le_linear_of_zero_var_tight` — zero-variance
  linear law (unchanged semantics).

Replacement rule (drop-in for the C466 diff):

```
C_weak  = exp(R) · Var_p(δz)        # C466 — obsolete
C_tight = kappa(R) · Var_p(δz)      # C471 — this proposal
kappa(R) = (exp(R) - 1 - R) / R**2  # math.exp, R > 0
```

Win factors (curvature deflation = certified-drop inflation,
exactly `e^R/κ(R)` on the η*≤1 branch):

| R    | e^R     | κ(R)   | e^R/κ(R) |
|------|---------|--------|----------|
| 0.5  | 1.6487  | 0.5949 | 2.77×    |
| 1.0  | 2.7183  | 0.7183 | 3.79×    |
| 2.0  | 7.3891  | 1.0973 | 6.73×    |

## (c) Minimal Python diff (in `hagi/lm.py::_certified_step`)

Replace only the curvature line of the C466 patch (everything
else — η≤1 cap, `A ≤ 0` / `C ≤ 0` branches, fallback to the range
step when `η* > 1` — stays as in C466):

```python
# ---- tight kappa curvature (primes C471) ----
per_sample_range = disp.max(dim=1).values - disp.min(dim=1).values  # R_i
R = float(per_sample_range.max())                  # worst-case per batch
                                                 # (or per-sample, see limits)
def kappa(r: float) -> float:                     # tight Bennett constant
    return (math.exp(r) - 1.0 - r) / (r * r) if r > 0 else 0.5
p = t.softmax(logits, dim=-1)
mu = (p * disp).sum(dim=1, keepdim=True)
var = (p * (disp - mu) ** 2).sum(dim=1)
C = float((kappa(per_sample_range.clamp(min=1e-12)) * var).mean())  # was: exp(R)*var
# then IDENTICALLY to C466: A<=0 -> 0.0; C<=0 -> linear unit step;
# eta_raw = lr_scale * A / (2*C); eta_raw <= 1 -> (eta_raw, A^2/(4C));
# else fallback to the old range step eta = 4A/Rp_sq (valid for all eta).
```

(`math.exp` per the task spec; `r → 0` limit of κ is 1/2 — guard
against division by zero as shown.)

## (d) Sanity numbers (primes C480, `.tmp/C480/sanity-tight-kappa.py`)

Header table reproduced above (script re-verifies `1/2 ≤ κ ≤ e^R`
and monotonicity on (0,4]). Toy single-sample step, 5 flat logits,
displacement `d = [1.4, −0.6, 0.4, −0.6, −0.6]` (R = 2.0), target =
argmax — R chosen so the TIGHT safe step respects the mandatory
η ≤ 1 cap:

| version | C      | η*     | certified drop | real drop | sound (real ≥ cert) |
|---------|--------|--------|----------------|-----------|---------------------|
| weak e^R  (C466) | 4.7290 | 0.1480 | 0.1036 | 0.4072 | yes |
| tight κ   (C471) | 0.7023 | 0.9968 | 0.6978 | 2.4297 | yes |

Certified-drop gain = 6.73× = exactly `e^R/κ(R)`; step-size gain
the same factor. Both branches are individually certified.

## (e) Validation criterion (unchanged from C466, loop-5 style)

On every `_certified_step` call record the REAL CE drop
`CE(θ) − CE(θ + ηD)` next to the certified drop. Accept:
`real_drop ≥ certified_drop` on EVERY step of a full run. Log the
branch taken (tight / fallback-range / zero-var); the tight run
must be no worse than the weak-adaptive run everywhere and
strictly better whenever the tight branch fires with η* ≤ 1
(guaranteed factor `e^R/κ(R) ≥ 1` by `kappa_le_expR`).

## (f) Honest limits

- The η ≤ 1 cap is STILL REQUIRED (`ceOneHot_next_le_adaptive_tight`
  hypotheses `0 ≤ η ≤ 1`); the fallback-range branch stays.
- R must be > 0 for `kappa`; at R → 0 use the limit 1/2 (κ is
  continuous with κ(0)=1/2 by `kappa_ge_half` + monotone limit);
  the code guard handles it.
- Per-sample κ vs batch worst-case R: the Lean theory is
  single-sample; the pseudocode uses per-sample `κ(R_i)` (matches
  the existing batch-mean convention of §3.9, same as C466 claimed
  for `e^{R_i}` — no stronger claim).
- Domination is still CONDITIONAL, but on the weaker premise
  `Var ≤ R²/(8 κ R)` (`ce_adaptive_curv_le_range_tight`); diffuse
  targets still fall back to the range step.
- `kappa` is `noncomputable def` in Lean — it is a real-analysis
  object; the Python `math.exp` implementation is the runtime
  instantiation (Float, not exact — the validation loop (e) is the
  soundness check, as in C466).
