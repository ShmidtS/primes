# PROPOSAL: tight Bennett-κ update of the adaptive CE majorizer in `CertifiedStepLM`

For: the HAGI_v2 implementation agent. Self-contained: no primes-repo
context needed. All Lean anchors are proved and frozen in primes
(module `Hagi/Theory/AdaptiveMajorizer.lean`, namespace
`Hagi.Theory.AdaptiveMajorizer`).

It replaces coefficient-for-coefficient the weaker curvature
`e^R · Var_p(δz)` (multiplier `e^R`) by the tight one; the weaker
version overestimates curvature by `e^R / κ(R)` — 2.77× at R=0.5,
3.79× at R=1, 6.73× at R=2. The η≤1 cap, fallback branches,
zero-variance branch and validation loop are unchanged.

## (a) Formulas and Lean anchors

Tight Bennett constant and its laws (all in
`Hagi.Theory.AdaptiveMajorizer`):

- `kappa R = (Real.exp R - 1 - R) / R ^ 2` — the definition;
- `kappa_mono` — κ is nondecreasing on (0, ∞);
- `kappa_ge_half` — `1/2 ≤ κ R` for `R > 0`;
- `kappa_le_expR` — `κ R ≤ e^R` (the tight multiplier never exceeds
  the weak one).

Tight majorizer family:

- `varMgf_le_tight` — tight CGF bound
  `log Σ q·exp g ≤ E_q[g] + κ(R)·Var_q(g)` (range ≤ R);
- `lse_shift_upper_var_tight` — tight twin of `lse_shift_upper_var`;
- `ceAdaptiveCurvTight` — curvature `C_tight = κ(R) · Var_p(δz)`
  with `R = ceStepRange`, `p = softmax(logits)`;
- `ceOneHot_next_le_adaptive_tight` — step majorizer
  `CE_next ≤ CE − η·A + η²·C_tight` for `0 ≤ η ≤ 1` (the cap is
  still mandatory — `kappa_mono` replaces exp-monotonicity, the
  all-η law still does NOT hold);
- `ce_adaptive_descent_tight` — safe step `η* = A/(2·C_tight)`,
  certified drop `A²/(4·C_tight)` under `C_tight > 0, A ≥ 0,
  A/(2·C_tight) ≤ 1`;
- `ce_adaptive_curv_le_range_tight` — dominance premise
  `Var ≤ R²/(8·κ R)`: WEAKER than the weak premise `R²/(8·e^R)`
  (since `kappa_le_expR`), so the tight version dominates on a
  STRICTLY LARGER regime;
- `ce_adaptive_drop_dominates_tight` — the tight adaptive drop
  dominates the range drop `2A²/R²`;
- `ceOneHot_next_le_linear_of_zero_var_tight` — zero-variance
  linear law (unchanged semantics).

Replacement rule (drop-in):

```
C_weak  = exp(R) · Var_p(δz)        # obsolete
C_tight = kappa(R) · Var_p(δz)      # this proposal
kappa(R) = (exp(R) - 1 - R) / R**2  # math.exp, R > 0
```

Win factors (curvature deflation = certified-drop inflation, exactly
`e^R/κ(R)` on the η*≤1 branch):

| R    | e^R     | κ(R)   | e^R/κ(R) |
|------|---------|--------|----------|
| 0.5  | 1.6487  | 0.5949 | 2.77×    |
| 1.0  | 2.7183  | 0.7183 | 3.79×    |
| 2.0  | 7.3891  | 1.0973 | 6.73×    |

## (b) Minimal Python diff (in `hagi/lm.py::_certified_step`)

Replace only the curvature line of the patch (everything else — η≤1
cap, `A ≤ 0` / `C ≤ 0` branches, fallback to the range step when
`η* > 1` — stays):

```python
per_sample_range = disp.max(dim=1).values - disp.min(dim=1).values  # R_i
R = float(per_sample_range.max())                  # worst-case per batch
                                                 # (or per-sample, see limits)
def kappa(r: float) -> float:                     # tight Bennett constant
    return (math.exp(r) - 1.0 - r) / (r * r) if r > 0 else 0.5
p = t.softmax(logits, dim=-1)
mu = (p * disp).sum(dim=1, keepdim=True)
var = (p * (disp - mu) ** 2).sum(dim=1)
C = float((kappa(per_sample_range.clamp(min=1e-12)) * var).mean())  # was: exp(R)*var
# then IDENTICALLY: A<=0 -> 0.0; C<=0 -> linear unit step;
# eta_raw = lr_scale * A / (2*C); eta_raw <= 1 -> (eta_raw, A^2/(4C));
# else fallback to the old range step eta = 4A/Rp_sq (valid for all eta).
```

(`math.exp` per the task spec; `r → 0` limit of κ is 1/2 — guard
against division by zero as shown.)

## (c) Sanity numbers

Header table above (the check re-verifies `1/2 ≤ κ ≤ e^R` and
monotonicity on (0,4]). Toy single-sample step, 5 flat logits,
displacement `d = [1.4, −0.6, 0.4, −0.6, −0.6]` (R = 2.0), target =
argmax — R chosen so the TIGHT safe step respects the mandatory
η ≤ 1 cap:

| version | C      | η*     | certified drop | real drop | sound (real ≥ cert) |
|---------|--------|--------|----------------|-----------|---------------------|
| weak e^R  | 4.7290 | 0.1480 | 0.1036 | 0.4072 | yes |
| tight κ   | 0.7023 | 0.9968 | 0.6978 | 2.4297 | yes |

Certified-drop gain = 6.73× = exactly `e^R/κ(R)`; step-size gain the
same factor. Both branches are individually certified.

## (d) Validation criterion

On every `_certified_step` call record the REAL CE drop
`CE(θ) − CE(θ + ηD)` next to the certified drop. Accept:
`real_drop ≥ certified_drop` on EVERY step of a full run. Log the
branch taken (tight / fallback-range / zero-var); the tight run must
be no worse than the weak-adaptive run everywhere and strictly
better whenever the tight branch fires with η* ≤ 1 (guaranteed factor
`e^R/κ(R) ≥ 1` by `kappa_le_expR`).

## (e) Limits

- The η ≤ 1 cap is STILL REQUIRED (`ceOneHot_next_le_adaptive_tight`
  hypotheses `0 ≤ η ≤ 1`); the fallback-range branch stays.
- R must be > 0 for `kappa`; at R → 0 use the limit 1/2 (κ is
  continuous with κ(0)=1/2 by `kappa_ge_half` + monotone limit);
  the code guard handles it.
- Per-sample κ vs batch worst-case R: the Lean theory is
  single-sample; the pseudocode uses per-sample `κ(R_i)` (matches
  the existing batch-mean convention of ALGORITHMS §3.9 — no
  stronger claim).
- Domination is still CONDITIONAL, but on the weaker premise
  `Var ≤ R²/(8 κ R)` (`ce_adaptive_curv_le_range_tight`); diffuse
  targets still fall back to the range step.
- `kappa` is `noncomputable def` in Lean — a real-analysis object;
  the Python `math.exp` implementation is the runtime instantiation
  (Float, not exact — the validation loop (d) is the soundness
  check).
- Anchors are frozen in primes; re-verify before port.
