# PROPOSAL: measured (δ-gated) expert merge for the MDL-prune loop

For: the HAGI_v2 implementation agent. Self-contained. All Lean
anchors are proved and frozen in primes (module
`Hagi/Theory/MergeQuant.lean`, namespace `Hagi.Theory.NonlinearMerge`).

## (a) Context

HAGI_v2 MDL-prune merges experts through a purely quadratic gate
(primes twin: `Hagi.Ensemble.MergePrice`,
`MergeApproved` / `merge_gate_certified` with `sigmaPrice`) which
has NO residual term — sound only for the quadratic loss model. The
measured (δ-gated) version holds for ARBITRARY nonlinear merge
losses; a NEGATIVE theorem shows the unmeasured gate is unsafe.

## (b) Formulas and Lean anchors

Measured-residual machinery (`Hagi.Theory.NonlinearMerge`):

- `interp w1 w2 t = w1 + t·(w2 − w1)`, `mid = (w1+w2)/2`, `linAt` —
  first-order linearization of L at w₁ along the path;
- `linResidualGrid L g w1 w2 ts` — the MEASURED linearization
  residual on a finite grid of t-points:
  `∑_t |L(w_t) − L_lin(w_t)|` (procedure: pick rational t-points,
  evaluate L and the linearization, sum the abs deviations);
  `linResidualGrid_nonneg`, `linResidualGrid_point_le` (each grid
  point's deviation ≤ the sum);
- `nonlinear_merge_bound` — MAIN: two measured residuals
  (δ at t=1/2, δ₂ at t=1) give, for ANY L (no convexity, no
  linearity): `L(mid) ≤ ½(L(w1) + L(w2)) + δ + δ₂/2`;
- quadratic twin (when the loss IS the quadratic model):
  `quadLossDiag / quadGradDiag / curvRemainder`,
  `quad_merge_exact` (exact identity), `quad_merge_le_mean`,
  `quad_residual_mid`, `curvRemainder_le_path`;
- measured gate — `MergeApprovedMeas twoGap prices w δ_bound κ s n'`:
  `(∑_i w_i·prices_i) + δ_bound + κ·(n'·s)/2 < twoGap`;
  certificate `merge_gate_meas` (defeq unwrap);
- NEGATIVE: `merge_unsafe_without_measurement` — for every B > 0
  there is a 1D loss with `L(w1) = L(w2) = 0` but
  `L(mid) ≥ B` (concave parabola `B − 4B(x−½)²`): any merge bound
  MUST carry a residual δ ≥ B; the δ-free
  `Hagi.Ensemble.MergePrice.merge_gate_certified` is exactly the
  quadratic-model case (its `MergeApproved` has no δ-term — the
  forms are distinct).

Replacement: in the MDL-prune merge decision, substitute
`MergeApprovedMeas` for the δ-free gate: keep the price sum
(σ-metric per domain) and the ternary compression term κ·n'·s/2,
ADD the measured δ_bound from the `linResidualGrid` procedure.

## (c) Minimal Python diff

```python
def merge_gate_measured(self, w1, w2, prices, w, two_gap, kappa, s, n_prime):
    # ---- linResidualGrid: finite rational t-grid ----
    ts = [F(1,4), F(1,2), F(3,4), F(1)]         # rational grid points
    g1 = grad(self.loss, w1)                     # linearization at w1
    L1 = self.loss(w1)
    delta = 0.0
    for t in ts:
        wt = w1 + t * (w2 - w1)                  # interp
        lin = L1 + t * dot(g1, w2 - w1)          # linAt
        delta += abs(self.loss(wt) - lin)        # sum of abs deviations
    delta_bound = delta                          # linResidualGrid value
    # ---- measured gate (MergeApprovedMeas) ----
    lhs = sum(wi * pi for wi, pi in zip(w, prices)) \
        + delta_bound + kappa * (n_prime * s) / 2.0
    return lhs < two_gap, lhs                    # True => merge certified BY MEASUREMENT
```

## (d) Sanity numbers

Exact-rational (Fraction) 1D losses, experts w1 = 0, w2 = 1:

- Convex `L(w) = (3/2)(w−1)²`: grid t ∈ {1/4, 1/2, 3/4, 1} gives
  `linResidualGrid = 45/16 = 2.8125`; point domination
  (|resid(1/2)|, |resid(1)| ≤ grid) holds;
  `nonlinear_merge_bound`: L(mid) = 0.375 ≤ (L1+L2)/2 + δ + δ₂/2
  = 1.875 (True);
  δ-gate PASS: prices 1/8 + 1/8 + δ_bound(=|resid(1/2)| = 3/8) =
  0.625 < twoGap = 1 (merge certified);
- NEGATIVE (concave `B − 4B(x−½)²`, B = 1): ends are BOTH zero,
  mid = barrier 1 — the unmeasured gate would approve (prices 0)
  and lose 1.0; the measured residual |resid(1/2)| = 1 ≥ B fires
  exactly as `merge_unsafe_without_measurement` demands.

## (e) Validation criterion

Per merge candidate in the MDL-prune loop: run the grid
measurement (4 loss evaluations at rational t-points — cheap, no
gradients beyond g1), then require BOTH (i) the δ-gate
`Σprice + δ_bound + κ·n'·s/2 < twoGap` and (ii) the realized merge
loss change `L(mid) − min(L(w1),L(w2))` measured post-hoc ≤
`½|L(w1) − L(w2)| + δ + δ₂/2` on every executed merge of a full
prune cycle. Log rejected-by-δ candidates separately from
rejected-by-price: δ-rejections are the nonlinear-loss rescue that
the old gate silently ignored.

## (f) Limits

- The grid is FINITE: `linResidualGrid` bounds deviations only AT
  the sampled t-points; between grid points the residual can exceed
  δ_bound (the Lean object is the grid sum, no interpolation claim
  — `linResidualGrid_point_le` is pointwise on the grid only).
  Dense-enough grids are the runtime's responsibility; the (e)
  post-hoc check is the backstop.
- Extra cost: |ts| extra loss evaluations + one gradient per merge
  candidate (vs 0 for the δ-free gate) — fine for MDL-prune
  cadence, not for per-step use.
- The quadratic twin (`quad_merge_exact` etc.) is the degenerate
  case: when the loss IS the quadratic model, δ collapses to the
  computable `curvRemainder` (`quad_residual_mid`) and the gate
  degrades gracefully toward `merge_gate_certified` — no
  double-pay, but no rescue either.
- twoGap, prices are measured quantities (ensemble gap law,
  σ-metric) — the gate is only as good as those measurements; the
  Lean certificate composes them, it does not re-derive them.
- Anchors are frozen in primes; re-verify before port.
