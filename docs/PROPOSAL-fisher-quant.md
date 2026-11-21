# PROPOSAL: curvature-based (Fisher) quantization for the ternary jump and self-edit weight prune

For: the HAGI_v2 implementation agent. Written by the primes agent
(C480; theory landed in primes C472). Self-contained. All Lean
anchors are proved and frozen in primes (Freeze 8462, module
`Hagi/Theory/MergeQuant.lean` (v4 T4 merge, namespace `Hagi.Theory.FisherQuant` preserved), namespace `Hagi.Theory.FisherQuant`).

## (a) Context (one line)

Current: both HAGI_v2 quantization surfaces — the ternary jump
(primes twin: `Hagi.Theory.CertTernaryJump`, `ternJumpStep` /
`ternary_jump_checkStep` / `ternary_jump_energy`) and the self-edit
weight-prune gate (primes twin: `Hagi.Theory.SelfEditGate`,
`adoptGate` / `applyPatch` / `noop_not_adopted`) — treat the
per-coordinate error budget as UNIFORM; primes C472 proved that a
per-coordinate curvature (Fisher/Gershgorin) budget is quadratic,
not linear, in the error and that the optimal allocation is
monotone in curvature.

## (b) Formulas and Lean anchors (primes, Freeze 8462)

Second-order machinery (all in `Hagi.Theory.FisherQuant`):

- `quadLoss / quadGrad` — least-squares loss and its exact gradient;
- `crossCurv a j k = ∑ i, a i j * a i k` — the (i,j)-entry of the
  Hessian `AᵀA`;
- `colCurv a j = ∑ k, |crossCurv a j k|` — the GERSHGORIN diagonal
  `c_j = Σ_k |⟨col j, col k⟩|` (the naive diagonal `H_jj` claim is
  FALSE — off-diagonal mass is honestly priced in);
- `quadLoss_second_order` — the EXACT second-order identity
  `L(θ+δ) = L(θ) + Σ_j g_j δ_j + Σ_{j,k} crossCurv jk · δ_j δ_k / 2`
  (no inequality, no measurement);
- `hess_le_colCurv` — `δᵀ(AᵀA)δ ≤ Σ_j c_j δ_j²`;
- `fisher_quant_loss_bound` — MAIN abstract bound: under a
  coordinatewise curvature premise and per-coordinate quantization
  `|δ_j| ≤ ε_j`:
  `ΔL ≤ Σ_j |g_j| ε_j + Σ_j c_j ε_j² / 2`;
- `fisher_quant_loss_bound_opt` — at a stationary point (g = 0):
  pure curvature `ΔL ≤ ½ Σ_j c_j ε_j²`;
- `quadLoss_curv_le`, `quad_fisher_quant_bound(_opt)` — the
  curvature premise DERIVED (discharged) for the quadratic carrier;
- `fisher_beats_lipschitz`, `fisher_tolerance_mono` — anisotropy:
  flat coordinates (small c) tolerate a `c_max/c_min` factor more
  error (tolerance `ε_j ≤ 2L/c_j` regime);
- `fisher_alloc_mono` — BRIDGE to `Hagi.Budget.weightedExpAllocation`:
  the closed-form optimal exp-budget allocation is MONOTONE in the
  curvature weight c — coordinates where quantization hurts most
  get MORE bits; `fisher_alloc_isotropic_uniform` pins: isotropic
  curvature ⇒ uniform allocation, NO gain (honest).

## (c) Minimal Python diff

Where: (i) the ternary-jump scale selection and (ii) the self-edit
weight-prune ranking. Both currently use uniform ε. Replace with
per-coordinate ε derived from a cheap diagonal curvature proxy:

```python
import math

def col_curv(G):                       # G: (m, d) activation/feature matrix,
    C = G.T @ G                        # d x d Gram = A^T A  (crossCurv)
    return abs(C).sum(axis=1)          # c_j = sum_k |<col j, col k>|  (colCurv)

def fisher_eps(c, budget):             # eps_j ∝ 1/c_j at fixed sum = budget
    inv = (1.0 / c.clamp(min=1e-12)).sum()
    return budget * (1.0 / c.clamp(min=1e-12)) / inv

# ternary jump / weight prune:
c = col_curv(acts)                     # acts: last-batch feature matrix
eps = fisher_eps(c, eps_total)         # was: uniform eps_total/d
# quantize coordinate j to grid of radius eps[j]; acceptance unchanged
# (ternary_jump_checkStep-style energy gate / adoptGate), but the
# certified price is now  sum(|g|*eps) + 0.5*sum(c*eps**2)  (quadratic)
price = float((g.abs() * eps).sum() + 0.5 * (c * eps ** 2).sum())
```

## (d) Sanity numbers (primes C480, `.tmp/C480/sanity-fisher-quant.py`)

Exact-rational (Fraction) dataset, 3 samples × 3 coordinates,
A = [[1,0,0],[1,2,0],[0,1,3]], y = [1,4,3], θ = (1,1,1),
δ = (1/8, −1/4, 1/8):

- `quadLoss_second_order` identity: EXACT equality on Fractions
  (`True` — no float slack);
- `hess_le_colCurv`: Hessian form 11/64 ≤ Gershgorin 7/8 (True);
- `fisher_quant_loss_bound`: real ΔL = 0.585938 ≤
  Σ|g|ε + ½Σcε² = 1.187500 (True);
- stationary point (θ = exact least-squares solution, grad ≡ 0):
  ΔL = 0.085938 ≤ ½Σcε² = 0.437500 (True) — the pure-quadratic
  regime the weight-prune lives in;
- allocation at budget B = 3/4: optimal ε ∝ 1/c gives curvature
  penalty 0.649038 vs uniform 0.812500 — 1.25× better on this
  3-coordinate toy; the bit-space reading (bits monotone in c) is
  `fisher_alloc_mono`.

## (e) Validation criterion

Instrument each quantization event (ternary jump, self-edit prune):
measure the REAL loss change `ΔL_real` before/after and the
certified price `Σ|g_j|ε_j + ½Σ c_j ε_j²` computed with the SAME
c, ε. Accept: `ΔL_real ≤ certified price` on EVERY event of a full
run (real ≥ certified in the safe direction), and end-task metrics
(puzzle accuracy / holdout CE) not worse than the uniform-ε
baseline — the Fisher allocation should strictly reduce the total
certified price whenever c is anisotropic (`fisher_alloc_mono`
regime; isotropic case is a no-op by
`fisher_alloc_isotropic_uniform`).

## (f) Honest limits

- The abstract bound keeps the FIRST-order term Σ|g_j|ε_j; the
  pure quadratic form holds only near stationary points
  (`fisher_quant_loss_bound_opt`) — the weight-prune case; the
  mid-training ternary jump still pays the linear transport.
- `quadLoss_second_order` is exact for the QUADRATIC carrier only;
  for the real CE objective the curvature premise is an empirical
  proxy (Gram of activations/last-layer features) — the (e) loop,
  not the Lean identity, is the soundness check.
- `colCurv` is a GERSHGORIN diagonal (upper bound on the Hessian
  quadratic form, `hess_le_colCurv`): with correlated columns it
  can overestimate substantially (11/64 vs 7/8 in the toy — 5×);
  the allocation gain is real but the certified price is
  conservative.
- c is computed from a finite batch (sample noise); isotropic
  batches give NO gain (pinned by
  `fisher_alloc_isotropic_uniform`) — do not expect improvement on
  flat, decorrelated layers.
