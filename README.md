# HAGI_v2 formalization (`Hagi/`)

Lean 4 / Mathlib (v4.34.1) formalization of the mathematical
core of the HAGI_v2 project — the ternary RD-channel causal
language model grown from small domain experts. Empirical
measurements (benchmarks, RMS errors, saturation curves) are
not mathematical statements and are out of scope.

Detailed per-round history: `STATUS.md`.

## Structure

| Directory | Content |
| --- | --- |
| `Prelude`, `Foundations` | Information-theoretic definitions (KL, entropy, TV, softmax); recurrence/telescope laws; Hoeffding/chord lemmas; the canonical scalar HAGI potential. |
| `Core`, `Architecture`, `Spectral`, `Depth` | Linear algebra of the merge: Sylvester–Hadamard orthonormality, Kronecker products, DFT-3/F₃ unitarity, real 6×6 lift, block-diagonal step-0 equivalence, parent-preserving lift, leaf selection theory, factorized merge, cortex/fiber geometry. |
| `Energy` | Ternary quantization (trits, nearest-grid rounding, error ≤ half-step), free-energy identities (KL descent, geometric pool), variance recursion, normalization seam. |
| `Data`, `Information` | Distillation identities (CE/KL), entropy preservation under recursion, mixture KKT, Fannes/Pinsker conditional forms, memory-capacity floors. |
| `Probability` | Finite concentration: Hoeffding, Azuma, batch variance = Var/B, success concentration → exponential takeoff, KLS/Poincaré interface (conditional), Friedman-type bound on finite histories (original). |
| `Ensemble` | Jensen-gap law (twoGap: exact cosh form, CE identity, quadratic bound), Hoeffding kernel, recursive distillation (telescoping, compound gain, harvest budget, greedy horizon-optimality), merge scaling. |
| `Step`, `Pretraining` | SafeQP controller (existence/uniqueness, stochastic and adaptive variants with explicit constants), joint-step regression laws, domination, STE step model; zeroth-order (Dust) estimator laws: exact unbiasedness, 1/K variance, alignment. |
| `Budget` | Bit allocation (marginal exchange, factor-2 balance, termination), water-filling, KV allocation, compute budget laws. |
| `Growth` | Cone/takeoff family: frontier-scaling invariant (sustained takeoff from production dynamics), gain renewal, disagreement chains, gain-operator chain, cone unification. |
| `Dynamics`, `External`, `Deployment`, `Discovery`, `Autonomy`, `Omni`, `Pretraining` | Contraction/endpoint budgets; imported laws (μP, vocab critical point, phase metric); proxy-shift budget; PPT discovery (MH kernels, truncation bias); exponential-weights routing, supervisor viability (halving), insight channel; omni (cross-modal gap = mutual information, capability gates, Φ-monotonicity). |
| `Unified` | The state-and-cycle layer: `GrowthState` (the measured stage ledger), stage theorems, macro-cycle, the conditional capstones (`MasterHAGI*`, `GrandSynthesis`), `CertifiedHAGIInvariant`, the nonvacuity witness, the assumptions record, the merge bridge. |
| `Model`, `Generalization`, `Runtime` | Gap-law model; generalization telemetry (`GenMetrics`, `Qgen`, gen-safe step); ternary exact accounting. |

## The three layers (honest status)

1. **Unconditional mathematics** — linear algebra, convexity,
   concentration, quantization: proved from scratch on finite
   carriers, no measured premises.
2. **Conditional certificates** — the capstone theorems
   (`MasterHAGI`, `MasterHAGI_trunc`, `grand_synthesis`)
   take the measured stage laws (`h_emp_*`) as explicit
   hypotheses. They are conditional statements about the
   loop, not derivations of the premises.
3. **Bridges (open frontier)** — the partially closed gap
   between the layers:
   - `Unified/Nonvacuity`: `CorePremises` is satisfiable —
     a concrete cycle with the quantization-distortion
     premise derived from the ternary rounding theorem;
   - `Unified/MergeBridge`: the merge stage law derived
     from the Core `lse` ensemble theory (merged CE =
     mean CE − Jensen gap, gap ≥ 0);
   - `Assumptions.Trunc`: the capstone premise set as one
     named record.
   Deriving the remaining `h_emp_*` premises (h_emp_grow,
   h_emp_smooth, h_emp_lip) from the Core layer is open.

## Build and checks

```bash
lake build                      # full build (use LAKE_JOBS=1 on low RAM)
bash scripts/ci.sh              # build + lint battery
```

Checks: `TrivialLint` (no sorry, no custom axioms, no
trivialities), `Freeze.py` (declaration statements locked in
`declarations.lock`), `DocLint` (docstring names/numbers
match code), `StatusLint`, `LayerLint` (folder-layer import
order, shrinking whitelist).

## Conventions

- Measured premises carry the `h_emp_` prefix; each is an
  explicit hypothesis, never hidden.
- Empirical/derived claims that are NOT theorems are marked
  in the module docstrings.
- Namespace `Hagi.*`; canonical definitions live in
  `Prelude.Info`, `Foundations.*` (dedup via delegation).
