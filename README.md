# HAGI_v2 formalization (`Hagi/`)

Lean 4.35.0 / Mathlib formalization of the mathematical
core of the HAGI_v2 project — the intended ternary RD-channel
causal language model grown from small domain experts. Empirical
measurements (benchmarks, RMS errors, saturation curves) are
not mathematical statements and are out of scope.

Detailed per-round history: `STATUS.md`.

## Structure

| Directory | Content |
| --- | --- |
| Prelude, Foundations | Information-theoretic definitions (KL, entropy, TV, softmax); recurrence/telescope laws; Hoeffding/chord lemmas; the canonical scalar HAGI potential. |
| Core, Architecture, Spectral, Depth | Linear algebra of the merge: Sylvester–Hadamard orthonormality, Kronecker products, DFT-3/F₃ unitarity, real 6×6 lift, block-diagonal step-0 equivalence, parent-preserving lift, leaf selection theory, factorized merge, cortex/fiber geometry. |
| Energy | Ternary quantization (trits, nearest-grid rounding, error ≤ half-step), free-energy identities (KL descent, geometric pool), variance recursion, normalization seam. |
| Data, Information | Distillation identities (CE/KL), entropy preservation under recursion, mixture KKT, Fannes/Pinsker conditional forms, memory-capacity floors. |
| Probability | Finite-sample probability and selected-batch inference: Hoeffding, Azuma and Freedman-type bounds; supported importance-weighted loss and Euclidean-gradient MSE, exact propensity optima and upper-envelope guarantees; MWU/hedge, Gibbs/PAC-Bayes and information-theory identities. These are statements about the declared finite models, not sampling-runtime or generalization guarantees. |
| Ensemble | Jensen-gap law (twoGap: exact cosh form, CE identity, quadratic bound), Hoeffding kernel, recursive distillation (telescoping, compound gain, harvest budget, greedy horizon-optimality), merge scaling. |
| Step, Pretraining | SafeQP controller (existence/uniqueness, stochastic and adaptive variants with explicit constants), joint-step regression laws, domination, STE step model; zeroth-order (Dust) estimator laws: exact unbiasedness, 1/K variance, alignment; RCDL mode-A: exact descent-history ⟷ rank-1 LiveDelta bridge, additive Frobenius consolidation budget, three-currency MDL objective with double-counting detector and no-compression-below-entropy bridge. |
| Budget | Bit allocation (marginal exchange, factor-2 balance, termination), water-filling, KV allocation, compute budget laws. |
| Growth | Cone/takeoff family: frontier-scaling invariant (sustained takeoff from production dynamics), gain renewal, disagreement chains, gain-operator chain, cone unification. Thermostat vertical: T_t = T₀α^t annealing, monotone cooling, concentration gates, certified-state capstones (stop ∧ gate ∧ concentration ∧ ε-representative point) and the four purities along the anneal (TV → 0, ⟨E⟩ → E*, F → E*, S → 0, excess ⟨E⟩−F → 0), calorimetric excess bound, admission-margin soundness of the memory controller; full six-pair bridge graph (Gibbs ↔ thermostat ↔ Hoeffding ↔ MWU). |
| Dynamics, External, Deployment, Discovery, Autonomy, Omni, Pretraining | Contraction/endpoint budgets; imported laws (μP, vocab critical point, phase metric); proxy-shift budget; PPT discovery (MH kernels, truncation bias); exponential-weights routing, supervisor viability (halving), insight channel; omni (cross-modal gap = mutual information, capability gates, Φ-monotonicity). |
| System, Unified | The state-and-cycle layer: `GrowthState` (core state + `StageEffects` measured ledger + `Certificate`/`Metrics`/`Candidate`), `StageCertificate` with the per-generation soundness and the multi-generation telescope (`stage_certificate_telescope`), the conditional capstones (`MasterHAGI*`, `GrandSynthesis`, `ArchitectureTheorem` with `HAGICert` on `Fin I` domain families), `CertifiedHAGIInvariant`/`CoupledHAGIInvariant` with numeric nonvacuity witnesses, the assumptions record (`Assumptions.Trunc` + idle witness), the merge bridge, the state-level takeoff, the end-to-end live-weights cycle; the memory-management cycle: admission controller (novelty ∧ certified gain), consolidation quality bound, quantized safe-update window. |
| Model, Generalization, Runtime | Finite CE/batch-gradient models and bridges to selected-gradient MSE; generalization telemetry (`GenMetrics`, `Qgen`, gen-safe step); ternary exact accounting. None of these is by itself a held-out guarantee or an optimal architecture theorem. |

## Module organization

Modules follow declaration carriers, proof dependencies and consumers,
not merely topic names or directory size. Existing cohesive
consolidations are retained; further joins require a bounded reviewed
packet with declaration/type/body retention and consumer checks.
`Hagi.lean` is the import root. The non-root `Hagi/` tree currently has
494 modules; two are reached transitively rather than directly.
A consolidation is not evidence of reduced training cost or FLOPs.

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
   Deriving an arbitrary stage model's `h_emp_grow`,
   `h_emp_smooth` or `h_emp_lip` from Core alone is not
   established. Selected premises are derived only for their
   specialized carriers; that does not discharge the same-named
   premises of every other model.

The **C200 source snapshot**
(`5a3fb7116f1a279c156e63ca8b6d41ba1af1fa69`) has
494 modules, 12,076 Root constants, 9,054 ALLAXIOMS records,
6,170 Freeze declarations and 313 intrinsic declarations; 0 sorry.
LayerLint passes with one explicit retained cross-layer exception.
Per-cycle history: `STATUS.md`; algorithms and supported sampling
results: `ALGORITHMS.md`.

The **R1/P1-D packet** preserves that mathematical API while eliminating
four exact statement-duplicate groups. Two original public theorem names
are genuine Batteries aliases to their canonical proofs. A public
`posterior_congr_of_model_eq` now owns the shared EM posterior transport;
the guarded-logit duplicate reuses its retained same-file private theorem.
Across the six changed modules their preserved statements, nine redirected
calls and two alias bodies account for exactly 11 compiled body changes;
the four asymmetric-cost consumer bodies are unchanged.

Post-packet facts: 12,074 Root constants = 8,014 public + 513 private +
3,547 generated; 9,052 ALLAXIOMS records; 6,168 Freeze declarations;
313 intrinsic declarations; 1,213 retained IR entries and no module-count
change. `scripts/StatementDupCheck.py` has zero groups. These are formal consolidation counters,
not evidence of improved training, lower model size, runtime or FLOPs.

The former 4,354-row legacy Freeze lock was first reconciled to the
6,170 declarations of the C200 source snapshot, then received the reviewed
R1/P1-D update to 6,168. Generated `declarations.lock` and
`scripts/namepool.txt` are ignored by Git. AssumptionScan still reports
36 files/116 lexical labels (5 proved declarations plus 111 premise
binders), not 111 unused or automatically removable assumptions.

## The canonical capstone (Gen-3)

The master result is `CertifiedLoop.certified_loop`
(Unified/CertifiedLoop.lean): a chain of `StepCert` steps —
dependent honest descent (`HonestTransition.actualDescent`:
obj s' ≤ obj s − drop), componentwise quality floor
(`FloorKept`), honest budget (b' ≤ b − spend) — yields
simultaneously Σdrops ≤ obj₀ − objₙ, quality on every
intermediate state (`certified_loop_all`), strict descent
for n ≥ 1 (`certified_loop_strict`) and the budget
telescope. The gate `gate_never_increases` (commit/hold)
keeps energy non-increasing always. Non-vacuity: the
executable quadratic machine instantiates the certificates
on any horizon (`quad_loop_horizon`, `quad_witness_T3`,
`quad_witness_T10`); the CI CHALLENGE gate pins the
Gen-3 statement (`master_hagi_challenge_v3`).

The old flat Gen-1 capstones (`MasterHAGI*`,
`grand_synthesis`) are `@[deprecated]`: the copied-effects
semantics is provably inconsistent at T = 2
(the obstruction is documented in the audit trail; the module
was removed as a verbatim wrapper).

## Repo layout

- `Hagi/` — 494 modules of the HAGI_v2 formalization, imported by
  `Hagi.lean`; see `STATUS.md` and `ALGORITHMS.md`;
- `scripts/` — the CI lint battery and audit tooling (`ci.sh` is the
  single entry point); lexical assumption data: `assumptions.lock`.
  The older `spec_manifest.toml` is a historical R237 snapshot, not
  the current corpus manifest.

## Build and checks

```bash
lake build                      # full build (use LAKE_JOBS=1 on low RAM)
bash scripts/ci.sh              # build + lint battery
```

Checks: TrivialLint (no sorry, no custom axioms, no
trivialities), Freeze.py (declaration statements checked against
`declarations.lock`), DocLint (docstring names/numbers
match code), StatusLint, LayerLint (folder-layer import
order, shrinking whitelist), DupLint/NsLint, CHALLENGE
(Gen-3 comparator capstone), STMDUP, MACHINEDIFF
(differential machine tests), ALLAXIOMS (axiom purity of
every theorem). All 16 gates passed at C200; see `STATUS.md`
for the exact snapshot. Passing CI is not a proof of physical
runtime fidelity or optimal model quality.

## Conventions

- Measured premises carry the `h_emp_` prefix; each is an
  explicit hypothesis, never hidden.
- Empirical/derived claims that are NOT theorems are marked
  in the module docstrings.
- Namespace `Hagi.*`; canonical definitions live in
  `Prelude.Info`, `Foundations.*` (deduplicate by proved delegation
  only when carrier and assumptions agree).
