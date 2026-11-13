# Tech debt (repo)

## C224: CertStep name duplication (transitional)

- `Hagi.Cert.CertStep` (new canonical kernel, layer 2) duplicates the
  name of `Hagi.Unified.HonestTransition.CertStep` (layer 6, cycle 41,
  with ~8 bridges/consumers).
- No Lean collision (different namespaces), but semantic duplication:
  master plan v3 Track S3 is to absorb/deprecate the legacy structure
  into the canonical kernel via adapters, not silent shadowing.
- Until S3 lands, both exist on purpose. Adapters must reconcile the
  legacy inequality-style budget fields with the kernel's exact
  consumption laws (`budget_next`/`risk_next` equalities) — potential
  spec arbitration if legacy only proves inequalities.

## C230: BatchCEAlignmentBudget sharp-range rewiring — RESOLVED (C233 R2)

- Resolved by C233 (addendum A5 §R2): `BatchCEAlignmentBudget` now
  carries the additive sharp wiring —
  `batchLogitRangeSquare_le_rangeCurvature_mul_alignment` (same
  curvature constant K controls the sharp R', unconditionally) and
  `alignment_le_scaled_logitCertifiedDrop` (budget constant
  `2/(K+1)` certifies the sharp `batchLogitCertifiedDrop` under
  `0 < batchLogitRangeSquare`), via the new bridge
  `batchCertifiedDrop_le_batchLogitCertifiedDrop` in
  `BatchCEStepCertificate.lean`. Single-example wiring in
  `Unified/DerivAlong.lean` (`ceStepLogitRange_sq_le_featureMass_sq_norm_sq`,
  `ceStepLogitQuad_le_engine`, `jointEnergy_le_ceLinear_logitRange`).
- Honest bounds: the telescope constant `(K+1)/2` itself does NOT
  sharpen (no sharper curvature constant follows from `R' ≤ R`
  alone), and `BudgetedParetoStepContract`/`BudgetedParetoStepCert`
  are NOT rewired: their deltas are tied to
  `budgetedParetoBatchTrainStep`, whose eta comes from
  `batchSafeStep` inside the TrainState machine (rewiring = new
  train-step pair + guard-branch replication, dependent-type
  surgery); no additive bridge exists because executed old-step
  descent does not dominate the sharp-step residual (different
  steps; the `drop ≤ drop'` bridge needs `0 < R'`, which does not
  transport to the executed step). Per-file dispositions:
  `.tmp/C233/matrix.md`, ALGORITHMS.md §15.
- C230 itself landed: bf16-guarded descent + Cert/Core
  TransitionStep adapter (Hagi/Contracts/BatchRangeBF16Cert.lean,
  Hagi/Cert/Adapters.lean).

## C234 (2026-11-13): A5 R3 Math/-layer gap
A5 targets `Hagi/Math/CertifiedArgmax.lean` (6-layer map), but
`Hagi/Math/` is absent from `scripts/LayerLint.py` LAYERS. Canon
landed at `Hagi/Cert/CertifiedArgmax.lean` (layer 2 certification
kernel). Migration to a dedicated Math layer deferred to the
6-layer unification beat; when created, move canon + update
LAYERS + umbrella import (namespaces preserved, Freeze-clean).

## TD A5-R3-C235: Info/Fannes Math-layer gap (2026-11-13)

A5 §R3 slice 2 (C235) mandates Info/Fannes consolidation into
`Hagi/Math/InfoCore.lean` + `Hagi/Math/FannesPinsker.lean`;
`Hagi/Math/` remains absent from `scripts/LayerLint.py` LAYERS.
Landed at the legal layering instead: `Hagi/Prelude/InfoCore.lean`
(layer -1; Prelude.Info + Information/DiscreteFannes +
Data/FannesSmooth — Information(1) would break Core/Geometry
same-layer consumers) and `Hagi.Probability.FannesPinsker.lean`
(layer 2; Unified/FannesComplete + InfoCanonical + NernstFannes +
Probability/PinskerTV — needs Probability peers, same-folder DAG).
7→2 file count per A5; namespaces preserved (FQN-stable). When the
Math layer is created, move both canons + update LAYERS + umbrella
imports (Freeze-clean, module-field-only census changes).

## TD A5-R3-C236: Gibbs/mirror-Hedge placement deviations (2026-11-13)

A5 §R3 slice 3 (C236): Gibbs/Hedge/MWU 10 files → GibbsCore +
MirrorHedge. Two legality-driven deviations, both documented in
.tmp/C236/{survey,plan,review}.md:
1. GibbsConcentration could NOT move "onto GibbsCore": it imports
   GibbsCooling (which imports GibbsCore — cycle) and the four
   Probability siblings EntropyConvexity/FannesPinsker/ChernoffCGF/
   MomentBounds (each importing GibbsCooling — no Gibbs-file can
   absorb it). Legal lowest common home = MirrorHedge (its only
   consumer was MWU, co-located there); ns Hagi.Probability
   preserved, FQN-stable.
2. MirrorHedge landed in Hagi/Optimization (layer 3), not beside
   Hedge in Autonomy: MWU's consumers include Optimization-layer
   modules; Optimization is the legal lowest common home. Ns blocks
   Hagi.Probability / Hagi.Optimization / Hagi.Autonomy all live in
   the one file (NsLint any-rule). When the Math layer unification
   beat lands (cf. C234/C235 notes), consider a dedicated
   Probability-level Gibbs superset module to host GibbsConcentration
   semantics closer to the Gibbs canon.
C228's ewNorm_survivor_lower preserved verbatim (verified in
RootApi). Freeze: only 2 private MWU helpers re-keyed by module
path (stmt hashes identical); typeHash changes 0.

## TD A5-R3-C237: water-filling x5 disposition + first adapter (2026-11-13)

A5 §R3 slice 4 (C237): "water-filling x5 -> WeightedExpAlloc; keep
discrete BitAlloc transfer". Survey (.tmp/C237/survey.md) findings:
1. `Hagi/Budget/WeightedExpAlloc.lean` ALREADY landed as the
   parameterized canon (cycle 66, 4ce97b2) on top of the abstract
   core `RankBudget.rankResidual_equalized` (exp-tangent
   equalized-marginal certificate, per-index κ + budget weights).
2. First adapter landed THIS beat: BitAlloc's continuous section —
   `water_filling_inner_optimum` reproofed as a genuine reduction to
   `rankResidual_equalized` (κ = log 2, unit weights; C221-pattern
   corollary reproof, statement byte-identical). The duplicate
   Jensen engine in the proof is superseded; `jensen_exp_sum_le`
   kept (byte-identical, reusable).
3. DEFERRED adapter #2 (documented plan, NOT landed):
   KVWater.waterfilling_bound. Reduction path: κ > 0 → core with
   weights ≡ 1, Λ = κ·λ, 0 < c derived from heq; κ = 0 → both
   residuals equal ∑ c (trivial); κ < 0 (outside the κ = log 2
   exponential-SNR model; the hypothesis set of the frozen statement
   does not exclude it) → local tangent argument retained, making
   the adapter a hybrid. Deferred rather than shipping a half-
   genuine reduction in the canon's flagship module.
4. A5 AMENDMENT RECOMMENDED: NeuronAlloc (Σ c/n loss, Cauchy–
   Schwarz, n ∝ √c, Engel structure) has a genuinely different
   mathematical premise (power-law residual vs exponential decay)
   and is NOT reducible to WeightedExpAlloc. It belongs to the
   compute-scaling/Engel family, not water-filling. Semantic
   honesty invariant: no forced unification.
5. Kept as A5 prescribes: the discrete BitAlloc transfer family
   (transfer_exact, imbalance_yields_gain, stable_factor_two,
   two_layer_*, WaterFilling.exists_balanced_allocation,
   BitAllocTermination chain) and WaterFillingMoE (generic KKT
   bookkeeping + channel dictionary, not exp-tangent).

## TD A5-R3-C238 — linear-cone consolidation 16→5 (not 16→2)

A5 §R3 nominal "16 cone files -> 2" is ILLEGAL under LayerLint + the
import-cycle structure; the landed honest maximum is 16→5 (13 files
merged into Hagi/Growth/LinearCone.lean and Hagi/Dynamics/
GrowthBridge.lean; every decl moved byte-identically, Freeze
zero-diff). Three keepers, with reasons:

1. Hagi/Foundations/ConeTakeoff.lean stays in Foundations(0):
   Generalization/ModeState(4) and Legacy consumers; any Growth(4)
   home is a cross-folder equal-layer violation.
2. Hagi/Foundations/GrowthBand.lean stays: Model/MeasuredEffects(4)
   consumer.
3. Hagi/Growth/Takeoff.lean stays: Growth-layer consumers
   (GainDecomposition, Saturation); merging into LinearCone would
   cycle LinearCone→GainDecomposition→StateBinding→LinearCone
   (via FrontierScaling), and ChainToCone cannot join LinearCone for
   the same reason — hence ChainToCone landed in Dynamics/
   GrowthBridge (it is a bridge: disagreement-chain → cone; its sole
   in-family consumer T3Ignition moved with it).
Amendment recommendation: A5 L3 wording "Hagi/Dynamics (LinearCone,
GrowthBridge)" should read "cone core in Hagi/Growth/LinearCone +
bridges in Hagi/Dynamics/GrowthBridge" — a Dynamics home for
LinearCone is unreachable while Growth-layer consumers
(StateBinding, Takeoff) exist.

## TD A5-R3-C239 — toy-witness quarantine 18→4 reality; 0/10 dirs disbanded

C239 (HEAD parent 8a7c3011). Two A5 §R3 tail items landed with honest
deviations:

1. "18 toy -> Benchmarks": ~14 of the 18 were already quarantined by C217
   (Hagi/Legacy/Nonvacuity, QuadraticConcrete, *Witness files). C239 moved
   the remaining 4 root-reachable toy leaves to the new
   Hagi/Benchmarks quarantine lib (C217 pattern: separate default-target
   lean_lib, ReachLint/NsLint exemptions, Freeze still tracks via
   inventory.lean umbrella import): QuadLoopWitness, QuarticWitness,
   QuadraticEndToEnd (Hagi/Examples/ dir thereby disbanded),
   Unified/TernaryWitness. Main census 12121→12032 (−89 rows, all from the
   4 namespaces; Freeze zero-diff proves no statement lost).
   KEEP (load-bearing, NOT quarantined): Unified/QuadMachine (QuadGate/
   QuadTrajectory/QuadBudget consumed by MachineProto), Unified/
   DescentCoreQuad(+Diag) (consumed by RateTheory/LoopInstances),
   Foundations/QuadEta (quadLossAt: TrainingTransition/MomentumHB/State),
   Learning/ToyTrajectory (TrainingTransition consumer), Unified/
   LoopInstances (instantiation layer).
2. "disband 11 single-file dirs (keep Cert/)": 0 disbanded. Legal blocker:
   Freeze forbids public FQN churn and NsLint requires folder==namespace,
   so disbanding = namespace rename = mass statement rename signal; the
   only legal mechanism is a Benchmarks/Legacy-style exempt quarantine,
   which none of the 10 qualifies for. Per-dir keep reasons (all verified
   single-file): Prelude/InfoCore (layer −1 base, 20+ consumers);
   Geometry/SphericalSimplex, Spectral/RankGrowth, Numerics/SoftmaxFix,
   Sparsity/SparseStep0, Planning/Imagination (real formalizations, not
   toy; their A5 L1 "Math" target dirs do not exist yet); Generalization/
   ModeState (Legacy/MasterHAGI consumer); Percolation/Site (root consumer
   SchellingPercolation; A5 R4 is its designated beat); Audit/Audit
   (layer-0 foundations, "to be split"); Challenge/MasterChallengeV3
   (ChallengeCheck gate target); Cert/ (3 files, A5 keeps).
   scripts/ClosureReport.py still lists pre-C217 module paths (stale
   inventory, not part of ci.sh battery) — left untouched, out of scope.

## TD A5-R4-C240 — Research quarantine landed; MDL disposition (2026-11-13)

1. Research quarantine DONE (C240): 12 modules moved byte-identical
   (statements untouched; only intra-cluster import lines rewritten) to
   Hagi/Research/ (C239 Benchmarks pattern: separate default-target
   lean_lib Hagi.Research, ReachLint/NsLint exemptions, Freeze tracks via
   inventory.lean): Omni/{ConditionalInformation,CrossModalGap,
   OmniInvariant,OmniState}, Percolation/Site, Discovery/{PPT,PPTCanonical},
   Optimization/{Schelling,SchellingPercolation,MarkovPercolation},
   Contracts/{SchellingCandidateSelection,SchellingMarkovRouting}.
   Closed cluster — zero root consumers beyond Hagi.lean (survey
   .tmp/C240/survey.md §A); namespaces kept → public FQNs unchanged.
   Main census 12032→11783 (−249 OWNER rows, all from the 12 moved
   sourceModules).
2. MDLThreeCurrency "double-counting fix" (A5 §R4) — DISPOSITION: no docs
   misaccounting found (STATUS/README/ALGORITHMS describe
   `double_counting_identified` accurately; ALGORITHMS.md has no MDL/J3
   text). The theorem is a feature: it algebraically IDENTIFIES the naive
   identification `cst = Lpred` (state cost := data code length) as double
   counting. J3 family has zero consumers — nothing in the corpus actually
   double counts. Honest fix requires MATH (future beat): define a
   C_state bridge (state-code length ≠ data-code length, e.g. bits of
   packed weights post-consolidation) so the identification is impossible
   structurally, then wire C_state to the consolidation loop (MDLRank/
   BitAlloc). No half-fix in a refactor beat — documented here only.

## TD A5-R5-C241 — GROUPSCALE-EXEC: computable per-block scale argmin (2026-11-13)

R5 isolation (C241) verified: all Classical.choose selectors
(batchGradientMinimizer, minimumResource, robustMinimumResource,
selectedGroupScales, selectedCoupledScales) are consumed only by
theorems; the executable path already rests on batchLogitSafeStep,
segmentMinNorm, safeqpEtaMax, finiteSelection (cost bridge
finiteSelection_cost_eq_minimumResource). The 255^G joint search is
decidable-finite; its problem is cost, not constructivity
(ALGORITHMS.md §16).

CLOSED (C248, A8 F5, 2026-11-13): landed in
Hagi/Model/CEGroupedScale.lean — `selectedGroupScalesExec` (explicit
`List.foldl` argmin over `List.finRange 255`, seed
`knownSampleScale`), fold invariant `foldl_argmin_inv`, minimality
`selectedGroupScalesExec_score_le`, COST EQUALITY
`selectedGroupScalesExec_cost_eq` (tie-tolerant, finiteSelection
pattern), surrogate total `selectedGroupScalesExec_total_le`.
Empirical grounding (A8 F5, Class-D, motivation only): dynamic
per-block scale 2.64x better than L2 rounding. Honesty note: def
stays `noncomputable` (classical ℝ comparison) — the algorithm is an
explicit finite fold, not a choice operator; the deferred item asked
for exactly this shape. No runtime consumer yet — the selector is now
evaluable as data when one arrives.
