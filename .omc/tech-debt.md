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

## TD A8-F6-C254 — Matrix Newton–Schulz hP removal (2026-11-13) — CLOSED (C296+C297)

FURTHER RESOLVED (C297, `feat: spectral norm svd transport
contraction`, parent 12f0e390). C296 proven: diagonal action +
sup-norm contraction + orthogonal equivariance. C297 adds the
spectral-norm transport: the pinned Mathlib DOES have a
spectral-norm Matrix API (scoped `Matrix.Norms.L2Operator`,
CStarRing identity) — the C296 "absent" verdict was stale;
`nsSpectralNorm_orth_inv` (orthogonal invariance) +
`ns_contraction_svd` (SVD-premise spectral contraction,
`A = U Σ Vᵀ`, entries in [0,1]) + consumer `muon_step_bound_ns_svd`
(Euclidean-space hP discharge under the SVD premise). REMAINS
OPEN: SVD existence (the decomposition is a premise), iterate
lifting, and the fully general hP-free Muon statement. Original
entry follows.

DEFERRED (C254, item 3). Target: remove the hypothesis
`hP : ∀ z, ‖P z‖ ≤ ‖z‖` from `muon_step_bound`/`muon_pl_rate`
(Hagi/Step/Muon.lean) by proving contraction for the actual
Newton–Schulz polar iterate U ← U(3I−UᵀU)/2. Honest analysis:
the scalar certificate exists (`nsStep_dist_sq`, `nsIter_mem`,
C231), but lifting the scalar map σ ↦ σ(3−σ²)/2 to the matrix
iterate requires functional-calculus / spectral-transfer machinery
(singular values of the iterate vs the map applied pointwise),
which Mathlib does not provide off-the-shelf here. No cheap slice
exists: `muonDir P g = P g`, so the bound IS the contraction
contract. Future beat: matrix spectral transfer for NS iterations
(eigenvalue/singular-value interlacing or polynomial composition
argument), then instantiate hP. Expected outcome was DEFER — no
gold-plating attempted.

## TD A10-C287 — HoeffdingBridge quarantine (2026-11-15) — DONE (C288)

RESOLVED in C288 (`refactor: delete weaker hoeffding bridge leaf`,
parent 5a2de978): `Hagi/Ensemble/HoeffdingBridge.lean` deleted,
`Hagi.lean` import removed, lock row
`Hagi.Ensemble.hoeffding_tail_via_weighted` removed surgically
(declarations.lock 6670→6669 rows; Freeze verify PASS, 372 known
non-fatal additions since C258 left out per repo convention).
Justification: `Hagi.Probability.hoeffdingBridge_weaker` (C287)
proves canonical exponent ⇒ bridge exponent; 0 consumers (fresh
rg scan, C288 plan). RootApi NEG-1 confirms the FQN no longer
resolves.

## TD C288 — latent STMDUP twins in BatchCEBudgetGuard (2026-11-15) — DONE (C289)

RESOLVED in C289 (`fix: dedup param twin in budget guard`, parent
b9fba226): both `_param` twins DELETED (0 consumers, fresh rg scan,
`.tmp/C289/plan.md`); not alias-converted (dead name, YAGNI). No
lock surgery: the twins were never in declarations.lock (un-baked
drift; lock stays 6669 rows, Freeze verify PASS, byte-identical
restore after bake test). Clean-bake verification: fresh
`Freeze.py --update` on fixed tree ⇒ 7039 declarations, STMDUP PASS
(0 groups) — the duplicate is gone (`.tmp/C289/bake-postfix.log`,
`stmdup-postfix.log`; pre-fix reproduction `stmdup-prefail.log`).
NamePool delta: exactly the 2 twin names removed, 0 added.
Drift-baking disposition: the 370-row addition drift (372 − 2 twins)
remains NOT baked, per the repo convention since C258 (C288
precedent); the STMDUP barrier to a future bake is now removed —
the next `--update` after review will bake cleanly.

Original record:

DISCOVERED in C288: commit 4448280 (C286, "parametric instances for
ce variants tranche three") added `batchSampleCE_nonneg_param` and
`batchCEObjective_nonneg_param` (Hagi/Contracts/
BatchCEBudgetGuard.lean L460/L472) with statement hashes IDENTICAL
to the pre-existing `batchSampleCE_nonneg` / `batchCEObjective_
nonneg`. Masked because declarations.lock was stale since C258
(verify-mode counts additions "fine", STMDUP reads the lock).
Reproduced: clean HEAD 5a2de978 + full `Freeze.py --update` ⇒
STMDUP FAIL (2 groups). Disposition for a dedicated beat: delete or
restrengthen the `_param` twins (differentiate statements), then
run `Freeze.py --update` baking the accumulated 372-row addition
drift; STMDUP must PASS on the refreshed lock.

Original quarantine record (C287):

QUARANTINE FLAG (C287, A10 merge map: "Concentration single
radius/confidence API + e-process core, delete HoeffdingBridge").
Target: `Hagi/Ensemble/HoeffdingBridge.lean`
(`hoeffding_tail_via_weighted`, bound `exp(−t²/(2n²))`). NOT deleted:
the freeze lock (`declarations.lock`) blocks deletion until
`scripts/Freeze.py --update` after review. Deletion evidence now
formalized: `Hagi.Probability.hoeffdingBridge_weaker`
(Concentration.lean, C287) proves the canonical exponent
`exp(−2t²/n)` implies the bridge exponent `exp(−t²/(2n²))`
(exponent gap factor n/4 at every n ≥ 1); the bridge is an in-tree
leaf (survey `.tmp/C287/survey.md`: no consumers). Disposition:
awaiting `Freeze.py --update`, then remove module + `Hagi.lean`
import `Hagi.Ensemble.HoeffdingBridge`.

## TD C298 — latent STMDUP twin compounding_bound/slack_geometric_decay (2026-11-15) — CLOSED (C299)

DISCOVERED in C298 health beat (clean-bake Freeze experiment,
`.tmp/C298/bake.log` + `stmdup.log`, C289 protocol): fresh
`python scripts/Freeze.py --update` on clean HEAD 3553af58 ⇒ 7074
declarations, `scripts/StatementDupCheck.py` ⇒ **STMDUP: FAIL
(1 group)**: `Hagi.Probability.compounding_bound` ≡
`Hagi/Model/EnergyReasoning/AlternatingRound.lean:Hagi.Model.
EnergyReasoning.slack_geometric_decay` (identical statement hash;
the AlternatingRound twin was added in C293/C294 and is part of
the un-baked drift since C258 — lock still 6669 rows, which is why
normal CI passes: STMDUP reads the lock). Lock restored
byte-identical after the experiment; Freeze verify PASS on the
surgical lock (`.tmp/C298/freeze.log`). Disposition for a
dedicated beat: consumer scan, then delete the weaker twin or
restate one with a differentiated statement; then bake the
accumulated addition drift (6669→7074) so STMDUP guards the real
tree again. No fix attempted in C298 (analysis beat, no Lean
changes).

CLOSED by C299 (`fix: dedup compounding twin and bake lock`):
private twin `slack_geometric_decay` deleted (single consumer
`slack_partial_sum` re-pointed to the public
`Hagi.Probability.compounding_bound` via per-t bridge; public API
kept — zero in-repo consumers but lock row 4787). Lock baked
6669→7073 (7074 clean-bake minus the twin): bake diff minimal
(exactly one removed row, statement hash match 3a6d46574483e4b8);
Freeze PASS + STMDUP PASS post-bake. First full bake since C258
— precedent policy: bake only with (a) pre-edit clean-bake log,
(b) STMDUP check on candidate lock, (c) minimal-diff proof vs
pre-edit clean-bake, (d) Freeze+STMDUP PASS post-bake.

## TD E4-C300 — nonlinear backbone composition ladder (OPEN, seeded)

E4 full nonlinear backbone certificate (rank 2 of the C292-C297
analysis). C300 lands the SEED
(`Hagi/Model/BackboneTransfer.lean`): the residual-transfer
induction step — certified head drop through one residual block
with leak `Lc*mu*||dx||` — plus the multiplicative stack bound
`(prod(1+mu_i)-1)*||dx||` (cascadeGain pattern, C250 machinery
cited not reproved). No differentiability hypotheses
(premise-form LipschitzWith; the R3-rejected z-differentiability
route is bypassed at the composition level). REMAINING LADDER
(each rung a candidate beat): (1) attention-softmax Lipschitz
premise — turn `attention_error_damped`
(`Hagi/Core/Attention.lean`) into a mu_attn bound on the softmax
map itself — LANDED by C307 (see TD E4-C307); (2) RoPE exactness — rotation isometry giving a mu=0
rung (`Hagi/Core/RoPEMoments.lean` context); (3) GDN RAM
read/write perturbation rung (`Hagi/Model/GDNBridge.lean`); (4)
RMSNorm unit-RMS giving bounded logit scale feeding C291 constants
(`Hagi/Model/RMSNorm.lean`); (5) chain rungs 1-4 into
`resStack_transfer_descent` for the full FastArch3 stack. Not
claimed anywhere: full forward/backward certificate.

## TD E4-C307 — attention block transfer composition (DONE)

E4 ladder rung 1 (TD E4-C300 remaining rung 1). C307 lands
`Hagi/Model/AttentionTransfer.lean`: the attention error-damping
certificate (`Hagi.Core.attention_error_damped`) wired into the
C300 residual-transfer stack. Interface verdict: the carrier
bounds the WEIGHTED-OUTPUT deviation (value errors e i); the
bridge is e i := v i (x+dx) − v i x (value-map response), giving
`attn_branch_damped` (branch perturbation ≤ max_i value response)
and `attn_branch_lipschitz` (uniform LipschitzWith μatt value
premise ⇒ LipschitzWith μatt branch). Pre-norm enters as a
LipschitzWith μn premise (RMSNorm rung 4 instantiates it later);
`attn_norm_branch_lipschitz` gives LipschitzWith (μn·μatt) — the
exact C300 block-hypothesis shape — so `attention_block_transfer`
(one pre-norm + softmax-weighted branch + residual block)
inherits the C300 leak bound and the stack
(`AttnBlock`/`attnStack`/`attnGain` =
∏(1+μnᵢ·μattᵢ)) inherits `attention_stack_transfer_descent`
(+`_strict`) via `resStack_transfer_descent`. Numeric anchors
(μ_att=0.3, μ_res=0.2: (1.3)(1.2)−1 = 0.56 ≥ 0.5). HONEST SCOPE:
softmax weight map (p from x through QK^T) is premise-form (fixed
probability distribution); RMSNorm Lipschitz is premise-form;
RoPE exactness is NOT landed (`rot_norm` preserves `pairInner`,
not a normed-space norm — a norm-carrier isometry lemma needs a
new norm surface = next rung); full FastArch3 forward/backward
certificate NOT claimed. REMAINING LADDER (updated): (1) RoPE
norm-carrier isometry rung — LANDED by C308 (see TD E4-C308);
(2) GDN RAM read/write perturbation rung
(`Hagi/Model/GDNBridge.lean`); (3) RMSNorm unit-RMS feeding
bounded logit scale (`Hagi/Model/RMSNorm.lean`); (4) chain all
rungs into the full FastArch3 stack certificate.
Not claimed anywhere: full forward/backward certificate.

## TD E4-C308 — rope isometry transfer composition (DONE)

E4 ladder rung (TD E4-C300 remaining rung 2 / C307 next-rung
note). C308 lands `Hagi/Model/RoPETransfer.lean`: the RoPE
rotation as a genuine NORMED-SPACE isometry wired into the
C300/C307 transfer stack. Route verdict: `rot_norm` gives only
the same-vector form (pairInner (R x) (R x) = pairInner x x) — NOT
enough for an isometry; the carrier-supported bridge is the FULL
bilinear preservation `rope_pair_inner` (per-block 2x2 rotation
orthogonal), plus the explicit transport `toEuc`/`fromEuc` to
`EuclideanSpace R (Fin d ⊕ Fin d)` with the exact-norm lemma
`toEuc_norm_sq` (‖toEuc x‖² = pairInner x x). Then
`rotEuc = toEuc ∘ rotVec ∘ fromEuc` is an `Isometry`
(`rope_isometry`); isometry pre/post-composition keeps Lipschitz
constants (`rope_block_transfer`, `rope_block_post_transfer`), a
rope-wrapped pre-norm attention block satisfies the SAME C300
leak bound at unchanged μn·μatt (`attention_block_rope_transfer`),
and stacks of wrapped blocks descend with the UNCHANGED gain
(`attnRopeGain_eq`, `attention_rope_stack_transfer_descent` +
`_strict`). Anchor: d=2, θ≡π/3, m=1 on ![(3,4),(0,0)] — norm 5
preserved. HONEST SCOPE: no matrix-orthogonality (RᵀR=I) or
operator-norm statement (the Euclidean isometry via pairInner is
the proved route); no existing statement changed (rot_norm
untouched); softmax weight map and RMSNorm constants stay
premise-form (C307); full FastArch3 forward/backward certificate
NOT claimed. REMAINING LADDER (updated): (1) GDN RAM read/write
perturbation rung (`Hagi/Model/GDNBridge.lean`); (2) RMSNorm
unit-RMS feeding bounded logit scale (`Hagi/Model/RMSNorm.lean`);
(3) chain all rungs into the full FastArch3 stack certificate.
Not claimed anywhere: full forward/backward certificate.

## TD E5-C301 — Venn/ANF compiler bridge ladder (OPEN, seeded)

E5 Venn/RAM compiler bridges (rank 3 of the C292-C297 analysis).
C301 lands the ANF CORE seed
(`Hagi/Data/AnfTransform.lean`): the Zhegalkin/Möbius transform
as the recursive butterfly on truth tables
(`(Fin n → Bool) → Bool`), its INVOLUTION (`anf_inversion` —
Möbius inversion on the Boolean lattice, butterfly induction +
GF(2) linearity `anf_add`), the subcube parity characterization
(`anf_subcube`: c_S = parity of f over {x ⊆ S}, in ZMod 2), and
the compile roundtrip (`anf_eval_eq`: eval ∘ transform = id) with
Fin 2 XOR/AND decide anchors. REMAINING LADDER (each rung a
candidate beat): (1) compose3 — the ternary Venn composition on
the Python side mapped onto the two-variable lattice carriers;
(2) context signatures — the Python V3 context-signature extraction
as a typed statement over the same carriers; (3) argument ranges —
range/dispatch correctness for compiled Venn arguments; (4)
collision abstention — the abstain-on-collision policy as a
certified predicate. Not claimed anywhere: end-to-end Python V3
compiler equivalence.

## TD E5-C302 — ANF compose3 seed + guarded support (OPEN, seeded)

E5 ladder rung 2 (TD E5-C301 rung 1). C302 lands the compose3 SEED
(`Hagi/Data/AnfCompose.lean`): truth-table-level composition
`anfCompose f g h x = f (g x) (h x)` (outer Bool×Bool, inner on
the shared Fin n carrier), its ANF synthesis instances
(`anfCompose_coeff` — subcube-parity coefficients of the composed
table, instance of anf_subcube; `anfCompose_eval` — compile
roundtrip, instance of anf_eval_eq — packaged as the Python
compose3 API), context-guard soundness (`anfAgreeOn`/
`anfSupportedOn`/`stencil_guard_sound`: support-dependence
composes for ANY outer f — the no-false-coverage direction of the
Python context-signature abstention; converse false, not claimed),
and the Fin 2 OR∘(AND,XOR) decide anchor. Degree bound
deg(f∘(g,h)) ≤ deg f · max(deg g, deg h): docstring NOTE only —
no monomial/degree API on the carrier yet. REMAINING LADDER:
(1) degree API + the degree bound as a theorem; (2) context
signatures — typed extraction statement; (3) argument ranges —
range/dispatch correctness; (4) collision abstention — certified
abstain predicate. Not claimed anywhere: end-to-end Python V3
compiler equivalence.

## TD E5-C306 — ANF dispatch collision abstention (DONE)

E5 ladder rung 3 (TD E5-C302 remaining rungs 3+4). C306 lands
`Hagi/Data/AnfDispatch.lean`: the Python V3 dispatch/abstention
policy as a certified two-candidate dispatch on the AnfTransform
carriers — `AnfCand` (stencil + `argRanges` Finset),
`inRange` (EXACT-match range model: the context's position set
equals the candidate's range, `∀ i, x i = decide (i ∈ R)`,
decidable; the subset reading is REFUTED — empty/nonempty disjoint
ranges both-applicable counterexamples make the required
disjointness lemma false), `collides` (both in range + outputs
disagree), `dispatchOrAbstain` (one applicable → its value; none
→ default; both → agreement check, disagree → `none`),
`dispatch_sound`/`dispatch_sound_default` (acceptance/default
correctness), `abstain_sound` (collision ⇒ abstain, no false
coverage), `guard_disjoint_no_collision` (disjoint NONEMPTY
ranges ⇒ never collide — the C302 stencil_guard_sound
composition, holding without supportedness; degenerate both-empty
pair excluded by the Nonempty side-condition and documented), and
the Fin 2 decide anchors (colliding pair → abstain; disjoint pair
→ dispatch ok). REMAINING LADDER: (1) multi-candidate (>2)
dispatch with the Python arg-range PRIORITY ordering; (2) degree
API + degree bound theorem; (3) typed context-signature
extraction statement. Not claimed anywhere: end-to-end Python V3
compiler equivalence.

## TD A12-C304 — credo quarantine deletions step 1 (DONE)

Executed the C282 §1.2 flagged-but-frozen shim list with the
C288/C289/C299 protocol (fresh 0-consumer scan → surgical lock row
removal → bake verify → per-name ledger). DELETED (5 names, all 0
external consumers; in-file use rewritten to canonical):
Hagi.Architecture.fiber_cortex_zero (alias; in-file caller switched
to fiberSplitOrtho), Hagi.Data.entTV_nonneg, Hagi.Probability.exp_chord
(alias; hoeffding_chord_mgf rewritten to Foundations.exp_chord_r;
export removed), Hagi.Probability.bhatia_implies_popoviciu (alias),
Hagi.Unified.MasterHAGI_linked (closed consumer set of one).
KEPT with fresh consumer evidence (build-hard): MasterHAGICore
(consumer: MasterHAGICoreOperational_v2 in Legacy/CorePremisesDerived),
MasterHAGI (consumer: nonvacuity witness in Legacy/Nonvacuity),
MasterHAGI_trunc (consumer: capstone bridge in Legacy/Assumptions).
KEPT by audit: ResidualVQ Model vs Budget — NOT statement duplicates
(zero shared statements, STMDUP 0); CertifiedTransition V1/V2/V3 —
live consumers (Ctv2Telescope, TransitionCert, LogitGrowth,
ProductiveTransition). Lock: 7114 → 7109 (surgical −5 rows; bake
diff vs surgical lock = exactly the 18 C303 RamProtocol drift rows,
not baked per C289 convention). AssumptionScan UNPREFIXED registry
MasterHAGI.lean row shrunk 3/3/2/2/2 → 2/2/1/1/1 (conscious
shrink-only update via C304 plan review; script dict + assumptions.lock
both updated). LOC: tracked Lean 162320 → 162254 (−66). Root census
main=13430. CI 1×PASS + ALLAXIOMS PASS (.tmp/C304/battery3.log).
