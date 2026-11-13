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
