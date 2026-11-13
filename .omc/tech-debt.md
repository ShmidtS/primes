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
