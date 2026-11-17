# Analysis of proved: C361–C372 period (2026-11-17, 12 commits)

All receipts terminal (`.tmp/C361..C372`, none skipped); full battery CI
PASS at every landing beat (per-beat battery/build logs). HEAD 06d5193
(C372), tree clean. This beat (C373) is READ-ONLY analysis + this doc.

## Commit one-liners (C361–C372)

- C361 056a342 `feat:` typed premise registry + generated theorem
  index — premise_registry.toml (60 entries, 5 classes), fail-closed
  PremiseRegistry.py validator, GenTheoremIndex census (610 modules,
  11273 theorems, 3618 defs; status Proven=532/Cond=23/Emp=11/
  Spec=24/Depr=20; axioms propext/Quot.sound/Classical.choice only,
  idempotent regen committed).
- C362 3f49ac9 `refactor:` prune unused scripts — 9 dead scripts
  deleted (−716 LOC), zero refs, battery untouched.
- C363 e5db50d `feat:` CanonicalTrainState — single-carrier state
  (core + router + quant + trust), `hold_rollback_total` (partial
  rollback unrepresentable), FullStepCert + kernel adapter into the
  C345 CertStepGen kernel.
- C364 c2b3b74 `feat:` CEModel interface — A/R²/next descent contract,
  singleSampleCE + batchCE bridges (statement-level dedup), generic
  strictDescent proved once, instantiated twice.
- C365 3c07045 `refactor:` consolidate duplicate proof ideas — 3
  merges (SoftmaxHead P-AGGREGATE template, StochasticSafeQP noise
  lemmas, ConditionalSuccess log-telescope), −100 LOC dup, honest-keep
  list for non-duplicates.
- C366 2124582 `feat:` DirectionProvider + KKT-certified SafeQP —
  direction-certificate contract, 4 bridges (negGradient, muon
  norm-only, sign, SafeQP), computational KKT residual spec
  (stat/comp/prim ≤ ε ⟹ descent bounds), de-Choosed.
- C367 091c5e9 `feat:` ε_total joint output-space compression error
  — `logit_head_total_error`: ‖D(Wx) − D'(Wqq x)‖ ≤ L(e_svd+e_quant)B
  + e_dec, three stages instantiated, honest pins for absent
  Frobenius→opNorm and scalar→vector lifts.
- C368 38eefbc `refactor:` merge tranche 1, Probability 42→37
  (ThermoBridge ×3, PMFBridge, FiniteBayes).
- C369 1825c5c `refactor:` tranche 2, Ensemble 11→7 (MergePrice ×4).
- C370 221c419 `refactor:` tranche 3, Budget/System/Pretraining
  36→28 (−8; WaterFilling, JointCost, UnifiedStep, SyntheticPretrain).
- C371 e546b80 `refactor:` tranche 4, EnergyReasoning 15→1
  (Pseudolikelihood receiver, 14 appends, 3 external retargets).
- C372 06d5193 `refactor:` tranche 5, −9 more (MirrorHedge ring 7→1
  chain, NewtonSchulz 3→1, EF21 2→1).

## (a) A15 scorecard (user program steps)

- **2.1/2.2 premise registry + theorem index — CLOSED (C361).**
  60 typed premises (1 math, 14 model, 31 empirical w/ measured
  pointers, 11 operational, 3 approximation); fail-closed validator
  + 9 unit tests wired as replicated battery tier; generated index
  committed with drift-visible regeneration contract.
- **2.3 scripts prune — CLOSED (C362).** −9 one-off scripts, each
  deletion doc-claim-verified (AssumptionBinders "consumed by"
  claim was false — deleted on evidence, not vibes).
- **3.1 CanonicalTrainState — CLOSED-contract (C363).** Invariant +
  kernel adapter landed; migration candidates (CRAMState, GrowthState
  consumers, Hagi.Model.*) explicitly pinned as later tranches —
  PARTIAL as a migration program.
- **3.2 CEModel — CLOSED-core (C364).** Contract + 2 bridges +
  payoff demo; GatedCE / NonlinearCE / QuantizedCE pinned as
  migration tranches (honest: different contract shapes).
- **3.3 idea dedup — CLOSED (C365)** for the found duplicates;
  survey's honest-keep list documents why the rest are not dups.
- **4.1 DirectionProvider + KKT SafeQP — CLOSED (C366).** Contract,
  4 bridges, computational KKT certificate; CEModel-family direction
  bridging pinned as tranche.
- **4.2 ε_total — CLOSED-form (C367).** Composition theorem + 3
  stages; Frobenius→opNorm and scalar→vector lifts are pinned-open
  premises (honest partial).
- **4.3 structural consolidation — CLOSED FAR BEYOND PLAN (C368–
  C372).** −40 files, 5 tranches, Freeze identity 7659 throughout,
  full tool-bug ledger captured (see (b)).
- **5.1 nonlinear CE generalization (majorizer remainder-ball →
  CEModel NonlinearCE bridge / convexity beyond log-linear) — OPEN.**
  No beat touched it; C364/C367 only pinned it.
- **5.2 (per program: per-family migration tranches above) —
  PARTIAL**, tracked in module docstring ledgers.
- **5.3 numerical trajectory theorem (explicit-constant trajectory
  bound on the canonical state) — OPEN.** CanonicalTrainState (C363)
  provides the carrier; no trajectory theorem proved on it yet.

Net: A15 is ~80% closed by count; everything remaining is math
(5.1, 5.3) or bounded plumbing (pinned migration tranches).

## (b) CREDO-метрики (деталями)

- **Файлы:** census C361 = 610 modules (ReachLint 609 reachable + 12
  quarantined − overlap). After C368–C372: ReachLint **573 reachable**
  (609 → 608 → 604 → 596 → 582 → 573). Net tracked-file delta from
  merges: **−40** (5+4+8+14+9); every merge FQN-preserving.
- **Freeze:** 7616 (C361 base) → 7626 → 7633 → 7637 → 7656 →
  **7659 (C367)**, then **identity 7659 through all five merge
  tranches** — 0 aliased, nothing lost/changed at every beat.
  Single lock intervention: C371 surgical 16-row private-decl path
  swap (wholesale --update rejected: would bake 235 unlocked decls).
- **Tool-bug ledger (merge_module.py), all reproduced + worked
  around + documented:**
  1. nested-namespace (C370): unclosed receiver namespace ⟹ child
     namespaces nest, FQNs corrupt (Freeze LOST Hagi.Budget.Hagi.*).
     Fix: close receiver namespace pre-append; verify tail each step.
  2. tail-indent (C370): receiver's last line re-indented +2 when
     ending inside a namespace ⟹ tactic drops out of block. Fix:
     restore indentation; check tail every merge.
  3. subset-import (C370): `import Mathlib.Tactic` before
     `import Mathlib` reorders instance elaboration ⟹ Freeze CHANGED.
     Rule: prune redundant subset-imports after union.
  4. append-order-dependency (C372): --append fails when receiver
     body references provider decls (NewtonPolar, EF21Markov) —
     DEFAULT mode (provider before receiver) required; also strip ALL
     child imports from an import hub before first merge (cycle).
  5. (C371, adjacent) path-keyed private decls in declarations.lock
     need surgical row swaps — statements unaffected (stmt hash
     excludes name path).
- **Scripts hygiene:** −9 scripts (C362); ci.sh never edited
  (constraint honored all 12 beats).

## (c) Health

- **Decls 7616 → 7659 (+43)**: C363 +10 (CanonicalTrainState),
  C364 +7 (CEModel), C365 +4 (dedup helpers), C366 +19
  (DirectionProvider/KKT), C367 +3 (TotalError). Merges: +0/−0
  (identity). A15 added exactly the contract/bridge layer, no
  statement duplication (STMDUP 0 groups throughout).
- **Module structure post-merge:** Probability 42→37, Ensemble 11→7,
  Budget 19→15, System 7→6, Pretraining 10→7, EnergyReasoning 15→1,
  Optimization 37→30, Step 39→37. Remaining large dirs: Contracts 55,
  Model 96, Unified, Foundations — repeatedly excluded for import
  fanout (3–15 external importers per small child) or topic
  orphanhood (4 consecutive exclusions of Optimization singles on
  cohesion grounds).
- **Gates:** battery PASS ×12; DupLint/NsLint/DocLint/LayerLint/
  StatusLint/ChallengeCheck 2/2/MachineDiffTest 1923 certified/
  TestMergeModule 20 all green every beat. AssumptionScan: 37 h_emp
  files / 117 identifiers stable since C366 (+1 h_emp_smooth).
  Axioms: propext/Quot.sound/Classical.choice only (regression PASS).

## (d) ГЛАВНОЕ — решение и ranked next

**Decision: merge-кампанию ЗАВЕРШИТЬ.** Five tranches harvested every
clean cluster; the remaining dirs (Contracts 55, Model 96, Step
SafeQP family) are import-dense — the C368–C372 exclusions repeated
the same rationale four times. Marginal ROI of tranche 6 is a filler
beat at best (SafeQP family: fanout 10 retargets for −3..−4 files —
retarget mechanics are proven, but it buys hygiene, not HAGI math).
Structure is no longer the bottleneck; the pinned-open A15 math is.
Return to research beats.

**Ranked next (impact/effort toward HAGI):**

1. **A15 5.1 nonlinear CE generalization (Math beat).** The C350–C360
   convergence stack is log-linear-only; the CEJacobianMajorizer
   remainder-ball (already in repo, frozen) is the exact bridge to a
   nonlinear-head descent/convexity statement — closes a pinned C364
   tranche AND extends the flagship convergence family beyond the
   linear model. All ingredients landed; effort MEDIUM. Best ratio.
2. **5.3 numerical trajectory theorem on CanonicalTrainState.**
   C363 landed the carrier + FullStepCert but no explicit-constant
   T-step trajectory bound (C360's theorem lives on its own state).
   A `fullObjective (θ_T) − f* ≤ c(T)` with discharged constants
   would make the canonical state the SSOT of the end-to-end story,
   not just the invariant story. Effort MEDIUM; composes with #1.
3. **Research queue from C358 (margin-PL, averaged-iterate).**
   Attainment (old #1) and stochastic×PL (old #2) were consumed by
   C359/C360; the next research beats are margin-PL (unregularized
   strong-μ via data geometry — removes the weight-decay crutch;
   effort MED-HIGH, margin geometry not in Mathlib) and
   averaged-iterate LR²/T (cheap fill-in, Fejér + telescope over
   `ce_convex_ident`). Take averaged-iterate as the between-beats
   filler if 5.1 stalls.
4. **Merge tranche 6 (SafeQP family only) — demoted to filler.**
   Fanout 10 (SafeQP 6 + SafeQPStep 6 importers incl. Legacy+Model
   consumers); −3..−4 files. Do only as a low-energy beat; Contracts/
   Model dirs: do not open (fanout + orphanhood, 4× documented).
5. **Semantic Freeze (A14 §4.0) / challenge v5 pin.** Infrastructure;
   schedule as dedicated tooling beats after the math tranches, not
   mixed (same verdict as C358 analysis).

Top-3: **(1) nonlinear CE generalization** — the only route that
widens the flagship convergence family; **(2) trajectory theorem on
CanonicalTrainState** — makes the C363 carrier load-bearing;
**(3) margin-PL from the C358 queue** — honest strong-μ without
regularization.
