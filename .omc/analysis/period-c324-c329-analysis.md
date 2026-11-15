# Analysis of proved: C324–C328 period (2026-11-16, 5 commits C324–C328; health beat C329)

All receipts terminal; gates green at every beat (CI: PASS,
ALLAXIOMS: PASS per-beat logs). Health beat C329 re-verified the
full battery, census, and RootApi at HEAD 634c24d (pre-commit).

## Commit one-liners (C324–C328)

- C324 263d820 `feat:` canary-weight ramp — first Deployment-layer
  module (`Hagi/Deployment/CanaryRamp.lean`, 386 lines, 17 decls):
  `canaryStepLeak` is the C250 `cascade_leak_bound_op` constant form
  VERBATIM; MAIN `canary_linear_ramp_harm` — total canary exposure
  ((T+1)/2)·L·dR·px for the linear ramp; `canary_step_certified`
  (CertStepGen, C322 pattern); Ville monitor premise-form (cites
  C264/C295, import-legal); deployment completion bound.
- C325 c058a8a `feat:` sleeping experts — `Hagi/Learning/
  SleepingRouter.lean` (667 lines, 28 decls): imputed-loss
  reduction (Freund–Schapire share-update); KEY IDENTITY
  `swWeight_eq_ewWeight` (process IS `ewWeight` on imputed losses)
  ⇒ the whole Hedge carrier applies verbatim; MAIN
  `sleeping_hedge_regret` — masked regret log K/η + η·T/2 on
  expert i's awake rounds. Closes the C320 honest gap (open item 1
  of the C323 inventory).
- C326 8bc1741 `refactor:` CREDO pass two — clean-bake instrument
  (committed lock stale by 77 rows) surfaced exactly ONE statement
  duplicate: `rd_stage_product_eps` deleted (canonical
  `quantProd_relError_sq`); lock baked 7261→7338 (+77 drift −1
  twin); KEPT list re-verified with fresh consumer evidence
  (mixture vs ensemble CE, SleepingRouter composition, Hadamard
  import+cite, canary internals all consumed); unused-private scan
  of ALL C313–C325 modules: honest zero. Tracked Lean −16 LOC.
- C327 1ea5c74 `feat:` continual forgetting — `Hagi/Learning/
  ContinualForgetting.lean` (311 lines, ns +.Anchor): TWO-CHANNEL
  contract. Audit channel `continual_forgetting_bound` (C264 gate
  at the SPENT δ, sharper than C274's δtotal) + δ-split arithmetic
  `auditSpendChain_delta_split`; construction channel
  `floorsKept_trajectory` (CertStepGen FloorsKept field law, free);
  THE contract `floor_floor_telescope`. +2 triviallint_baseline
  rows (documented UNUSED_PARAM shape, same as existing entries).
- C328 634c24d `feat:` certified low-rank sparse inference —
  `Hagi/Contracts/SparseInferenceCert.lean` (356 lines):
  `sparse_inference_error` (premise-form mask error ⇒ sens·tail^½
  readout change via C300/C322 Lipschitz-transfer; EY lower-bound
  adversarial catch corrected to premise-form),
  `sparse_mask_minimal` (Eckart–Young cited verbatim), op-count
  family (denseMatVecWork n² vs lowRankMatVecWork 2kn),
  `sparse_step_certified` — FIRST FLOP accounting spent through
  the CertStepGen budget channel. Honest scope: spectral only;
  unstructured masks NP-hard (Natarajan 1995), acknowledged not
  formalized; negatives RootApi-verified absent.

## Milestones

1. **Deployment layer born (C324)** — first `Hagi/Deployment/`
   module: the certified-rollout surface (canary ramp harm bound +
   completion) now has a home; C250 leak + C264/C295 e-process
   composed, nothing new invented.
2. **Router story complete (C325)** — the C319/C320/C325 chain now
   spans calibration → always-available regret → sleeping/specialist
   regret; the C320 honest gap (open inventory item 1) is CLOSED.
3. **CREDO-2 discipline (C326)** — the clean-bake instrument
   (quarantined since C299) executed for the first time on the
   full C313–C325 growth: 1 duplicate found+deleted, honest zero
   elsewhere, drift baked under the C299 precedent policy.
4. **Continual-learning contract (C327)** — first two-channel
   (construction + audit) contract in the Learning layer; the
   audit channel is SHARPER than its C274 source (spent-δ gate).
5. **Certified compute savings (C328)** — first FLOP-count budget
   spend in the kernel: compression certificates now account
   compute, not just error — the seed of the total-compute story.
6. **Layer growth is meaningful, not duplicative** — 3 new modules
   in 3 distinct layers (Deployment 5, Learning, Contracts); STMDUP
   0 groups at every beat + CREDO-2 sweep zero (after 1 delete);
   DupLint/Freeze clean throughout.

## Open items inventory (refresh)

1. ~~Sleeping-experts regret gap~~ — CLOSED by C325
   (`sleeping_hedge_regret`; TD entry in tech-debt.md updated).
2. Mixed-logit mixture: logit-mixture vs distribution-mixture
   different objects (C319 challenge-pins); MIXED treatment
   excluded by design — unchanged.
3. E6 stream bridge (full read-stream equivalence) — deferred,
   unchanged.
4. Joint analytic convergence of alternating rounds — pinned;
   tolerance-based rounds remain (C262/C293) — unchanged.
5. Matrix NS general (non-iterative forms) — Mathlib upstream,
   out of scope — unchanged.
6. P0 reproducibility infra — user-env dependent, parked.
7. Discovery/inductive span-synthesis — out of scope by design —
   unchanged.
8. E5 degree API + typed context signatures — open, no consumer
   pressure — unchanged.
9. Rectangular spectral-tail bridge (C328): the square-case
   `frobenius_error_truncatedSVD` does not transport to rectangular
   masks until the C232/C281 root-sorting gap closes — NEW this
   period (premise-form hE carried instead).
10. Unstructured/entrywise sparsity: optimal mask NP-hard
    (Natarajan 1995) — honest boundary, NOT claimed (C328);
    a greedy/iterative-pruning bound would be a fresh research
    beat (see ranking (a)).
11. Ville monitor (C324 `canaryVilleMonitorHold`) is premise-form
    (cites C264/C295 without import — Unified 6 > Deployment 5):
    a bridge module would be needed to consume it — low priority.

## Health check (C329, logs in .tmp/C329/)

- **Build**: PASS (`lake build` "Build completed successfully",
  9655 jobs — no Lean changes since C328, no-op rebuild expected).
- **Full battery CI: PASS** (battery.log, ci.sh NOT run —
  run-battery.sh replication): REACHLINT (595 modules reachable),
  TRIVIALLINT, TRIVIALITY (flags: 0), MATHLIBPIN, DUPLINT (0),
  NSLINT (0), DOCLINT, LAYERLINT, FREEZE verify (7371 declarations,
  0 aliased, nothing lost/changed), ASSUMPTIONSCAN (36 h_emp files,
  116 occurrences), MERGEMODULE (20 tests, Lean modes=2),
  STATUSLINT, CHALLENGE 1/1, STMDUP (0 groups — C326 baked lock
  holding), MACHINEDIFF (2000 configs; 1923 certified),
  ALLAXIOMS: PASS + regression PASS — **CI: PASS**.
- **Census HEAD vs C328 receipt** (census.log): ROOT_CENSUS_OK
  modules=557 main=13993 extra=1775 duplicate_main=0
  unique_global_mismatches=0 consumers=39 intrinsic_nodes=411
  source_fingerprint=1464754235333493995, git_head=634c24d —
  metrics and fingerprint BYTE-IDENTICAL to the C328 landed census
  (expected: no Lean changes since C328).
- **RootApi spot** (rootapi.lean, rootapi.log exit 0): 14/14
  period-public names #check OK through the Hagi root
  (Deployment.CanaryRamp, Learning.SleepingRouter, Budget.RDAlloc,
  Learning.ContinualForgetting, Contracts.SparseInferenceCert).
- **TD audit**: sleeping-experts gap entry added CLOSED (C325).
  Canary (C324) and sparse (C328): NO TD entries needed — receipts
  + STATUS carry honest scope inline; their deferrals are inventory
  items 9–11 above, not tech debt (DRY/Zawinski). C327's
  triviallint_baseline +2 is the documented baseline mechanism
  (UNUSED_PARAM, existing shape) — debt recorded by the mechanism
  itself, no TD row.
- **Growth accounting** (C323→C328, a09bb508..634c24d): 8 files,
  +1900/−29. Lean net ≈ +1725 (4 new modules: CanaryRamp 386,
  SleepingRouter 667, ContinualForgetting 311, SparseInferenceCert
  356; RDAlloc −19 CREDO-2); docs +173 (STATUS), +2 baseline rows.
  Census main 13823 → 13993 (**+170 main decls, +4 modules
  553→557**; C326 deleted 1 dup). Meaning-per-line verdict: all
  growth is NEW capability (deployment rollouts, sleeping regret,
  continual contract, FLOP accounting) — corroborated by STMDUP 0,
  DupLint 0, Freeze 0 lost/changed, and the CREDO-2 sweep's honest
  zero. No duplicative growth flagged.

## Next-track ranking (cost/benefit)

1. **(c) Training-compute certificate — total-compute-to-quality**
   — MEDIUM cost, HIGHEST benefit: composes two LANDED carriers
   (C291 descent rate: steps-to-ε from the certified drop; C328
   FLOP accounting: per-step budget spend) into the repo's first
   end-to-end "compute spent ⇒ quality reached" theorem — exactly
   the GOAL's минимизация вычислений, in-repo, minimal research
   risk (both ingredients proved; the composition pattern is the
   C322/C324/C327 CertStepGen telescope). Rank 1.
2. **(b) KV-cache / memory-bound inference certificate** — MEDIUM
   cost, HIGH benefit: extends C328's compute accounting from
   matvec FLOPs to attention inference over sequence length
   (cache-size and per-token cost model; C307 attention carriers
   are the natural premise source). Moderate novelty (sequence-
   length accounting is new surface) but premise-form routes
   exist. Rank 2.
3. **(a) Unstructured-sparsity honest route (magnitude/iterative
   pruning bound)** — HIGH cost, UNCERTAIN benefit: optimal masks
   NP-hard (pinned C328); a greedy/iterative magnitude-pruning
   ERROR BOUND is not a standard formalizable result — genuine
   research risk (needs a literature pass + likely fresh proof
   shape). Only after (c)/(b) land. Rank 3.
   Parked: (d) P0 reproducibility — env-blocked, unchanged.
