# Analysis of proved: C330–C334 period (2026-11-16, 4 commits C330–C334 incl. analysis beat C332; health beat C335)

All receipts terminal; gates green at every beat (CI: PASS,
ALLAXIOMS: PASS per-beat logs in .tmp/C330–C334). This health beat
(C335) re-verified build, Freeze, TrivialLint, census, RootApi,
clean-bake STMDUP, and the full battery at HEAD 8a49362
(pre-commit).

## Commit one-liners (C330–C334)

- C330 d943d47 `feat:` total compute to quality —
  `Hagi/Contracts/ComputeToQuality.lean` (230 lines): first
  end-to-end COMPUTE certificate — `steps_to_quality` (uniform
  certified descent d/step ⇒ objective ≤ ε in ⌈Δ₀/d⌉ steps),
  `total_compute_to_quality` + `totalComputeProduct` (total =
  steps × per-step FLOP, honest premise-form minimality),
  `lowrank_total_compute_le` (low-rank vs dense total tradeoff),
  `compute_budget_certificate` (resource ledger telescoping
  EXACTLY) + 4th kernel telescope `budget_telescope_gen`
  (CertStepGen).
- C331 28e9fae `feat:` KV cache incremental attention certificate
  — `Hagi/Contracts/KVCacheCert.lean` (499 lines): additive
  (den,num) accumulators decompose exactly (softmax weights do
  not); `kv_cache_exact` (cached = recompute EXACTLY), lse layer,
  division-free work model (recompute cubic vs cached quadratic),
  `kv_work_ratio` (exact 3R=(n+2)W), `kv_step_certified` zero-risk
  (first ZERO-error certificate: exactness spends 0 risk).
- C332 b328bcc `chore:` phase analysis c330 c332 + docs sync —
  period analysis, ALGORITHMS.md/STATUS.md sections, health check
  (census byte-check vs C331, Freeze 7419 PASS, clean-bake STMDUP
  spot-check that CAUGHT the C328 restatement twin — spun to C333).
- C333 becda4c `fix:` dedup sparse mask twin + bake —
  `sparse_mask_minimal` deleted (verbatim twin of C281
  `eckart_young_lower_bound_rect_true_tail`, 0 consumers);
  FULL BAKE 7338→7419 (+81 drift, verified-clean by C332
  clean-bake; STMDUP PASS 0 groups post-bake); net −8 LOC;
  StatusLint kept honest via canonical re-pointing.
- C334 8a49362 `feat:` data efficiency samples-to-quality
  certificate — `Hagi/Contracts/DataToQuality.lean` (264 lines,
  6 decls): `sampleComplexity` + `concConfidence_le_of_sample_
  bound` (EXACT inversion of the C287 radius: n ≥ log(m/δ)/(2η²)
  ⟹ concConfidence η n ≤ δ/m), `samples_to_quality` (finite class
  + C315 margin ⇒ empirical winner is population-best w.p. ≥ 1−δ
  at m = 2|ι| union multiplicity), `data_compute_budget` (joint
  data+compute ledger), anchor ≈300 samples ≤ 450.

## Milestones

1. **ALL THREE resource axes of the goal now have end-to-end
   theorems.** Compute: per-step FLOP (C328) × steps-to-ε (C330) ×
   inference serving cost (C331 exact 3R=(n+2)W) with the
   low-rank tradeoff (C330). Data: samples-to-quality (C334,
   C287+C315 composed, no new probability mathematics). Volume:
   compression certificates (C321 rate–distortion step, C322
   CertStepGen kernel). The C334 `data_compute_budget` unifies the
   data book (selection event) and the compute book (objective ≤
   ε) into one resource ledger — the goal «максимальное качество
   при минимальном объёме и вычислениях» in theorem form: quality
   target, sample budget, and FLOP budget on one telescoping
   certificate.
2. **Instrument truth restored (C332→C333).** The C332 clean-bake
   spot-check caught the one twin the stale lock hid; C333
   deleted it and baked the lock 7338→7419. C334 baked to 7424;
   this beat's clean-bake is BYTE-IDENTICAL (zero drift since
   C334) — the audit instrument (STMDUP) now sees the real tree.
3. **Certificate pattern covers exact and approximate regimes**
   (C331 zero-risk exactness; C328 error spend) and the kernel
   telescopes drop/delta/risk/budget (C330 4th telescope).
4. **Layer discipline held** — new modules in Contracts only
   (C330/C331/C334); no statement changes anywhere in-period
   (Freeze zero lost/changed at every beat).

## Open items inventory (refresh at C335)

1. Mixture-of-depths certified routing cost — NOT started; the
   natural next track (see ranking): C325 sleeping-router (WHO
   computes) × C328/C331 work models (WHAT it costs) × C300 stack
   leak (early-exit error tail).
2. Training-data curriculum — not started, research-first (needs
   per-phase descent-rate premise shape on C291/C330).
3. Unstructured/entrywise sparsity — NP-hard optimal masks
   (Natarajan 1995), honest boundary, parked.
4. P0 reproducibility infra — user-env dependent, parked.
5. E5 stream: compose3 degree API + typed context signatures — no
   consumer pressure, unchanged (TD E5-C301/C302 stay OPEN,
   seeded).
6. E4 residues: per-instance gate families beyond tanh (C313
   covered μg=1, ident-logit Lc=2) — unchanged.
7. Mixed-logit mixture, E6 bridge, joint analytic convergence of
   alternating rounds, matrix NS general (Mathlib upstream),
   discovery/inductive span-synthesis, Ville monitor premise-form
   bridge — all unchanged (period analyses C313–C329).
8. Rectangular spectral-tail bridge (C232/C281 root-sorting gap)
   — unchanged; no new exposure in-period.
9. Muon fully-general hP-free statement — SVD premise + iterate
   lifting remain open (TD A8-F6-C254 partial close at C297).

## Health check (C335, logs in .tmp/C335/)

- **Census HEAD vs C334 receipt** (census.log): ROOT_CENSUS_OK
  modules=560, main=14095, duplicate_main=0,
  unique_global_mismatches=0, source_fingerprint
  824609291486838882 — IDENTICAL to the C334 landed census (only
  git_head differs: 8a49362 vs becda4c, expected — no Lean change
  since the C334 commit tree).
- **Freeze verify**: PASS — 7424 declarations, 0 aliased, nothing
  lost/changed (lock baked at C334; no drift).
- **Clean-bake STMDUP spot-check**: fresh `Freeze.py --update`
  writes 7424 — BYTE-IDENTICAL to the committed-work-tree lock
  (zero un-baked drift since C334); StatementDupCheck PASS
  (0 groups). Lock needed no restore (identical).
- **TrivialLint**: new: 0, LINT: PASS. **RootApi spot**: 0 errors
  (all 6 DataToQuality names + carriers
  finite_class_pl_margin_argmax, concConfidence,
  total_compute_to_quality resolve through the Hagi root).
- **TD audit**: no tech-debt rows OPENED in C330–C334; standing
  rows are pre-period (E5 seeds, Math-layer unification deferrals,
  Muon residue) — audit note appended (.omc/tech-debt.md).
- **Full battery 1×**: see receipt (CI: PASS, ALLAXIOMS: PASS).

## Next-track ranking (C336 candidates)

1. **Mixture-of-depths certified routing cost** — MEDIUM cost,
   HIGH benefit, LOW research risk: per-token depth selection with
   early-exit certificates (exit-at-layer-k error ≤ tail bound).
   The C300 stack leak gives EXACTLY the needed composition
   primitive: the residual cascade bound (∏(1+μᵢ)−1)·‖dx‖ is the
   error tail of truncating the stack at layer k; multiply by the
   C328/C331 work model for the saved-FLOP side and route through
   the C325 sleeping-router for WHO exits. All carriers landed;
   cheap composition, fresh axis (adaptive per-token compute).
   Rank 1.
2. **Training-data curriculum** — MEDIUM-HIGH cost, MEDIUM
   benefit: ordering premise + same-total-steps theorem on
   C291/C330. Needs a per-phase descent-rate premise shape (new
   surface); research-first mini-beat (like C334's probe.lean
   inversion) before any module. Rank 2.
3. **Unstructured sparsity greedy bound / P0 reproducibility** —
   both parked: NP-hard optimal-mask boundary pinned; P0 blocked
   on user env. Revisit only if a cheap literature path appears.

So: the unified resource ledger is complete; the next marginal
theorem-per-cost is adaptive-depth routing on landed carriers.
