# Analysis of proved: C330–C332 period (2026-11-16, 2 commits C330–C331; analysis+docs beat C332)

All receipts terminal; gates green at both beats (CI: PASS,
ALLAXIOMS: PASS per-beat logs in .tmp/C330, .tmp/C331). This beat
(C332) re-verified census, Freeze, and ran the clean-bake STMDUP
spot-check at HEAD 28e9fae (pre-commit).

## Commit one-liners (C330–C331)

- C330 d943d47 `feat:` total compute to quality —
  `Hagi/Contracts/ComputeToQuality.lean` (230 lines): first
  END-TO-END compute certificate — `steps_to_quality` (MAIN 1:
  uniform certified descent d/step ⇒ objective ≤ ε in
  n = ⌈Δ₀/d⌉ steps, premise-form interface to C291),
  `total_compute_to_quality` + `totalComputeProduct` (MAIN 2:
  total = steps × per-step FLOP, honest premise-form step
  minimality caught by probe), `lowrank_total_compute_le`
  (compression tradeoff: if compressed descent d' ≥ d and
  2k ≤ n, low-rank ideal total (Δ₀/d')·2kn beats dense
  (Δ₀/d)·n²), `compute_budget_certificate` (MAIN 3: resource
  ledger — quality reached + budget telescopes EXACTLY), plus the
  missing `budget_telescope_gen` (4th kernel telescope: budget
  identity, now in CertStepGen).
- C331 28e9fae `feat:` KV cache incremental attention
  certificate — `Hagi/Contracts/KVCacheCert.lean` (499 lines,
  ns + .Anchor): route (b) additive accumulators — softmax
  weights do NOT decompose, the (den,num) pair of plain sums
  DOES; `kv_cache_exact` (MAIN 1: cached = full recompute
  EXACTLY on List carrier), lse layer (`lseCombine` associative
  exactly, `lse_cache_step` running logsumexp), division-free ℕ
  work model (`cached_total_work_eq` 2W=n(n+1) quadratic,
  `recompute_total_work_eq` 6R=n(n+1)(n+2) cubic,
  `kv_work_ratio` (MAIN 2): exact 3R=(n+2)W, `kv_total_work_lt`
  (MAIN 3): strict for n ≥ 2), `kv_step_certified` packaging
  (risk channel spends ZERO — exactness ⇒ error 0;
  assumptions.lock +1 primitive `lseCombine`, gate-ordered).

## Milestones

1. **The compute-certification arc is COMPLETE end-to-end** —
   per-step FLOP (C328) + steps-to-ε (C330) + inference cost
   (C331) + compression tradeoff (C330 `lowrank_total_compute_
   le`): the GOAL axis «минимизация вычислений» now has theorems
   spanning training compute (descent × FLOP), inference serving
   (cache vs recompute, exact ratio), and their tradeoff
   (low-rank total vs dense total). No other GOAL axis has this
   coverage.
2. **CertStepGen kernel completed (C330)** — the 4th telescope
   (`budget_telescope_gen`): the kernel now telescopes
   drop/delta/risk AND budget; ComputeToQuality/KVCacheCert are
   pure compositions on it (nothing new invented, per the
   C322/C324/C327/C328 pattern).
3. **First zero-error certificate (C331)** — `kv_step_certified_
   zeroError`: exactness spends 0 risk; the certificate pattern
   now covers both approximate (C328 error spend) and exact
   (C331 zero spend) regimes.
4. **Layer discipline held** — 2 new modules in Contracts only;
   STMDUP 0 groups at both beats (committed-lock view), DupLint
   0, Freeze 0 lost/changed; honest-boundary paragraphs +
   rootapi-negatives at both beats.

## Open items inventory (refresh)

1. **NEW (urgent, C333 candidate)**: clean-bake STMDUP (this
   beat, .tmp/C332/) found ONE statement duplicate invisible to
   the committed-lock STMDUP: `sparse_mask_minimal` (C328)
   verbatim-restates `eckart_young_lower_bound_rect_true_tail`
   (GradientBottleneckIdentification carrier). Same shape as the
   C326 `rd_stage_product_eps` delete; the local declarations.lock
   was stale (baked C326) so C327–C331 beats could not see it.
   Fix: delete alias in a Lean beat, bake lock.
2. Mixed-logit mixture — different objects, excluded by design —
   unchanged.
3. E6 stream bridge — deferred, unchanged.
4. Joint analytic convergence of alternating rounds — pinned —
   unchanged.
5. Matrix NS general — Mathlib upstream, out of scope — unchanged.
6. P0 reproducibility infra — user-env dependent, parked.
7. Discovery/inductive span-synthesis — out of scope by design.
8. E5 degree API + typed context signatures — no consumer
   pressure — unchanged.
9. Rectangular spectral-tail bridge (C232/C281 root-sorting gap)
   — unchanged; C330's `lowrank_total_compute_le` relies on the
   square-case condition only (2k ≤ n), no new exposure.
10. Unstructured/entrywise sparsity — NP-hard optimal masks
    (Natarajan 1995), honest boundary — unchanged (see ranking).
11. Ville monitor premise-form bridge (Unified 6 > Deployment 5)
    — low priority, unchanged.

## Health check (C332, logs in .tmp/C332/)

- **Census HEAD vs C331 receipt** (census.log): byte-check PASS —
  metrics + source_fingerprint IDENTICAL to the C331 landed
  census (expected: no Lean changes since 28e9fae).
- **Freeze verify**: PASS (7419 declarations, 0 aliased, nothing
  lost/changed).
- **Clean-bake STMDUP spot-check**: fresh lock 7338→7419 rows
  (+81: ContinualForgetting C327 + SparseInferenceCert C328 +
  ComputeToQuality C330 + KVCacheCert C331); fresh-lock
  StatementDupCheck flags exactly ONE duplicate group (open item
  1 above). Stale lock restored byte-identical afterwards
  (untracked local cache; committed state unaffected). The +74 KV
  names specifically: 0 duplicates among them — the catch is a
  C328 restatement, not a KV name.
- Full battery re-run this beat: see receipt (CI: PASS,
  ALLAXIOMS: PASS).

## Next-frontier ranking (cost/benefit)

1. **Data-efficiency / sample-complexity certificates** — MEDIUM
   cost, HIGH benefit: the repo's Hedge/regret carriers (C321/C325)
   + concentration inventory are the natural premise source for
   «quality reached per sample» theorems; pairs with the compute
   arc into a compute-vs-data frontier. Fresh axis, in-repo
   ingredients, moderate research risk. Rank 1.
2. **Mixture-of-depths certified routing cost** — MEDIUM cost,
   HIGH benefit: composes C325 sleeping-router (who computes) with
   C328/C331 work models (what it costs) into per-token certified
   routing savings; both carriers landed. Rank 2.
3. **Training-data curriculum** — MEDIUM-HIGH cost, MEDIUM
   benefit: sequencing-dependent descent composition on
   C291/C330; needs a per-phase descent-rate premise shape (new
   surface, honest-premise style). Rank 3.
4. **Unstructured sparsity (greedy/iterative pruning bound)** —
   HIGH cost, UNCERTAIN benefit: NP-hard optimal masks pinned
   (C328); a greedy magnitude-pruning ERROR bound is not a
   standard formalizable result — genuine research risk, needs a
   literature pass. Rank 4 (unchanged).
   Parked: Muon general spectral — Mathlib upstream, unchanged;
   P0 reproducibility — env-blocked, unchanged.
   Precondition for ANY new Lean beat: open item 1 (dup delete +
   lock bake) first — the audit instrument must see the truth.
