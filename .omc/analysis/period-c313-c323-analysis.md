# Analysis of proved: C313–C323 period (2026-11-15, 9 commits C313–C322 + 1 untracked beat C316)

All receipts terminal; gates green at every beat (CI: PASS,
ALLAXIOMS: PASS per-beat logs). Health beat C323 re-verified the
full battery, census, and RootApi at HEAD 88163f5 (pre-commit).

## Commit one-liners (C313–C322)

- C313 b212bcc `feat:` E4 premise discharge — μg (gdnGateTanh_lipschitz,
  tanh-family, μg = 1) + P7 (fastarch3_head_Lc, ident-logit headCE,
  Lc = 2); premise ledger v2 (`.tmp/C313/premise-ledger-v2.md`).
- C314 ef4957a `feat:` E5 final dispatch rung — multi-candidate
  PRIORITY dispatch (`dispatchPriority` + `_sound`/`_shadow`/
  `_agree_sound`); overlap resolved by ORDER, honest shadowing;
  C306-abstention and C314-priority semantics coexist by design.
- C315 600c27a `feat:` P4 frontier — two-tier generalization for
  learned energies: `finite_class_pl_uniform` (uniform convergence
  of PL-loss over a FINITE Fintype class, C264-union ∘ C287
  concRadius) + `finite_class_pl_margin_argmax` (identification);
  `learned_solver_correctness_exact` — accepted-solver validity
  NEVER depends on generalization (correctness quarantined from
  efficiency).
- C316 (UNTRACKED, `.tmp/C316/`) — Python CRAMExpert reference
  mirror: numpy-only reference of the energy/pl/alternating
  pipeline; every cited Lean FQN existence-checked; mirror-fidelity
  table NO DISCREPANCIES; report is the receipt, no commit by
  design (TD A5-R5-C241 note unchanged).
- C317 323e57b `feat:` E6 remaining rungs — RAM span offsets
  (`ramSpanAddr`/`ramLoadSpan`, mod-carry in Fin m; roundtrip /
  within / no-wrap) + access-gate separation (`RamAccess`:
  `ram_access_gate_sound` — gate only filters, never fabricates;
  `ram_access_selection_free` — selection pure).
- C318 bad978a `docs:` phase sync — STATUS/ALGORITHMS/tech-debt
  sections for C313–C317 consolidated (E4 ladder closed, E5
  dispatch path closed, E6 core closed).
- C319 db8d348 `feat:` soft routing — audit §7 (T): logit-mixture
  calibration `soft_router_ce_bound` (weighted Jensen for lse,
  Hedge-simplex weights) + distributional side
  `mixture_ce_le_weighted_avg`; negative anchors `hard_wrong_full_price`
  (CE = log(e²+1) ≈ 2.13) vs `soft_beats_hard_wrong` (½/½ mixture
  CE = log 2) — strict calibration win of soft over hard-wrong.
- C320 ed67f6d `feat:` audit §7 router end-to-end — Hedge regret
  carrier (`router_regret_bound` + `hsurv_derived`) composed with
  C319: `soft_router_total_bound` — T-round soft-mixture CE ≤ any
  single expert + log N/η + η·T/2. Honest pins: CE ≤ 1 premise,
  Fin N universe, NO sleeping-experts regret claimed.
- C321 b36cfa4 `feat:` audit A10 §9 p.5 — Hadamard AVERAGE-CASE
  quantizer error: deterministic formalization (energy premise,
  not measure theory) — `hadamard_spread_bound` (Parseval),
  `hadamard_large_coord_count_le` (Markov counter),
  `hadamard_ternary_error_bound` (MAIN) + conditional ρ-form;
  ρ < 1 is a PREMISE (`hadamard_not_universally_incoherent` pins
  why); ≈0.106/≈0.33 only in docstrings.
- C322 88163f5 `feat:` audit §7 p.7 — RD step certificate
  composition: `RDAlloc` (premise-form budget allocation,
  water-filling CITED from C237), `rd_step_error_bound` (C253
  additive two-stage law ∘ C252 sensitivity, premise-form),
  `rd_step_certified` (the compression step AS CertStepGen, C278;
  free riskRem per C254; LossCeiling polarity C267).

## Milestones

1. **E4 ledger 4-discharged** — P3 μn (C309), P4 rope (C308), P5
   μg (C313), P7 Lc (C313): the C311 assembly's per-instance
   residue is now theorems; remaining ledger rows are lived-with
   by design (P1 softmax-map, P6 doubly-stochastic, P8/P9
   per-instance/structural premises).
2. **E5 closed as DISPATCH PATH (two dispatchers)** — C306
   collision-abstention + C314 priority-with-shadowing coexist;
   `dispatch_two_eq_priority` bridges them. Still open in E5
   (explicitly, not dispatch): degree API, typed context
   signatures; argument-range MODEL frozen exact-match (subset
   reading refuted by counterexample).
3. **E6 core closed** — C303 store/load + stutter + C317 span
   offsets + selection/gate separation; RAM protocol is now a
   certified address-window model. Stream bridge (full
   read-stream equivalence) remains deferred.
4. **Two-tier generalization (C315)** — the P4 frontier opened:
   uniform convergence + argmax identification over finite
   classes, with the correctness/efficiency split pinned
   (`learned_solver_correctness_exact` — generalization failure
   can never produce an invalid accepted solution).
5. **C316 Python mirror, no discrepancies** — CRAMExpert reference
   validates carrier-level fidelity of the Lean formalization
   (every Python op mapped to an existing theorem-carrying FQN).
6. **Soft routing end-to-end (C319+C320)** — calibration
   (mixture CE ≤ weighted expert CE) composed with regret (Hedge
   survivor) into `soft_router_total_bound`: competitiveness with
   any single expert in hindsight. Honest gap: sleeping-experts
   regret NOT claimed (below).
7. **Hadamard average-case (C321)** — audit's ≈0.33 vs worst
   α≈0.106 story formalized deterministically; spread premise ρ
   isolated as premise with a refutation anchor for the
   universal reading.
8. **RD-step certified (C322)** — the slow loop's compression step
   is now a CertStepGen with byte/risk/delta channels.
9. **HAGI-Loop: all three loops have certified transitions** —
   fast proposal loop (premise-discharge beats), medium gate loop
   (CertStepGen carriers: C278, C322), slow consolidation loop
   (RD composition + LossCeiling polarity): every loop transition
   now carries a landed certificate.

## Open items inventory (refresh)

1. Sleeping-experts regret gap (C320 honest pin): bundle holds vs
   any always-available single expert; awake-only/specialist
   regret (Adaptive-Regret / fixed-share) NOT formalized.
2. Mixed-logit mixture: logit-mixture vs distribution-mixture are
   different objects (C319 challenge-pins); a MIXED treatment
   (logit mixture of distributions) excluded by design, not by
   theorem.
3. E6 stream bridge: full equivalence of read streams over repeat
   addresses — deferred rung.
4. Joint analytic convergence of alternating rounds: pinned
   (tolerance-based rounds remain; C262/C293 carry per-phase
   contraction/nonincreasing).
5. Matrix NS general (non-iterative/recurrent forms) — Mathlib
   upstream dependency, out of repo scope (C296/C297 closed the
   hP debt for the iterative form).
6. P0 reproducibility infra — user-env dependent.
7. Discovery/inductive span-synthesis (Python, inductive) — out of
   scope by design (C317 honest boundary).
8. E5 degree API + typed context signatures — open rungs, low
   priority (no consumer pressure).

## Health check (C323, logs in .tmp/C323/)

- **Build**: PASS (battery.log, LAKE build step "Build completed
  successfully"; no Lean changes since C322 — expectation: no-op
  rebuild, confirmed).
- **Full battery CI: PASS** — ReachLint (553 modules reachable),
  TrivialLint, triviality (flags: 0), Mathlib pin, DupLint (0),
  NsLint (0), DocLint, LayerLint, Freeze (7294 declarations, 0
  aliased, nothing lost/changed), AssumptionScan (36 h_emp files,
  116 occurrences), MergeModule (20 tests), StatusLint,
  ChallengeCheck 1/1, MachineDiff (2000 configs; 1923 certified,
  77 outside ledger premise), STMDUP (0 groups) — **CI: PASS**;
  **ALLAXIOMS: PASS** (+ regression PASS).
- **Census HEAD vs C322 receipt**: ROOT_CENSUS_OK modules=553
  main=13823 extra=1736 duplicate_main=0 unique_global_mismatches=0
  consumers=39 intrinsic_nodes=408
  source_fingerprint=8225701121805148847, git_head=88163f5 — TSV
  sha256 116f0a47… byte-IDENTICAL to the C322 landed census
  (expected: no Lean changes between C322 and this beat).
- **RootApi spot**: 14/14 period-public names #check OK
  (rootapi.log, exit 0) — GDNTransfer/FastArch3Transfer/AnfDispatch/
  EnergyClassGeneralization/RamProtocol/SoftRouterMix/SoftRouterTotal/
  HadamardSpread/RDAlloc namespaces all exported through Hagi root.
- **TD audit**: one stale entry FIXED at this beat — TD E5-C301
  still listed "(5) multi-candidate priority dispatch" as open
  although C314 landed it (E5-C306 already cross-references C314);
  E5-C301 now cross-references TD E5-C306/C314. All other entries
  consistent with receipts (E4-C300 CLOSED wording + C313
  discharge note; E5-C302 remaining ladder accurate; A12 ledger
  accurate).
- **LOC/decl growth accounting** (C312→C322,
  `git diff 32961cc..88163f5`): 13 files, +2156/−24; Lean
  +1863 net (8 new modules: EnergyClassGeneralization 205,
  SoftRouterMix 284, SoftRouterTotal 269, HadamardSpread 336,
  RDAlloc 269, RamProtocol +127, AnfDispatch +221, transfers
  +~250); docs +269 net (STATUS/ALGORITHMS sync, C318 −54/−...).
  Census main declarations 13681 (C312) → 13823 (C322): **+142
  main decls (+5 modules: 548→553)**. Meaning-per-line verdict:
  additions are NEW capabilities (dispatch semantics, RAM windows,
  generalization tier, router calibration/regret, Hadamard
  average-case, RD step packaging) — corroborated by STMDUP 0
  groups, DupLint 0 groups, Freeze 0 lost/changed. No growth
  flagged as duplicative.

## Next-track ranking (cost/benefit)

1. **(b) Canary-weight ramp certificate** — MEDIUM cost, HIGH
   benefit: composes EXISTING carriers (C250 CascadeLeak
   `Hagi/Architecture/CascadeLeak.lean` + e-process/CertStepGen
   monitoring) into the audit §7 canary-acceptance theorem (route
   weight w continuous, canary ramp 0→1, leak linear in w). Pure
   composition risk like C322; no new math expected. Rank 1.
2. **(a) Sleeping-experts regret** — MEDIUM-HIGH cost, HIGH
   benefit: fills C320's honest gap, upgrades the router bundle
   from "any single expert" to "best sequence of awake experts"
   (Adaptive-Regret / fixed-share). REQUIRES a research beat
   first (fixed-share analysis is not in the repo; may need fresh
   proof or careful premise-form restatement). Rank 2 — start
   with a research beat (ask.sciencemadereadable.com / literature
   pass) before committing to a proof shape.
3. **(d) CREDO pass 2** — LOW cost, MEDIUM benefit: the repo has
   grown +142 decls since A12 exhausted statement-level dedup
   (C304/C305); a fresh dedup sweep (STMDUP + consumer evidence)
   is cheap insurance against drift in the new modules. Rank 3 —
   good filler beat between (b)/(a).
   Deferred: (c) fresh research frontier (continual-learning
   bounds / sparsity-certified inference) — HIGH cost, uncertain
   fit; revisit after (a) closes the router story.
