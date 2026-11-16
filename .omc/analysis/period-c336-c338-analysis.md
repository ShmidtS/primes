# Analysis of proved: C336–C338 period (2026-11-16, 3 commits: C336, C337, health/analysis beat C338)

All receipts terminal; gates green at C336 and C337 (CI: PASS,
ALLAXIOMS: PASS per-beat logs in .tmp/C336, .tmp/C337). This beat
(C338) re-verified build, Freeze, TrivialLint, census, RootApi,
full battery 1× at HEAD ce6a165d (pre-commit), plus the env-
unblocked half of the parked P0 reproducibility item.

## Commit one-liners (C336–C337)

- C336 6d4eea0 `feat:` certified early-exit depth routing —
  `Hagi/Contracts/DepthExitCert.lean` (240 lines, 16 decls):
  the Mixture-of-Depth exit error is ≤ `Σᵢ bᵢ·∏_{j>i}(1+μⱼ)`
  (`exitLeak` + Σ-form `exitLeak_eq_sum`, residual-magnitude
  premise route via `resStack_skip_le`; the bound needs NO
  Lipschitz premise — μ enters only as after-gain weights);
  head-at-exit transfer `early_exit_error_bound` (C311 style);
  exact work ledger `early_exit_work` (prefix+tail = full, C328
  count model); two-sided per-token `early_exit_certificate`
  (routing is a premise; no optimality/load-balancing claim).
- C337 ce6a165 `feat:` curriculum phase accounting with
  dependency chains — `Hagi/Contracts/CurriculumCert.lean`
  (215 lines, 8 public + aux = 24 Freeze names): order-free
  NEGATIVE result — phase-rate accounting totals the SYMMETRIC
  sum `n₁·d₁ + n₂·d₂` (`curriculum_phase_accounting`;
  `curriculumTotal_comm`, swap corollary), so ordering per se is
  NOT certified to matter in the sum decomposition; order IS
  constitutive in `curriculum_dependency_chain` (phase-2 drop
  premise CONDITIONAL on the phase-1 endpoint, discharged by the
  C330 certificate; phase 2 telescopes from `t n₁`). Reversed
  order = UNCERTIFIED, not slower. Packaging:
  `curriculum_certificate` (gate + floor + exact budget ledger
  via C330 `budget_telescope_gen`).

## The adaptive-compute arc (C336–C337 as one movement)

The period closes the loop the C335 ranking predicted: C336 is
the MoD side (per-token adaptive DEPTH — who exits early, at what
certified error and exact saved-work price), C337 the curriculum
side (adaptive SCHEDULE — what is learned in which order, with
the honest negative that order-free accounting cannot certify a
swap effect, and the positive that dependency chains are exactly
where order becomes constitutive). Together with C330
(compute→quality) and C334 (samples→quality) the resource-ledger
family now covers: total compute, data, depth routing, and phase
ordering — each with exact ledgers and premise-honest scope
fences. The recurring shape: a premise-form routing/schedule
input, an exact (never ≤-only) work/step ledger, and an explicit
statement of what the certificate does NOT claim.

## Open inventory refresh (recount at ce6a165d)

- Tech-debt rows: unchanged standing set — E5-C301/C302 (ANF
  degree API + context signatures, OPEN seeded, no consumer
  pressure), C234–C236 (Math-layer unification deferrals),
  C239 keepers, C240 MDL C_state bridge (future math beat),
  A8-F6-C254 (SVD premise, iterate lifting), C224 (CertStep
  legacy absorption). NO rows opened by C336–C337 (TD C338
  audit note appended).
- Premise-ledger deferrals (inventory items, not TD rows):
  rectangular spectral bridge, unstructured-sparse NP-hard
  optimal-mask boundary, Ville monitor premise-form — all
  unchanged, none advanced this period.
- P0 reproducibility (parked → PARTIALLY landed this beat, see
  below): local-path leaks found and documented; canonical
  config proposed in comment/docs; elan-dependent fixes remain
  env-blocked.
- Freeze: 7448 declarations (C337 post), census main=14167 at
  ce6a165d — recount this beat, see .tmp/C338/census.log.

## P0 probe — clean-checkout reproducibility (landed part)

Findings (rg 'shmid|C:\Users' over `git ls-files`):

1. `lean-toolchain` contains an ABSOLUTE Windows path
   (`C:\Users\shmid\lean-toolchains\lean-4.35.0-windows`), not a
   version/commit string. Works only where that path exists; the
   matching toolchain commit IS pinned elsewhere
   (`scripts/mathlib-rev.txt` line 2: `eb6cafb…`, enforced by the
   CI MATHLIBPIN gate). Fix parked: rewriting the file requires
   an elan-managed toolchain + full rebuild verification
   (env-blocked; no breaking config changes in this beat).
2. `lakefile.toml` mathlib require is a LOCAL PATH override
   (`path = "C:/Users/shmid/mathlib4"`); `lake-manifest.json`
   mirrors it (`dir`, no rev). On a fresh clone WITHOUT that
   path, resolution FAILS — the require carries no git URL, so
   lake cannot fall back to fetching. Landed: comment block in
   lakefile.toml documenting the override + the canonical
   fallback (git URL + rev from scripts/mathlib-rev.txt) for
   fresh clones; working setup untouched (comment-only diff).
3. No other tracked leaks: scripts/ci.sh reads mathlib location
   from lake-manifest.json (MATHLIB_DIR overridable); pins are
   centralized in scripts/mathlib-rev.txt (rev 56a0058…).
4. README gained a "Воспроизводимость" subsection: toolchain
   source + pinned commit, mathlib rev pin, build command, the
   local-override caveat, and the fresh-clone fallback recipe —
   verified steps only, no overpromise.

## Next-track ranking (C339 candidates)

1. **Spec-refresh: whole-repo ARCHITECTURE/STATUS audit pass**
   — LOW-MEDIUM cost, HIGH benefit, LOW risk. The frontier list
   is thinning and every recent module composed LANDED carriers
   (C330–C337 all telephoned home); that is exactly the signal
   for the "big audit" pattern (last full pass ~C312 ladder
   close): survey what the 14k-decl repo now PROVES vs the HAGI
   goal, harvest gaps and un-consumed seeds (E5 ladder, C240
   bridge, premise-ledger deferrals), feed a fresh addendum.
   Rank 1 — research beat, no new surface, refreshes the queue
   that this beat found thin.
2. **New math from literature** (certified inference/training
   topics not yet covered, via ask.sciencemadereadable scan) —
   MEDIUM cost, VARIABLE risk. Good second beat AFTER the audit
   (the audit's gap list should aim it); running it first risks
   duplicating existing coverage.
3. **Python-side untracked work (mirror update for C328–C337)**
   — LOW cost, LOW-MEDIUM benefit. Hygiene: keeps the mirror
   honest, unblocks nothing on the Lean frontier; schedule as a
   rider on the next chore beat rather than its own cycle.

So: the adaptive-compute arc (MoD depth + curriculum honesty) is
closed and ledgered; the reproducibility debt is documented with
a safe fallback path; the frontier queue needs a fresh audit pass
before the next math module.
