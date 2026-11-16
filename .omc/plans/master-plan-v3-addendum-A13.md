# Addendum A13 (2026-11-16, cycle C339): full-repo spec-refresh audit

Motivation: rank-1 of the C336–C338 period analysis — the frontier
queue is thinning and every module C313–C337 composed LANDED
carriers; time for the periodic "what does the repo NOW prove vs
the HAGI goal" pass (last full pass ~C312 ladder close). This
addendum is the evidence-cited survey: capability map, gap
analysis, ranked priorities for the next campaign.

Evidence baseline (this beat, HEAD a5b056c9 = C338, tree clean):
census ROOT_CENSUS_OK modules=562 main=14167 extra=1820
duplicate_main=0 unique_global_mismatches=0
source_fingerprint=3051676517433627106 (byte-identical metrics to
the C338 landed census — rerun at HEAD, .tmp/C339/census.log);
Freeze verify PASS 7448 declarations, 0 aliased, nothing lost or
changed (.tmp/C339/freeze.log). Sources read in full:
.omc/tech-debt.md, period analyses c324–c329 / c330–c335 /
c336–c338, addendum A12 (CREDO — this addendum adds NO new code
surface and violates no anti-growth law).

The HAGI goal (master-plan-v3): optimal architecture + best
training algorithm + maximum quality at minimum volume and compute.

## (a) WHAT IS PROVEN NOW — the capability map

1. **Certified transitions, all three loops.** The Cert kernel
   (`Hagi.Cert.*`, layer 2): `CertStep` exact consumption laws
   budget_next/risk_next (STATUS §Cert kernel; TD C224 keeps the
   legacy HonestTransition form pending S3 absorption); the
   generic telescope kernel `CertStepGen` with four telescopes —
   drop/delta/risk/budget (C330 `budget_telescope_gen`, 4th
   kernel telescope; receipt .tmp/C330). Training loop: certified
   per-step descent to quality ε (C291 descent rate → C330
   steps-to-ε). Risk/audit loop: two-channel continual contract
   `floor_floor_telescope` (C327, audit gate at the SPENT δ —
   sharper than C274). Curriculum/schedule loop: dependency-chain
   certificates (C337, .omc/analysis/period-c336-c338-analysis.md).

2. **Resource certificates — all axes of the goal have end-to-end
   theorems** (milestone 1 of the C335 analysis): compute — per-step
   FLOP accounting (C328 SparseInferenceCert, first FLOP spend
   through the budget channel) × steps-to-ε (C330
   `total_compute_to_quality`) × inference serving (C331 KV-cache
   EXACT `3R=(n+2)W`, zero-risk) × low-rank tradeoff (C330
   `lowrank_total_compute_le`); data — samples-to-quality (C334
   `samples_to_quality`: exact inversion of the C287 radius +
   C315 margin, m = 2|ι| union) and the JOINT ledger
   `data_compute_budget`; volume — compression certificates
   (C321 rate–distortion step, C322 CertStepGen kernel); depth —
   MoD early-exit with exact work ledger `early_exit_work` +
   two-sided per-token certificate (C336); schedule ordering —
   curriculum phase ledgers (C337).

3. **Energy solver (CRAM track).** A9/E1–E2: CRAM problem carrier +
   discrete kernel + continuous Lyapunov identity; B3 (A11):
   typed CRAM transitions into the canonical Cert kernel with
   exact resource laws (ALGORITHMS.md §23, §B3). Honest scope pins
   carried inline (CRAM ≠ LLM replacement; descent only along a
   given differentiable curve). Python mirror: C316 numpy
   CRAMExpert reference, mirror-fidelity table NO DISCREPANCIES
   (period c313–c323 analysis; report in .tmp/C316, untracked by
   design).

4. **Symbolic path (ANF/RAM/Venn).** Zhegalkin/Möbius transform
   with involution + compile roundtrip (C301 AnfTransform);
   compose3 synthesis + guarded support (C302); certified
   collision abstention with the subset-reading REFUTED (C306);
   multi-candidate priority dispatch (C314); RAM span offsets +
   access-gate separation (C317). Not claimed: end-to-end Python V3
   compiler equivalence (TD E5-C301/C302 OPEN, seeded).

5. **Routing (who computes).** Calibration → always-available
   regret → sleeping/specialist regret chain complete: C319/C320 →
   C325 `sleeping_hedge_regret` (imputed-loss identity
   `swWeight_eq_ewWeight` closes the C320 gap); canary deployment
   ramp harm bound + Ville monitor premise-form (C324, first
   Hagi/Deployment module).

6. **Continual contract.** C327 two-channel: audit
   (`continual_forgetting_bound`, spent-δ gate) + construction
   (`floorsKept_trajectory`) unified by `floor_floor_telescope`.

7. **Backbone composition (FastArch3-shaped).** The E4 ladder
   CLOSED C300–C311, hardened C313: residual-transfer kernel
   (C300) × attention (C307) × RoPE isometry μ=0 (C308) × RMSNorm
   constants with the NOT-GLOBALLY-LIPSCHITZ negative (C309) ×
   GDN doubly-stochastic mixing (C310) → end-to-end
   `fastarch3_transfer_descent` + premise ledger v2 (C311/C313:
   P3 μn and P7 Lc discharged, μg = 1 tanh, Lc = 2 ident-logit).
   Certified descent for the FastArch3-SHAPED model UNDER ledgered
   premises — not a claim about trained weights or the runtime.

8. **Generalization.** C315 two-tier: uniform convergence of PL-loss
   over a finite class (`finite_class_pl_uniform`) + identification
   (`finite_class_pl_margin_argmax`); solver correctness
   quarantined from efficiency (`learned_solver_correctness_exact`).
   C334 composes it into the sample-complexity ledger.

9. **Honesty pins — the negative results as first-class assets**
   (each named, each verified present in its cited artifact):
   (1) `rnEuc_not_lipschitz_with` — pure RMSNorm not globally
   Lipschitz (C309); (2) curriculum order-free accounting is the
   SYMMETRIC sum — ordering per se not certified to matter
   (C337); (3) reversed curriculum order UNCERTIFIED, not slower
   (C337); (4) exact-match arg-range model — subset reading
   refuted by counterexample (C306); (5) MIXED logit-mixture vs
   distribution-mixture different objects, excluded by design
   (C319 pins); (6) unstructured optimal masks NP-hard (Natarajan
   1995) — honest boundary, not formalized (C328); (7) the C233
   telescope constant (K+1)/2 does NOT sharpen (TD C230/C233);
   (8) Cesaro average weaker than last iterate, no held-out
   quality (STATUS §Unified); (9) `growthObjective_…_tendsto_ciInf`
   — no claim the infimum is 0 or a global optimum (STATUS);
   (10) EM paths: NLL → infimum only, no parameter convergence
   (STATUS §changingEMPath); (11) MoD routing is a premise — no
   optimality/load-balancing claim (C336); (12) P1 softmax
   weight-map lived-with as premise (C311 ledger); (13) Muon
   hP-free general form blocked on SVD premise + iterate lifting
   (TD A8-F6-C254, partial C297); (14) GDN2/RAM forms NOT claimed
   as state contractions (C310); (15) `hoeffdingBridge_weaker` —
   the deleted bridge was provably the weaker exponent (C287/
   C288). Fifteen named pins — the count holds.

10. **Instrument integrity.** Lock baked and drift-free since C334
    (C335 clean-bake byte-identical; C333/C334 bakes 7419→7424;
    Freeze 7448 with 24 documented fine additions — same state as
    C338); STMDUP 0 groups; the C332→C333 twin episode instrument
    (clean-bake spot-check) is now standing practice.

## (b) THE GAPS vs THE GOAL

(i) **Formal ≠ executable.** The Python runtime mirror exists ONLY
    for the CRAM pipeline (C316, mirror-validated, untracked); the
    FastArch3/head theorems (C311/C313), the deployment theorems
    (C324), the depth/curriculum ledgers (C336/C337) and the
    resource certificates (C328–C334) have NO executable counterpart
    — no runtime consumes `selectedGroupScalesExec` (TD A5-R5-C241
    residue), no inference path exercises the KV/FLOP ledgers.
    The repo proves guarantees about shapes of computation, not
    about any running system beyond CRAM.

(ii) **Premises lived-with (the honest debt).** P1 softmax
    weight-map (C311); μg gate families beyond tanh (C313 residue);
    P6 IsDoublyStochastic / Sinkhorn boundary (C231, C310); SVD
    premise + iterate lifting for Muon (TD A8-F6-C254); Ville
    monitor premise-form (C324, needs a Unified→Deployment bridge
    module); rectangular spectral-tail bridge (C232/C281 root-
    sorting gap, carried as hE premise in C328); E_min and margin
    premises in the generalization ledgers (C315/C334). None is
    hidden — each is ledgered — but each is a gap between the
    theorem and the algorithm as run.

(iii) **No global optimality anywhere — by design.** Every training
    result is descent/regret/sample-complexity: `steps_to_quality`
    presumes a uniform certified drop; growth objectives converge
    to an infimum with no optimality statement (STATUS pins 9–10);
    MoD routing premise-form (C336); the "optimal architecture"
    half of the HAGI goal is addressed only structurally (the
    FastArch3 shape admits certified descent), never by a
    comparison-to-optimum theorem. This is an honest scope choice,
    and it is the largest single distance between the corpus and
    the literal goal text.

(iv) **Scale gap.** All numeric anchors are toy fixtures (n=4
    RMSNorm 3-4-5; d=2 RoPE π/3; 255^G decidable-finite; ≈300
    samples). No asymptotic statement beyond count-forms
    (O(n²) vs O(kn) work models, 3R=(n+2)W); no theorem couples
    the certificates to width/depth/data scale regimes.

(v) **Pinned-open items** (standing inventory, unchanged since the
    C335/C338 refreshes): joint analytic convergence of alternating
    rounds (C262/C293 tolerance rounds remain); matrix NS general
    (Mathlib upstream); E6 full read-stream equivalence bridge;
    discovery/inductive span-synthesis (out of scope by design);
    E5 degree API + typed context signatures (no consumer
    pressure); C240 MDL C_state bridge (future math beat); P0
    reproducibility elan/config swap (env-blocked; documented
    C338); unstructured-sparsity greedy bound (research risk).

## (c) RANKED PRIORITIES for the next campaign

1. **P-1: Python mirror extension — execute one resource
   certificate.** LOW-MEDIUM cost, HIGH benefit, LOW risk. The
   formal≠executable gap (b-i) is the goal-facing gap; the C316
   CRAM mirror proves the method (numpy reference + FQN
   existence-check + fidelity table). First beat: extend the C316
   pattern to ONE landed certificate end-to-end — KV-cache
   `kv_cache_exact` + `kv_work_ratio` (C331) is the cheapest exact
   object (pure arithmetic, zero ML dependencies) — with a mirror
   script + fidelity report as the receipt; FastArch3 forward pass
   under the premise ledger as the follow-on.
2. **P-2: Discharge one lived-with premise — Ville monitor
   bridge.** LOW cost, MEDIUM-HIGH benefit, LOW risk. A bridge
   module consuming C264/C295 e-processes from the Deployment
   layer would convert the C324 canary monitor from premise-form
   to a closed certificate; the layering blocker is known
   (Unified 6 > Deployment 5) and the fix is a thin bridge module
   at layer 5/6 boundary — composition, not new math (CREDO-
   compatible). First beat: survey the C264/C295 export surface,
   land `Hagi/Deployment/VilleBridge.lean` if layer-legal.
3. **P-3: Rectangular spectral-tail bridge.** MEDIUM cost, MEDIUM
   benefit, MEDIUM risk. Closes the C232/C281 root-sorting gap,
   which currently degrades C328's `sparse_inference_error` to
   premise-form hE and blocks the rectangular Eckart–Young
   transport. First beat: research probe (probe.lean, C334
   pattern) — can the square-case `frobenius_error_truncatedSVD`
  transport via singular-value interlacing in pinned Mathlib?
   If not, pin the boundary honestly and stop.
4. **P-4: Scale-regime statement — one asymptotic theorem.**
   MEDIUM-HIGH cost, MEDIUM benefit, MEDIUM risk. E.g. KV work
   ratio as n→∞ dominance, or depth-ledger scaling in the MoD
   stack (C336 exitLeak vs stack depth). First beat: pick ONE
   count-form theorem and state/prove its limit form; research
   scan first (ask.sciencemadereadable pass per C338 rank-2).
5. **P-5: Literature-scan beat for new math** (C338 rank-2,
   now AFTER the audit as it recommended): MEDIUM cost, VARIABLE
   benefit. Aim the scan at the gap list (b-iii optimality-
   comparison forms, b-iv scaling laws) rather than open-ended
   topics. First beat: the scan + shortlist with in-repo novelty
   check against this capability map.

Deferred (unchanged): E5 degree API (no consumer pressure), C240
MDL bridge, matrix NS general (upstream), P0 config swap
(env-blocked), discovery synthesis (by-design out of scope).

## Measurement / discipline (inherits A12 CREDO)

A13 adds ZERO code surface. Priorities P-1/P-2 are compositions of
landed carriers; P-3/P-4 are bounded research probes before any
module; P-5 is a scan. Any campaign beat landing new modules must
still show meaning-per-line (STMDUP 0, DupLint 0, Freeze clean,
census deltas explained per name).
