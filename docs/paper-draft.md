# Certify-Then-Commit: A Formally Verified Self-Improving Learning System

Draft v0.2 (C531). Все утверждения — либо Lean-якорь (FQN, файл,
строка на HEAD 22576dab), либо измеренный результат прогона с
указанием витка (Cn), либо явный PIN в §Limitations. Никаких
недоказанных клеймов.

## Abstract

We present **certify-then-commit (CTC)**, a discipline in which a
learning system takes a step only after a machine-checked
certificate: the loop **PROPOSE → CERTIFY → ADMIT →
COMMIT/HOLD/ROLLBACK → LOG**. Every accepted step is backed by a
Lean 4 theorem proved against Mathlib; the corpus currently
counts **536 modules / 12 772 theorems / 0 `sorry`** (generated
theorem index at HEAD 22576dab). The cycle-level soundness theorem
`certify_then_commit_sound` guarantees, per T-round run: objective
telescoping over the committed ledger, a probability-δtotal bound
on false commits, an ε-bound on holdout-risk growth, and exact
budget balance. The loop is exercised live: the HAGI_v2 runtime
emits per-step telemetry that is assert-checked at runtime against
the theorem bounds (Python, exit 0), and a mini-HAGI continual
benchmark on measured tasks (3 tasks, 2 grow phases) runs 15
certified steps with zero forgetting in the full-GPM arm and a
measured rank-truncation escape (4 committed steps) in the
relaxed arm, while a held-out prediction benchmark reaches 6/6
certified forecasts. Since v0.1 the loop has been pushed along
two new axes: repeated certified trunk growth now reaches depth
8 (from 5) after a snap-to-dyadic policy defeated the measured
×3.2-per-grow denominator explosion (C506 → C521), and the
commit/hold decision gained a formally verified rollback gate
restoring the full pre-step state (C530). We state honest pins: measurement premises
(`BandDescribes`), measured ε-compromises, hybrid degeneration,
corpus drift, and mini-scale.

## 1. Related Work

- **Continual learning / GPM.** Gradient Projection Memory
  constrains updates to directions orthogonal to old-task input
  span. Our `Hagi/Step` GPM line formalizes zero-forgetting
  (`gpm_zero_forgetting`) and its relaxed rank-truncated
  relaxation (§3.3), including the machine-checked form of the
  all-HOLD phenomenon (`gpm_hold_when_covered`).
- **Anytime-valid inference.** Sequential tests with Ville-type
  master bounds; our discharge routes cite the stitched-Ville
  master `adaptive_anytime_valid` (C399) and stop-mediated
  `false_stop_bound` (C446) as premise-discharge channels.
- **Certified descent / majorizers.** Quadratic majorization with
  safe step sizes; our tight Bennett multiplier κ (§3.1) sharpens
  the classical e^R multiplier by a measured factor
  (e^R/κ(R): 2.77× / 3.79× / 6.73× at R = 0.5 / 1 / 2 — PROPOSAL
  tight-kappa, C471/C480 sanity).
- **Verified ML.** Formalization corpora in Lean 4/Mathlib; this
  work contributes the cycle-level end-to-end theorem plus SVD
  infrastructure prepared for Mathlib upstream
  (docs/UPSTREAM-SVD.md).

## 2. Framework: the certify-then-commit cycle

A T-round cycle over system states with per-round proposals,
certificates, admission gates, commit/hold/rollback decisions and
a budget ledger. The single end-to-end theorem:

> **Theorem (certify_then_commit_sound).**
> `Hagi/Theory/CertifyThenCommit.lean:332` (C463, G6).
> For any T-round CTC cycle, under per-round false-commit measure
> premises (μ{falseCommit i} ≤ δ i) with Σδ i ≤ δtotal and
> per-round holdout allowances Σ e i ≤ ε:
>
> (b) objective telescopes: `obj (t T) ≤ obj (t 0) − Σ drops`
> over committed ledger entries;
> (c) with probability ≥ 1 − δtotal no commit is false
> (union bound over T false-commit events);
> (d) holdout risk grows by at most ε;
> (e) the budget ledger balances exactly
> (`budget (t T) + Σ spends = budget (t 0)`), stays nonnegative,
> and the floors are kept.

Discharge routes for the false-commit premises are cited in the
source: C399 `adaptive_anytime_valid`, C446 `false_stop_bound`.

## 3. Components

### 3.1 Adaptive majorizer with tight κ

> **Theorem (adaptive_descent).**
> `Hagi/Theory/AdaptiveMajorizer.lean:714`.
> If `next η ≤ L − η·A + η²·C` for all η ∈ [0,1] with A ≥ 0,
> C > 0, and η* = A/(2C) ≤ 1, then `next η* ≤ L − A²/(4C)`.

The tight Bennett multiplier κ(R) = (e^R − 1 − R)/R² satisfies
1/2 ≤ κ(R) ≤ e^R for R > 0 (`kappa_ge_half`, :294;
`kappa_le_expR`, :310; monotone `kappa_mono`, :267), replacing
the weaker e^R curvature bound and shrinking the certified-drop
pessimism by e^R/κ(R).

### 3.2 Fisher-quantized updates

> **Theorem (fisher_quant_loss_bound).**
> `Hagi/Theory/MergeQuant.lean:204`.
> If the loss has coordinatewise-bounded second-order curvature
> (premise `hcurv`) and per-coordinate quantization |δ_j| ≤ ε_j,
> then `L(θ0+δ0) − L(θ0) ≤ Σ|g_j|ε_j + ½Σ c_j ε_j²` — quadratic,
> not linear, in the quantization error.

At a stationary point the price is purely second-order
(`fisher_quant_loss_bound_opt`, :226); curvature-weighted budgets
dominate uniform ones (`fisher_beats_lipschitz`, :316;
`fisher_alloc_mono`, :350).

### 3.3 GPM-relaxed with σ_tail

> **Theorem (rank_trunc_forgetting_bound).**
> `Hagi/Theory/Continual.lean:239` (C498).
> A rank-truncated GPM step changes the response on an old input
> by at most `‖row‖ · sigmaTail` — the forgetting budget is tail
> energy leakage, not zero.

> **Theorem (gpm_tradeoff).**
> `Hagi/Theory/Continual.lean:346` (C498).
> Old-input forgetting and new-input progress are both bounded by
> the same `‖row‖·sigmaTail` product: shrinking the tail shrinks
> both. The ε² compromise is exact, not asymptotic.

At full projection P = 1 the tail vanishes and the relaxed theory
degenerates to exact zero-forgetting (`gpm_full_zero`, :284). When
the projection covers the new input, every admissible step has
exactly zero progress — the machine-checked form of the all-HOLD
phenomenon (`gpm_hold_when_covered`, :370).

### 3.4 Sandwich-softmax certified prediction

> **Theorem (cert_pred_adaptive).**
> `Hagi/Theory/Softmax.lean:711` (C495/C502).
> If every class's certified band around the softmax is at most
> 2ε wide and the true softmax gap exceeds 2ε, the band midpoint
> argmax is certified.

Refining the walls (larger denominator precision n, m) never
un-certifies a prediction (`cert_pred_adaptive_mono`, :731;
`bandWidth_mono`, same file), built on the sandwich accuracy lemma
`sandwich_mid_acc` (`Hagi/Theory/Softmax.lean:307`) and
certified descent through bands (`sandwich_descent`,
`Hagi/Theory/CertSandwichBench.lean:65`).

### 3.6 Repeated certified trunk growth (C506)

<!-- source: .tmp/C506/receipt.md; .omc/analysis/period-c506-508-analysis.md §(а) -->

Three identity-grow events in a single run grow the trunk depth
2 → 3 → 4 → 5, each grow asserting the EXACT objective
invariant (residual-zero identity, γ=0; neutral admission +
negative control ε=1/10 ⇒ REJECT), followed by certified
finite-difference training of the new block only (old blocks
frozen). Soundness: `grow_blocks_repeat_sound`
(`Hagi/Theory/GrowTrunkBlock.lean:149`) and
`grow_blocks_obj_invariant_repeat` (`:164`).

| depth | max feature denominator (digits) | certified steps |
|---|---|---|
| 3 | 280 | 4 (block 3) |
| 4 | 840 | 4 (block 4) |
| 5 | 2520 | 4 (block 5) |

Total: 16 certified steps, 62 s cycle, objective strictly
decreasing between grow-trainings and exactly invariant at each
grow (assert on all 3 events). The measured honest limit:
denominators grow ×~3.2 per grow, so depth 6 projects to ~8000
digits / ~150 s — recorded in telemetry as an explicit budget
limit (caps in place, never fired).

### 3.7 Snap-rational grow: the exponential wall defeated (C521)

<!-- source: .tmp/C521/receipt.md -->

Snap policy: after each block is certified-trained, the new
block's weights and features snap to q/2^40 (banker's rounding,
exact `Fraction` arithmetic, per-value error ≤ 2^-41) with a
certified per-point error bound (2|s−y| + |ds|)·|ds| and a
telescoped final guarantee obj_final ≤ obj_cycle_start + Σ
bounds (cumulative ~2.7e-38). Lean: `snap_preserves_objective_bound`
(`Hagi/Theory/GrowSnap.lean:82`), `snap_denominator_reset`
(`:120`), `grow_snap_cycle_sound` (`:146`).

Before/after (C506 → C521 runs, live corpus):

| | C506 (exact) | C521 (snap q/2^40) |
|---|---|---|
| max trunk depth reached | 5 | 8 (6 grow events, 28 certified steps) |
| feature denominators | 2520 digits (depth 5) | 13 digits (bounded 2^40, asserted at every grow) |
| cycle time | 62 s | 8.1 s |
| depth-6 projection | ~8000 digits / ~150 s (wall) | wall removed |

Honest note: snap is not objective-monotone — the certified
state carries a bound, not a drop; 3 of the 6 snaps actually
improved the objective.

### 3.8 Continual-learning mechanism family (C498–C510)

<!-- source: .tmp/C508/receipt.md; .tmp/C510/receipt.md; decision table: .omc/analysis/period-c506-508-analysis.md §(б) -->

Per-step decision table over the four certified mechanisms
(zero-GPM, full-GPM, rank-trunc, A-GEM), driven by MEASURED
state (conflict sign ⟨g, g_old⟩, span fullness):

| measured state | mechanism | number |
|---|---|---|
| no conflict (dot ≥ 0) | A-GEM free step | full gradient, zero price |
| rare conflicts at task start | A-GEM | progress 0.267 vs 0.050 (C508) |
| per-point forgetting bound required | rank-trunc | forgetA −0.0013 vs −0.140 (C508) |
| span(A) exhausted (C494 deadlock) | rank-trunc | only escape |
| strict zero influence on old task | full-GPM | exact, expensive |
| non-conflicting task allows zero step | zero-GPM | cheap, no progress guarantee |

Measured head-to-head, same task/wA/budget/eta/grid (C485
scenario, 24 steps, exact `Fraction`s):

| arm | B_progress | forgetA | projections | committed | holds |
|---|---|---|---|---|---|
| rank-trunc (C508) | 0.0499 | −0.0013 | 24 | 24 | 0 |
| A-GEM (C508) | 0.2667 | −0.1402 | 18 conflicts | 24 | 0 |

A-GEM advances ×5.3 faster; all 18 conflict projections had
interference EXACTLY zero (live instance of
`agem_step_nonneg_interf`, `Hagi/Theory/Continual.lean:326`);
rank-trunc buys a per-point forgetting bound
(`rank_trunc_forgetting_bound`, §3.3). A-GEM guarantees only
first-order non-interference; its negative forgetA is honestly
reported (snapping gives no post-snap guarantee).

The deterministic per-step selector (C510, `hybrid_step_sound`,
`Hagi/Theory/Continual.lean:456`) picks the branch with NO
weakening of its guarantee; on its measured snapshot
(corpus-pin n=53) conflicts were 0/24, so the hybrid honestly
degenerated to the free A-GEM policy (hybrid = A-GEM row:
progress 0.4322, forgetA −0.3831, all 24 committed), while the
degenerate rank-trunc arm (k=2=rank) kept forgetA exactly 0.
This degeneration is pinned in §5.

### 3.9 Rollback gate as a certify-then-commit component (C530)

<!-- source: .tmp/C530/receipt.md (source anchors: HAGI_v2 hagi/selfmodel.py guarded_optimizer_step, wave199) -->

The COMMIT/HOLD decision of §2 is closed under failure: HOLD
restores the EXACT pre-step state — parameters, optimizer state
and RNG (three-component snapshot), and COMMIT requires a
measured weighted validation gain above the full error budget
(e_gen + e_quant + e_route + m_safety).

> **Theorem (rollback_gate_sound).**
> `Hagi/Theory/RollbackGate.lean:98` (C530).
> gate = false ⟹ the guarded step equals the incoming state
> exactly (with per-component params/optimizer/RNG corollaries).

`rollback_obj_exact` (`:127`): any objective is unchanged by a
rollback — the functional twin of the runtime `torch.equal`
self-test. `commit_certified_gain` (`:177`): a commit implies
wa < wb − errBound, i.e. the δ-budget is spent only on commits
(`rollback_budget_unspent`). Mixed chains telemeter the last
COMMIT (no phantom HOLDs), and `weak_gate_loses` is the negative
twin: forcing a commit without the gate strictly worsens the
objective.

### 3.10 Rank-truncation escape

In the mini-HAGI gpm2 phase, full-GPM honestly HOLDs (4 HOLD
rounds, first delta exactly zero on the 1/10000 grid — exact
replica of the C494 phenomenon), and the relaxed rank-truncated
projection escapes: minimal k with max sigmaTail² ≤ eps², eps =
1/10 (PIN, §5), gives 4 committed steps with per-step forgetting
≤ ‖delta‖·sigmaTail (assert-checked). Measured run: C500.

## 4. Benchmarks (measured only)

### 4.1 mini-HAGI (C500)

3 tasks, 2-block trunk, 2 grow phases, holdout, canonical
objective. Full pipeline (A-trunk2 → C-gpm1 → E-gpm2relax →
F-quant → G-stop): **15 certified steps**; certified objective
chain monotone; gpm2 phase: full-GPM arm 0 committed / 4 honest
HOLDs vs relaxed arm 4 committed (k = 1, eps = 1/10);
zero forgetting in the full-GPM arm; relaxed-arm forgetting ≤
bound at every step (asserts green, exit 0).

### 4.2 vs-trainer certified forecasts (C495/C502)

31 measured points (25 train / 6 holdout); 8 committed training
steps; **6/6 holdout predictions certified** (disjoint bands);
accuracy 4/6 (bounded by the model, not the certificate —
certified midpoints agree with the true softmax argmax 6/6);
adaptive band-tightening was available (nm doubling to 1024) but
not needed: all bands disjoint already at n = m = 4.

## 5. Honest limitations (pins)

1. **Measurement premise.** Certified prediction is conditional
   on `BandDescribes z lo hi` — a MEASUREMENT premise
   (`Hagi/Theory/TrainerBenchmark.lean:62`), not derived from the
   model.
2. **ε-tolerances are measured, not tuned.** eps = 1/10 in
   mini-HAGI is a PIN: eps = 1/100 is impossible at any k < rank
   (tail² budget fails — measured tail2max_by_k telemetry). The
   ε in the cycle theorem is a premise-channel allowance.
3. **Scale.** mini-HAGI: 3 tasks, small d; vs-trainer: 31 points.
   No large-scale claims.
4. **Premise-form channels.** falseCommit bounds are premise-form
   with cited discharge routes (C399/C446); in general they
   assume honest reporting of the measurement layer.
5. **Telemetry is runtime-asserted, not Lean-IO.** "Machine
   checked" in this paper refers to Lean proofs; the live-loop
   telemetry is checked by per-step Python asserts against the
   theorem bounds (exit 0), a strictly weaker guarantee.
6. **Prediction accuracy is a model property.** The 4/6 holdout
   accuracy of §4.2 is bounded by the model, not the certificate
   (certified midpoints agree with the true softmax argmax 6/6).
7. **Hybrid degeneration.** On the measured C510 snapshot the
   hybrid selector saw 0/24 conflicts and degenerated to the
   free A-GEM policy (forgetA −0.3831); selector branches other
   than agemFree are covered by probe + Lean theorem but not by
   live telemetry. rank(A∪B)=4=dim makes the full-GPM branch
   unreachable live.
8. **Corpus drift.** The live `unified_ledger` corpus drifts
   between runs (46 → 51 → 53 points across C508–C510; mini-hagi3
   ABORT in C521 is pre-existing drift). Cross-cycle numeric
   comparisons (e.g. §3.6 vs §3.7) use each run's own receipted
   measurements; objective values are not comparable across
   corpus versions.

## 6. Experiment plan (to strengthen before submission)

1. Scale mini-HAGI: tasks 3 → 8+, deeper trunk, measured grow
   schedule; report certified-step rate and HOLD taxonomy.
2. vs-trainer: larger holdout (6 → 50+), exercise the adaptive
   nm-doubling path (currently dormant at n = 4), report
   accuracy-vs-certification curves.
3. Exercise ROLLBACK on an injected premise violation (currently
   the branch is theorem-backed but benchmarked only via HOLD).
4. Cross-check κ-tightness end-to-end: certified-drop gain
   e^R/κ(R) measured on the live loop, not only the sanity grid.
5. Independent re-verification: fresh checkout, `TestFreeze.py`
   + theorem-index regen, plus external review of the 7 anchor
   statements (statement-audit skill).
6. SVD upstream landing (docs/UPSTREAM-SVD.md) to shorten the
   non-Mathlib trusted base.

## Appendix A: anchor table (verified at HEAD 22576dab)

| Anchor | File:line | Cycle |
|---|---|---|
| certify_then_commit_sound | Hagi/Theory/CertifyThenCommit.lean:332 | C463 |
| adaptive_descent | Hagi/Theory/AdaptiveMajorizer.lean:714 | C462+ |
| kappa_le_expR | Hagi/Theory/AdaptiveMajorizer.lean:310 | C471 |
| fisher_quant_loss_bound | Hagi/Theory/MergeQuant.lean:204 | C472 |
| rank_trunc_forgetting_bound | Hagi/Theory/Continual.lean:239 | C498 |
| gpm_tradeoff | Hagi/Theory/Continual.lean:346 | C498 |
| cert_pred_adaptive | Hagi/Theory/Softmax.lean:711 | C495/C502 |
| grow_blocks_repeat_sound | Hagi/Theory/GrowTrunkBlock.lean:149 | C506 |
| snap_preserves_objective_bound | Hagi/Theory/GrowSnap.lean:82 | C521 |
| grow_snap_cycle_sound | Hagi/Theory/GrowSnap.lean:146 | C521 |
| hybrid_step_sound | Hagi/Theory/Continual.lean:456 | C510 |
| rollback_gate_sound | Hagi/Theory/RollbackGate.lean:98 | C530 |

<!-- verified at HEAD 22576dab (C531); anchor lines via rg on
     Hagi/Theory/*.lean -->
