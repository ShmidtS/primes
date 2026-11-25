# Certify-Then-Commit: A Formally Verified Self-Improving Learning System

Draft v1.1 (release). Все утверждения — либо Lean-якорь (FQN, файл, строка;
сверены на HEAD e160b7ec, freeze identity 9043), либо
измеренный результат прогона с указанием витка (Cn), либо PIN в §5.
Якоря кода HAGI_v2 (python `file:line@sha`) сверены `git show` на
указанном sha (мосты C638–C648: @1ae924e / @ca52eb4, волны 254–255;
мосты C651–C657: @e9a96fc / @b3740e0, волны 256–258; мост C664:
@bab8aff, волна 258b). Карта «слой машины ↔ теорема ↔ код» — единственная, §0.
Никаких недоказанных клеймов. Теоремный счётчик abstract остаётся от
e40aa426: новый индекс не генерировался.

## Abstract

**Certified HAGI** is a self-improving learning system in which every
step is taken only after a machine-checked certificate: PROPOSE →
CERTIFY → ADMIT → COMMIT/HOLD/ROLLBACK → LOG, formalized in Lean 4
against Mathlib (**12 875 theorems in 543 modules, 0 `sorry`**, count at
e40aa426; freeze identity **9043** declarations at e160b7ec). The cycle
theorem `certify_then_commit_sound` gives, per T-round run, objective
telescoping, a 1 − δtotal bound on false commits, an ε-bound on
holdout-risk growth and exact budget balance; the consolidated statement
`hagi_master_v34` covers the machine in fourteen clauses (the eleven of
v3.3 plus the useful first growth step, the Adam first step and the
two-way holdout gate, C662). Measured end to
end: mini-HAGI v3 covers 108/115 targets in one live trace (26 certified
steps, forget = 0 bit-exact; C558), the reading floor ⌈nB/w⌉ is attained
and a 2-level hierarchy cuts the peak window budget 127 → 63 at n = 8128
(C611). The formula hits of the paper are closed form and proved:
the optimal snap grid k* = ⌈log₂(L·d/ε)⌉ − 1, the useful first warm-up
step **η* = 4|a|/R² with drop_max = 2a²/R²**, and the codelength sandwich
**H(p) ≤ E[len] ≤ H(p) + KL(p‖p̂)/log 2 + 1** via Kraft–McMillan.
Release feature: **17 PALOMAR cards** and a **§0 map of 31 code
bridges** (C521–C668) in which the consumer's own code (HAGI_v2, python
`file:line@sha`) is checked against the canon and labelled exact,
conditional or honest-gap. We state the open hypotheses as pins (§5,
pins 30–34): U2 global reachability, the chain rule behind a < 0 (closed
for a linear carrier in C663, open for the relu block),
without-replacement conservativity, the range-coder round-trip, and the
holdout gate.

## 0. Certified HAGI map: machine layer ↔ theorem ↔ code

One table for the whole release. **Layer** is the part of the machine;
**canon** is the Lean declaration (`file:line`, rg-verified at HEAD
of HEAD e160b7ec); **code anchor** is HAGI_v2 python
`file:line@sha` (`git show`-verified) or the primes bench twin;
**status** is one of **exact** (the code's statement at the cited lines
is an instance of the theorem), **conditional** (holds under a model
hypothesis the code does not check), **honest gap** (the code does
something the theorem does not cover, said so). Row numbers are cycles.
<!-- source: .tmp/C659/audit.py (Lean anchors); git show <sha>:hagi/*.py (code anchors) -->

| Layer | Canon (Lean file:line) | Code anchor (HAGI_v2 file:line@sha) | Status | Cycle |
|---|---|---|---|---|
| growth | `grow_block_bench_sound` (Hagi/Theory/GrowTrunkBlock.lean:123); `function_preserving_growth` (Hagi/Theory/FunctionPreservingGrowth.lean:200) | `_block_add`/`grow`, hagi/lm.py:581-601 @ca52eb4 | exact | C640 |
| growth | `grow_blocks_repeat_sound` (Hagi/Theory/GrowTrunkBlock.lean:148) | `MAX_BLOCKS = 2`, hagi/unified.py:381 @ca52eb4 | exact (2 blocks) | C640 |
| growth | `growthGate` (Hagi/Theory/NegativeTransfer.lean:570) | `_maybe_grow`, hagi/unified.py:383-440 @ca52eb4 | honest gap: heuristic signal, not the canonical gate | C640 |
| growth | `snap_k_eq_ceil` (Hagi/Theory/GrowSnap.lean:342); `grow_snap_cycle_sound` (:145) | no snap grid in HAGI_v2; bench twin `--mode grow-snap` | honest gap: no consumer code | C521/C593 |
| growth | `adapter_step_certified` (Hagi/Theory/AdapterGrowth.lean:190) | bench twin `--mode adapter-grow` | conditional (bench carrier) | C532 |
| step | `ce_range_code_drop` (Hagi/Theory/AdaptiveMajorizer.lean:1497) | range branch, hagi/lm.py:1313-1324 @1ae924e | exact | C638 |
| step | `ce_adaptive_code_drop` (Hagi/Theory/AdaptiveMajorizer.lean:1473) | `_adaptive_step`, hagi/lm.py:1261 @1ae924e | conditional (window (1e-5, 50]) | C638 |
| step | `CertifiedFiniteStep` (Hagi/Theory/FunctionPreservingGrowth.lean:402); `warmup_h1_of_certified_steps` (:410) | `_certified_finite_step`, hagi/lm.py:826-879 @ca52eb4 | conditional (one objective) | C644 |
| step | `useful_first_step` (Hagi/Theory/FunctionPreservingGrowth.lean:584); `first_step_useful_certified` (:637) | block `grow()`, hagi/lm.py:589-601 @ca52eb4 | conditional (a < 0, hlin) | C657 |
| step | `adam_first_step_dot_pos` (Hagi/Step/AdamDirection.lean:85); `ema_sign_flip_negative` (:125) | `torch.optim.Adam`, hagi/lm.py:349 @b3740e0 | exact as a verdict: descent only at t = 1 | C655 |
| step | `mgda_eq_of_stationary` (Hagi/Model/BatchCEDescentMgdaCode.lean:126) | `mgda_weights`, hagi/selfmodel.py:35-60 @ca52eb4 | exact at ε = 0, equal ‖g‖ | C639 |
| reading | `covStartsStep_covers` (Hagi/Theory/CoverageReading.lean:184); `hier_covers_any_n` (:283) | bench twin `--mode adaptive-span`, `generate-hier` | honest gap: no consumer code | C602/C611 |
| reading | `slot_last` (Hagi/Theory/CoverageReading.lean:720); `slotRev_first` (:734) | `_windows`, hagi/unified.py:297-316 @b3740e0 | exact for order; honest gap: target adjacency | C651 |
| reading | `slot_last` (Hagi/Theory/CoverageReading.lean:720); `padSlot_tail` (:748); `padSlot_last` (:756); `padSlot_full` (:765) | train_guarded holdout, hagi/lm.py:905-907 @bab8aff; `_read_all_windows`, hagi/lm.py:1041-1054 @bab8aff; `generate`, hagi/lm.py:1126-1127 @bab8aff | exact for order; honest gap: `unified.py:1010` @bab8aff still reads `[::-1]` | C664 |
| step | `chain_linear` (Hagi/Theory/FunctionPreservingGrowth.lean:721); `useful_of_adam_first` (:741) | block `grow()`, hagi/lm.py:581/:594-596 @ca52eb4 | conditional (linear carrier; nonlinear: strict descent only, C665) | C663 |
| probability | `holdout_gate_two_way` (Hagi/Theory/HoldoutGateTwoWay.lean:52); `holdout_gate_two_way_delta` (:109) | growth gate, hagi/unified.py:536-543/:563-567/:577 @b3740e0 | conditional (iid slice; k = 512 near-vacuous) | C660 |
| transfer | `neg_transfer_char` (Hagi/Theory/NegativeTransfer.lean:117); `nl_drop_optimal` (:481) | `_fit_domain_adapter`, hagi/unified.py:360/:367 @b3740e0 | conditional (quad model; bench gate C601) | C572/C606 |
| transfer | `auto_transfer_gate_sound` (Hagi/Theory/AutoTransferGate.lean:139) | bench twin `--mode transfer-gate-certified` | honest gap: no consumer code | C577 |
| compression | `constant_distill_exact` (Hagi/Theory/AdapterGrowth.lean:782); `distill_coverage_preserved` (:824) | bench twin `--mode distill` | honest gap: no consumer code | C556 |
| compression | `codelength_ge_entropy_of_kraft` (Hagi/Theory/ArchiverCodeLength.lean:55); `idealLen_le_ce_add_one` (:164) | `probs_to_cdf`/`encode_step`, hagi/archiver.py:33-70 @b3740e0 | conditional (ideal coder, not range coder) | C653 |
| compression | `trit_roundtrip` (Hagi/Theory/TritCodec.lean:117) | `decode_step`, hagi/archiver.py:96-118 @b3740e0 | honest gap: positional pack, not a range coder | C651/C653 |
| probability | `empirical_bernstein_mean_bound` (Hagi/Probability/EmpiricalBernstein.lean:286); `batch_drop_generalizes` (Hagi/Contracts/BatchGlobalTelescope.lean:122) | refine loop, hagi/lm.py:978-1008 @ca52eb4 | conditional (iid batch) | C647 |
| probability | `certified_rounds_union` (Hagi/Contracts/BatchGlobalTelescope.lean:367) | 8-round loop, hagi/lm.py:978-1008 @ca52eb4 | conditional (independent rounds; WOR open) | C648 |
| rollback | `rollback_gate_sound` (Hagi/Theory/RollbackGate.lean:99); `backtrack_accept_drop` (:262) | `guarded_optimizer_step`, hagi/selfmodel.py:78-180 @ca52eb4 | exact as a predicate | C530/C643 |
| rollback | `repair_sound` (Hagi/Theory/RepairForgetting.lean:105); `repair_drop_bound` (:78) | `_repair_forgetting`, hagi/unified.py:408-454 @e9a96fc | exact for control flow; linear bound only | C651 |
| compression | `trit5_roundtrip` (Hagi/Theory/NadyaOptimal.lean:79); `int4_roundtrip` (:98); `exists_best_mse_scale` (:126) | `trit5Pack`/`_pack_int4`/`_best_mse_ternary`, Надя.txt:390-440 (snapshot 2026-11-24) | exact for the pack; honest gap: list-level int4 padding, candidate list | C666 |
| step | `cosine_sched_bounds` (Hagi/Theory/NadyaOptimal.lean:143); `muon_step_norm_bound` (:201) | HybridMuon schedule, Надя.txt:120-152 | conditional (polar norm c is a hypothesis; momentum and weight decay outside) | C666 |
| probability | `paired_lcb_false_grow_bound` (Hagi/Theory/NadyaOptimal.lean:270) | LCB gate, Надя.txt:109-112/:884-890 | conditional (deterministic radius r; code uses z·σ̂/√n) | C666 |
| compression | `bypass_reaches_compression_limit` (Hagi/Theory/NadyaOptimal.lean:304); `ce_covered_zero` (Hagi/Theory/ExactBypass.lean:70) | EXACT_BYPASS, Надя.txt:695-750 | exact for the ideal coder (q = 1 on the support) | C666 |
| growth | `wlogits_width_preserved` (Hagi/Theory/WidthGrowth.lean:597); `attn_score_scale_preserved` (:329); `rotary_old_pairs_unchanged` (:266) | `grow_width`, Надя.txt (function name) | exact for nh = 1, even width; honest gap: nh > 1, odd width, clip are hypotheses `WGrowth` | C667 |
| step | `rank_one_inner_le` (Hagi/Theory/MuonSpectral.lean:156); `rank_one_spectral_norm` (:179); `rank_one_attains` (:231) | Newton–Schulz orthogonalizer newton_schulz_orthogonalize (hagi/core.py:1350, called with iters=3 at core.py:1755 @ca52eb4) | honest gap: rank-one spectral slice proved; full-rank Muon step (von Neumann) open; C671: `smax = ‖G‖₂` for real matrices closed (`smax_eq_opNorm`, Hagi/Theory/MuonSpectral.lean:333) | C670/C671 |
| step | `isometry_inner_le_ssum` (Hagi/Theory/MuonIsometry.lean:128); `uv_transpose_attains_ssum` (:156); `muon_step_optimal_in_isometry_group` (:175) | Newton–Schulz orthogonalizer newton_schulz_orthogonalize (hagi/core.py:1350, iteration core.py:1363, Frobenius normalisation core.py:1353, called with iters=3 at core.py:1755 @ca52eb4) | max over the isometry group ΔᵀΔ = I proved without von Neumann; honest gap: the code's output is an approximate isometry (iters=3, σ_min lower bound not formalised), rectangular G and the convergence of the iteration to U Vᵀ not formalised | C672 |
| step | `batch_directional_derivative` (Hagi/Theory/BatchRankOne.lean:65); `sgd_step_attains` (:136); `rank_one_best_v` (:209) | Muon step on `W1`, hagi/core.py:1755/:1350 @ca52eb4 | honest gap: Frobenius ball and rank-one family proved; spectral-norm optimum and the link to the lm.py:586 layer open | C669 |
| step | `hasFDerivAt_w1L` (Hagi/Theory/FirstLayerGrad.lean:87); `w1_grad_rank_one` (:123); `useful_of_adam_first_w1` (:167) | first layer `W1`, hagi/lm.py:586/:594 @ca52eb4 | strict descent only (no certified drop; single input) | C668 |
| rollback | `post_warmup_growth_safe` (Hagi/Theory/FunctionPreservingGrowth.lean:352) | keep-iff-holdout, hagi/unified.py:435-437 @ca52eb4 | conditional (h1) | C642 |

**What is proved end to end.** Inside Lean, with no code hypothesis:
the cycle theorem (`certify_then_commit_sound`,
Hagi/Theory/CertifyThenCommit.lean:327) and its fourteen-clause
consolidation (`hagi_master_v34`, Hagi/Theory/MasterTheoremV3.lean:323)
— budget, zero-forgetting under a frozen task, objective telescoping,
coverage monotonicity, the exact transfer iff, the minimal snap grid,
the coverage floor and peak window budget. Against the consumer's code,
the exact bridges are the range branch of the certified step, identity
growth of the trunk, the MGDA direction at ε = 0, and three control-flow
predicates (backtracking, repair, window order) — repair with a linear,
not geometric, bound. Two rows are exact only as *verdicts*: the
wave-258 window fix leaves a k-byte gap between context and target, and
Adam is a descent step only at t = 1.
<!-- source: STATUS.md cards C638–C667; §3.19/§3.20 carry only deltas -->

**What remains a hypothesis or a model.** (1) h1 for the real warm-up:
the code warms the block with bare Adam and never calls the certified
step (pin 25). (2) Batch → global: iid sampling and independent rounds,
while the code samples without replacement and updates θ between
rounds; the WOR conservativity is an unproved intuition (pin 28, 32).
(3) The descent signal a < 0 of the useful first step is a hypothesis;
its chain-rule link to `adam_first_step_dot_pos` is not formalized (pin
31), and the global reachability of a useful block (U2) is open (pin
30). (4) Codelength bounds are for the ideal coder ⌈−log₂ p̂⌉₊; the
range coder of archiver.py has no Lean model, and losslessness is tests
plus a measured 11/11 (pin 33). (5) Every holdout gate compares
measured values; no theorem relates train objective to holdout CE (pin
29, 34). (6) No bridge at all for the snap grid, adaptive-span and
hierarchical reading, the auto transfer gate, or constant distillation
— bench twins only.

## 1. Related Work

- **Continual learning / GPM.** Gradient Projection Memory
  constrains updates to directions orthogonal to old-task input
  span. Our `Hagi/Step` GPM line formalizes zero-forgetting
  (`gpm_zero_forgetting`) and its relaxed rank-truncated
  relaxation (§3.3), including the machine-checked form of the
  all-HOLD phenomenon (`gpm_hold_when_covered`).
- **Anytime-valid inference.** Sequential tests with Ville-type
  master bounds; our discharge routes cite the stitched-Ville
  master `adaptive_anytime_valid` and stop-mediated
  `false_stop_bound` as premise-discharge channels.
- **Certified descent / majorizers.** Quadratic majorization with
  safe step sizes; our tight Bennett multiplier κ (§3.1) sharpens
  the classical e^R multiplier by a measured factor
  (e^R/κ(R): 2.77× / 3.79× / 6.73× at R = 0.5 / 1 / 2 — PROPOSAL
  tight-kappa, C471/C480 sanity).
- **Verified ML.** Formalization corpora in Lean 4/Mathlib; this
  work contributes the cycle-level end-to-end theorem plus SVD
  infrastructure prepared for Mathlib upstream
  (docs/UPSTREAM-SVD.md).

**Related-matrix (v0.6):** where each new-era result sits against
the closest classical line.

| Aspect | Classical line | This work (anchor, cycle) |
|---|---|---|
| Continual zero-forgetting | GPM projections | per-task adapter isolation, exact (clause 2 of `hagi_master_v31`, C600/C544) |
| Transfer control | heuristic warm-start gates (ce proxy) | exact quad-iff + smooth sufficient budget `n•nlBudget` (clauses 5+8, C572/C592; bench gate C601) |
| Quantization schedule | fixed grids | optimal `k* = ⌈log₂(L·d/ε)⌉−1` (`snap_k_eq_ceil`, C593; auto-k* bench C597) |
| Input coverage / reading | fixed or truncated windows | coverage iff `s ≤ w` with adaptive step and honest INFEASIBLE (`covStartsStep_covers`/`_adaptive_covers`, C602) |
| Master statements | per-property theorems | one 8-clause conjunction over the whole machine (`hagi_master_v31`, C600) |

## 2. Framework: the certify-then-commit cycle

A T-round cycle over system states with per-round proposals,
certificates, admission gates, commit/hold/rollback decisions and
a budget ledger. The single end-to-end theorem:

> **Theorem (certify_then_commit_sound).**
> `Hagi/Theory/CertifyThenCommit.lean:327` (G6).
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
> `Hagi/Theory/AdaptiveMajorizer.lean:713`.
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
> `Hagi/Theory/Continual.lean:239`.
> A rank-truncated GPM step changes the response on an old input
> by at most `‖row‖ · sigmaTail` — the forgetting budget is tail
> energy leakage, not zero.

> **Theorem (gpm_tradeoff).**
> `Hagi/Theory/Continual.lean:346`.
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
> `Hagi/Theory/Softmax.lean:810`.
> If every class's certified band around the softmax is at most
> 2ε wide and the true softmax gap exceeds 2ε, the band midpoint
> argmax is certified.

Refining the walls (larger denominator precision n, m) never
un-certifies a prediction (`cert_pred_adaptive_mono`, :833;
`bandWidth_mono`, :781), built on the sandwich accuracy lemma
`sandwich_mid_acc` (`Hagi/Theory/Softmax.lean:406`) and
certified descent through bands (`sandwich_descent`,
`Hagi/Theory/CertSandwichBench.lean:65`).

### 3.5 Repeated certified trunk growth

<!-- source: receipt C506; .omc/analysis/period-c506-508-analysis.md §(а); файл удалён в c442e69, история: git show c442e69^:.omc/analysis/period-c506-508-analysis.md -->

C506.

Three identity-grow events in a single run grow the trunk depth
2 → 3 → 4 → 5, each grow asserting the EXACT objective
invariant (residual-zero identity, γ=0; neutral admission +
negative control ε=1/10 ⇒ REJECT), followed by certified
finite-difference training of the new block only (old blocks
frozen). Soundness: `grow_blocks_repeat_sound`
(`Hagi/Theory/GrowTrunkBlock.lean:148`) and
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

### 3.6 Snap-rational grow: the exponential wall defeated

<!-- source: receipt C521 -->

C521.

Snap policy: after each block is certified-trained, the new
block's weights and features snap to q/2^40 (banker's rounding,
exact `Fraction` arithmetic, per-value error ≤ 2^-41) with a
certified per-point error bound (2|s−y| + |ds|)·|ds| and a
telescoped final guarantee obj_final ≤ obj_cycle_start + Σ
bounds (cumulative ~2.7e-38). Lean: `snap_preserves_objective_bound`
(`Hagi/Theory/GrowSnap.lean:81`), `snap_denominator_reset`
(`:119`), `grow_snap_cycle_sound` (`:145`).

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

### 3.7 Continual-learning mechanism family

<!-- source: receipt C508; receipt C510; decision table: .omc/analysis/period-c506-508-analysis.md §(б); файл удалён в c442e69, история: git show c442e69^:.omc/analysis/period-c506-508-analysis.md -->

C498–C510.

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

The deterministic per-step selector (`hybrid_step_sound`,
`Hagi/Theory/Continual.lean:456`) picks the branch with NO
weakening of its guarantee; on its measured snapshot
(corpus-pin n=53) conflicts were 0/24, so the hybrid honestly
degenerated to the free A-GEM policy (hybrid = A-GEM row:
progress 0.4322, forgetA −0.3831, all 24 committed), while the
degenerate rank-trunc arm (k=2=rank) kept forgetA exactly 0.
This degeneration is pinned in §5.

### 3.8 Rollback gate as a certify-then-commit component

<!-- source: receipt C530 (source anchors: HAGI_v2 hagi/selfmodel.py guarded_optimizer_step, wave199) -->

C530.

The COMMIT/HOLD decision of §2 is closed under failure: HOLD
restores the EXACT pre-step state — parameters, optimizer state
and RNG (three-component snapshot), and COMMIT requires a
measured weighted validation gain above the full error budget
(e_gen + e_quant + e_route + m_safety).

> **Theorem (rollback_gate_sound).**
> `Hagi/Theory/RollbackGate.lean:99`.
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

### 3.9 Rank-truncation escape

In the mini-HAGI gpm2 phase, full-GPM honestly HOLDs (4 HOLD
rounds, first delta exactly zero on the 1/10000 grid — exact
replica of the C494 phenomenon), and the relaxed rank-truncated
projection escapes: minimal k with max sigmaTail² ≤ eps², eps =
1/10 (PIN, §5), gives 4 committed steps with per-step forgetting
≤ ‖delta‖·sigmaTail (assert-checked). Measured run: C500.

### 3.10 Adapter era: four certified growth mechanisms

<!-- source: receipt C532; receipt C533; receipt C535; receipt C536 -->

C532–C536.

The growth mechanism family now spans four certified paths. All
admit new capacity by an EXACT objective-invariant admission and
train only the new parameters by certified steps.

| mechanism | cycle | new params/grow | max depth | maxden |
|---|---|---|---|---|
| identity/fiber block | C506/C521 | 21 (block) | 8 (snap, C521) | 13 digits (snap) |
| adapter r=1/r=2 (LoRA side-branch) | C532 | 8/16 (2·r·d) | — | exact Fractions |
| adapter + snap composite (8 levels r=1) | C533 | 8/level, 64 total | 10 | 13 digits (≤2^40, every level) |
| SVD-Matryoshka merge (stack → single) | C536 | 16 (rank ρ=2) | 10 → 1 matvec | 13 digits |

Core theory (Hagi/Theory/AdapterGrowth.lean):
`adapter_neutral_B` (:103) — B = 0 makes the side-branch EXACTLY
neutral for arbitrary A; `adapter_step_certified` (:192) —
COMMIT only on a measured strict drop; `adapter_param_count`
(2·r·d) with `adapter_param_count_le_block` (2rd ≤ d² at 2r ≤ d).
Measured (C532 bench, obj invariant EXACT at every admission):
adapter r=1 = 8 and r=2 = 16 parameters vs 21 for the identity
block; 12 certified steps, 0 holds.

**Composite stack (C533).** 8 admission-train-snap levels of
r=1 adapters grow the trunk depth 2 → 10 at 8 parameters per
level (64 total vs 21 for one full block). Each level snaps to
q/2^40 and folds into the features, so every level restarts
from the grid — the C506 ×3.2-per-grow denominator compounding
is structurally excluded (maxden 13 digits at every level).
Canonical run: start ≈ 2.283, total certified drop 2.271, 21
steps, 3.2–4.3 s, bit-identical deterministic repeat. The
cumulative snap error bound ≈ 2.98e-13 against a certified drop
of 2.27 — a ~13-orders-of-magnitude margin. Lean:
`adapter_snap_cycle_sound` (:283).

**Rank-adaptive selector (C535).** At each level the selector
PROBEs r=1 and r=2 on a copy (exact C530 rollback — the live
state never moves) and selects by measured score =
probe_drop/params (ties → r=1). `rankSelect` is a deterministic
function of the measured state (`rank_select_deterministic`);
`rank_select_sound` (:328) keeps the full guarantee of whichever
branch is chosen. Measured: score(r=2) ≤ score(r=1) at all 8
levels, so the selector honestly picks r=1 every time (adaptive
≡ fix-r1 bit-for-bit, 64 params, drop/param 0.035310, 17 steps);
the r=2 arm reaches the same drop at ×2 parameters (128, 10
steps) and is correctly rejected — no degradation.

**SVD-Matryoshka merge (C536).** After the 8-level stack, an
exact rational Gauss-Jordan rank/ factorization merges the
stack into a single adapter on the original trunk features:
`adapter_stack_rank_bound` (:416, rank(Π(I+Eᵢ) − 1) ≤ Σ rank Eᵢ),
`adapter_merge_error_bound` (:457, σ_tail + ℓ¹-Lipschitz),
`adapter_merge_params` (:443). Measured (exact rank of Δ = 2):

| model | params | matvec | obj change | certified bound |
|---|---|---|---|---|
| stack 8×r=1 | 64 | 8 | final 1.02460e-2 | cycle bound holds |
| merged k=ρ=2 | 16 (−75%) | 1 | −6.7e-11 (improvement) | 6.60e-8 |
| merged k=1 | 8 (−87.5%) | 1 | ~0.51 degradation | holds, usable=False |

Honest: k=1 (σ_tail ≈ 0.998) is correctly reported unusable;
the data gave rank 2 < min(d,L) = 4, so the bound is not vacuum.
17 certified steps, ~3.6 s, bit-identical repeat.

### 3.11 External absorption: five HAGI_v2 observations as theorems

<!-- source: receipt,C544,C545 receipts; plan: .omc/analysis/external-plan-c537-mapping.md (файл удалён в c442e69, история: git show c442e69^:.omc/analysis/external-plan-c537-mapping.md); delivery: docs/PROPOSAL-external-plan.md (C543) -->

C537–C545.
A mapping audit inverted the bridge: instead of porting
HAGI_v2 code, its top observed defects were formalized as
theorems (C538–C541) and delivered back with exact
code-fix mappings (docs/PROPOSAL-external-plan.md).

**(1) Weight-decay leak (P4).** `wd_proj_preserves`:
projected decay W′ = W − ηλ·(W − W·P) keeps W·P EXACTLY (the
measured projected leak 5.68e-15 is a machine zero = exact
zero); naive decay (1−ηλ)·W has the EXACT leak factor (1−ηλ) on
the protected component (`naive_decay_parallel`,
`naive_decay_norm`), leaks strictly (`naive_decay_leak`, :128;
measured naive leak 1.945); `wd_gpm_step_sound` (:159) composes
a black-box complement step with projected decay.

**(2) Empirical-Bernstein radius (P1).**
`empirical_bernstein_bound` / `_mean_bound` (+
`freedman_tail_two_sided`, `eb_radius_algebra`): with measured
σ̂² and range b, |μ̂| < √(2σ̂²L/n) + 2bL/n at ≥ 1−α. Witness
contrast (ΔCE=0.04, R=11.09, α=0.01): n_Hoeffding = 176 995 vs
n_EB(MP form) = 6439 — a **27.49×** sample saving (our form:
4267, 41.5×). Honest: σ̂ is a runtime premise (no MP λ-trick).

**(3) Observational-equivalence search completeness (P6).**
`oe_search_complete` (:80): OE-dedup search never loses a
solution that matches the target on the probes — completeness
is RELATIVE TO THE PROBES, no semantic equivalence claimed.
Witness: toy space 343 → 4 visits (~86×); the HAGI_v2 analogue
compressed 6478 → 896 candidates (7.2×).

**(4) Exact bypass, zero cross-entropy (P8).** On a
PROVEN_EXACT coverage, CE contribution is EXACTLY zero:
`ce_pointwise_of_prob_one`, `ce_total_eq_residual` (:90) —
total = residual, bit-for-bit (witness 4.264244 == 4.264244);
`exact_gate_sound` (:97) and the negative `exact_gate_rejects_zero`
(p = 0 ⇒ rejected, junk log never used).

**(5) Polar-Express interval certificate (P3).** A
scalar, SVD-free interval certificate for the minimax
Newton–Schulz iteration: three rationalized p(x) = ax+bx³+cx⁵
polynomials map the spectral box by EXACT rational bounds:
[1/1000, 1] → [1/256, 1313/1024] → [5/512, 601/512] → final
[9/512, 1049/1024] ≈ [0.0176, 1.0244] (`polar_express_step3_bound`,
Hagi/Optimization/PolarExpressCert.lean:372). Honest correction:
the upper end is 1.0244, i.e. within 2.5% of 1 — no spectral
explosion, but the iteration does not pin the top of the
spectrum to exactly 1.

**Adapter continual isolation (C544).** Composing adapters with
the continual line: per-task adapters give zero forgetting
STRUCTURALLY — `adapter_isolation_zero_forgetting` (AdapterGrowth.lean:564) and
`adapter_per_task_sound` (AdapterGrowth.lean:579) need no projections or budgets.
Measured head-to-head (conflict-pinned task B, same
trunk/data/eta/grid): ISO forgetA = 0 EXACT (bit-exact assert)
vs SHARED +0.2331 vs naive-trunk +5.5757 (the scenario of
`trunk_update_needs_projection`, :618, composed with C538).
PIN: on a same-distribution B the measured forgetting was
negative (SHARED −0.304 / TRUNK −0.753) — forgetting is a
conflict phenomenon; the conflict pin is documented in code.

### 3.12 The full self-improving loop in one trace

<!-- source: receipt C547 -->

C547.
The era closes with all certified components composed into ONE
live run (`--mode mini-hagi-loop`, real unified_ledger, 113
points): a single trace, a single JSON, one theorem.

> **Theorem (full_loop_sound).**
> `Hagi/Theory/MiniHagiLoop.lean:64`.
> Composition of `exact_gate_sound` + `adapter_step_certified` +
> `adapter_isolation_zero_forgetting` + `oe_search_complete` +
> `empirical_bernstein_mean_bound` — no new deep facts, only
> certified composition.

| phase | mechanism | measured result |
|---|---|---|
| P1 bypass | exact-gate (C541) | const 3/2 covers 107/113 (94.7%); CE of covered = 0 EXACT; wrong-const negative err = 1/4 |
| P2 adapter A | certified steps (C532) | 10 steps, CE 4 → 0.1216, drop > 0; HOLD negative leaves state unchanged |
| P3 grow | neutral admission + snap (C521/C532) | obj invariant bit-for-bit; 6 steps; CE 0.1214 |
| P4 continual | per-task isolation (C544) | adapter B 10 steps, forgetA = 0 EXACT; SHARED negative leak = 1.386 |
| P5 search + gate | OE dedup + EB (C540/C539) | const-2 law accepted (+5 EXACT); coverage 112/113 (99.1%); EB gate n_EB 9649 ≤ n_Hoeffding 10851 |
| P6 total | full_loop_sound | **26 certified steps, 1 hold, 10 parameters (2 adapters)** |

Honest notes (pinned in §5): the EB contrast on this corpus is
1.12× (vs 27.49× in the C539 instance) — a property of the
data, not the bound form; P1 coverage is on snap-quantized
targets (PIN); one position remains uncovered (the OE space was
exhausted — completeness does not promise solutions outside the
space).

### 3.13 Iterative self-improvement

<!-- source: receipt C549 -->

C549.
The full loop of §3.12 becomes ITERATIVE: one run executes 7
iterations in a single trace (one run / telemetry / JSON /
witness; budget MAX_ITER = 8 never exhausted — the stop is the
EB gate). Each iteration: OE-search in a space GROWN from the
accepted primitives → EXACT coverage extension (monotonicity
asserted bit-exact) → adapter retraining on the shrinking
residual (certified snap-GD, 10 steps/iteration, drop > 0 /
HOLD) → EB telemetry (n_EB < n_Hoeffding at every iteration).

> **Theorem (iterative_loop_sound).**
> `Hagi/Theory/MiniHagiLoop.lean:154`. Induction over
> the chain of additive iterations: coverage at step k is a
> subset of coverage at step n for all k ≤ n. The only new
> mathematical fact is monotonicity:
> `coverage_append_monotone` (`:134`, via `coversPrim` `:128`,
> `iterStep` `:122`, `IterState` `:117`); per-iteration soundness
> is `full_loop_sound` (§3.12) with no weakening.

Corpus (layered, PIN grid 1/16): L1 const (57 pos, i%2==0);
L2 = snap(256·x0+32·x3, 1/16) (19 pos, i%3==0) — anchored on
an accepted constant; L3 = snap(L2+32·x2, 1/16) (7 pos,
i%5==0) — block L2 as a building block; the 30-position
residual carries real tau(y).

| it | coverage | accepted primitive | residual CE (certified) |
|---|---|---|---|
| 1 | 0 → 54.9% | const (L1 + real tau-cluster) | 1504.8 → 1153.0 |
| 2 | 71.7% | affine, deps p1 | 3334.1 → 1593.1 |
| 3 | 78.8% | affine², deps p3 | 2291.0 → 1671.1 |
| 4 | 85.0% | real tau-cluster | 3053.9 → 2019.5 |
| 5 | 89.4% | real tau-cluster | 2.486 → 0.171 |
| 6 | 93.8% | real tau-cluster | 2.584 → 0.221 |
| 7 | 93.8% STOP | 0 accepted — EB gate | 2.954 → 0.221 |

60 certified steps total, 0 holds, 4 adapter parameters per
iteration.

**Compositional necessity (in-run negatives, asserted).** Law 2
is NOT found without block 1 (max constant coverage of the L2
residual = 1 < 5); law 3 is NOT found without block 2 (max
level-1 (c+aff) coverage of the L3 residual = 0 < 5). The
accepted chain p1 (const) → p3 (aff, deps p1) → p5 (aff², deps
p3) is genuinely compositional: later laws require earlier
building blocks. Real tau-clusters are found legitimately at
iterations 1, 3, 5, 6.

### 3.14 Universal loop on the full live corpus — an honest measurement

<!-- source: receipt C551 -->

C551.
The C549 compromise "the laws live in the corpus" is lifted:
the loop runs on ALL 113 live points of ALL domain keys of the
live `unified_ledger` (domain = ledger key; 114 keys / 113
live; the task-statement "~185 points" was rejected by direct
file read, recorded in research). Targets are REAL
snap(ce_i, 1/16). OE-search is honest: constants from real t;
linear p + a·x_j on real features (grid 1/16..256). If a law is
not found, that IS the result.

> **Theorem (universal_loop_corpus_mono).**
> `Hagi/Theory/MiniHagiLoop.lean:190`. Union-additivity
> of coverage over corpus concatenation lA ++ lB, composed with
> `iterative_loop_sound` — the universal run inherits the same
> certified monotone coverage as the iterative loop.

Iterations (one run / telemetry / witness): it1 — 4 constant
clusters (11/8, 25/16, 13/8, 27/16), 0 → 64/113; it2 — const
3/2 → 86/113; it3 — const 23/16 → 106/113 (93.8%); it4 — 0
accepted, EB-gate STOP. Certified: 1826 adapter steps
(drop > 0), 134 HOLD; coverage monotonicity asserted bit-exact
at every iteration; drift detector: recomputation on a frozen
copy gives 106 == 106; negatives: wrong-const err = 1/256 ≠ 0,
HOLD leaves state unchanged.

**Per-domain isolation.** 113 domains; 106/113 fully covered
(93.8%); adapter CE mean 0.0739 (min 2.5e-6, max 1.094);
**forgetA = 0 on ALL 113 domains** — real bit-exact asserts of
parameter snapshots after every training phase of every domain
(the C544 isolation), not a declaration.

**The honest part.**

- The 93.8% real coverage is achieved ENTIRELY by constant
  clusters — genuine structure in the data, but the weakest
  kind of law.
- NOT ONE linear law was found (every candidate < 5 new
  positions): the universal complexity of the live corpus is
  MEASURED — the real corpus is less deterministic than the
  layered synthetic one. This is a measured applicability
  boundary of the loop, not a failure of the search: the search
  space was enumerated honestly.
- Stability vs C549 (c549_stability): const 0 — 0/113;
  snap(256·x0+32·x3) — 0/113; +32·x2 — 0/113. The synthetic
  laws of §3.13 do NOT transfer to real full-corpus targets
  (0/113) — the layered targets were a construction of C549,
  and this run says so on record.

### 3.15 Unification: one adapter machine for the whole knowledge lifecycle

<!-- source: receipt C555; receipt C556; receipt C557 -->

C554–C556.
The phase analysis C557 names C554–C556 the UNIFICATION era:
growth, continual learning, compression and distillation stop
being separate mechanisms and become one certified adapter
machine — the full algebra of a knowledge lifecycle (admit,
learn, merge, distill, cover) under a single mathematical
object: a rank-bounded adapter stack. Two pillars carry the
"min volume, max quality" claim:

**Pillar 1 — self-compressing loop (C555).** The loop
learn→merge→learn admits rank-1 levels with an EXACT objective
invariant (B = 0), trains all live parameters by certified
fd-steps, and merges exactly (Gauss–Jordan over Fractions, so
the merge-error telescope sums to 0 bit-exact). Measured on
the full live corpus (113 domains): parameters after EVERY
merge ≤ 2·K·d = 32 (asserted, exact count it1→8, it2→16,
it3→24, it4..it6→32) while the no-merge contrast grows
linearly to 2·L·d = 48; cumulative certified drop monotone
0.158→0.248→0.276→0.317→0.346→0.364; residual CE
0.4354→0.0717 (−84%); 56 certified steps / 0 HOLD. Knowledge
grows; volume does not.

> **Theorem (self_compress_loop_sound).**
> `Hagi/Theory/AdapterGrowth.lean:722`. The loop
> telescopes the objective (delegate of grow_snap_cycle_sound,
> generalized to a merge cycle) AND keeps params ≤
> selfCompressParams k d = 2·k·d for ANY number of iterations
> (`self_compress_params_bounded`, :700; strict contrast
> `self_compress_params_contrast`, :710).

Honest negative: squeezing below k = d destroys knowledge on
this corpus (matryoshka k = 3 degrades to 5.44, k = 2 to 1.22
— both covered by the certified bound marking them unusable).

**Pillar 2 — lossless distillation of constant clusters
(C556).** The six constant clusters of C551 (106/113 via the
exact gate) are distilled into rank-1 adapters θ(c) = (A := 0,
B := const c): the output ≡ c on ANY input, EXACTLY, with zero
training steps. Measured: cluster CE 0.7831 → 0 BIT-EXACT
(per-cluster asserts + drift detector 106 == 106); exact-gate
branches 113 → 0 — the whole corpus runs one adapter path with
no branching.

> **Theorem (constant_distill_exact / distill_coverage_preserved).**
> `Hagi/Theory/AdapterGrowth.lean:782` / `:824`. The
> distilled readout is exactly c (construction), so coverage
> and CE = 0 are PRESERVED — composition with exact_gate_sound,
> not a duplicate.

**The honest parameter contrast** (a Lean fact, not a claim):
the distillate costs 6×2d = 48 parameters while symbolic
storage needs only the 6 VALUES — symbolic is strictly cheaper
(`symbolic_storage_cheaper`, :853: J < 2·J·d for d ≥ 2). The
value of distillation is UNIFICATION of paths (0 branches, one
matmul path, exact-bypass merged into the adapter residual),
not memory.

### 3.16 Mini-HAGI v3: the full certified assembly in one trace — the headline result

<!-- source: receipt C558 -->

C558.
The unification era closes with a reference assembly: every
certified component of C547–C556 executes in ONE bench run on
the live corpus (snapshot frozen on the run — lesson C535; the
live ledger had grown 113 → 115 between C556 and C558, and the
run honestly took 115 points; invariants stable: 6 constant
clusters, residual 7, coverage n−7 = 108/115). One trace, one
JSON, 115 points, 1.87 s, 55 certified steps, 0 holds,
forget = 0 (bit-exact frozen-copy drift detector).

| phase | mechanism | measured result (one trace, C558) |
|---|---|---|
| P1 bypass | exact-gate const clusters (C541/C551) | 6 clusters, 108/115, coverage monotone bit-exact |
| P2 distill | θ(c_j) rank-1 adapters, certified init (C556) | cluster CE = 0 BIT-EXACT; gate branches 115 → 0 |
| P3 adapter residual | certified fd-steps (C532) | 7/7 committed (drop > 0), residual CE 3.8022 → 0.5120 |
| P4 self-compress | admit→learn→exact-merge, K=d=4 (C555) | params ≤ 2·K·d = 32 after EVERY merge; obj 0.5120 → 0.0733; cum drop 0.4387 monotone; merge telescope = 0 |
| P5 EB stop | commit = 0 ⇒ STOP (C539) | branch active; actual stop = budget MAX_ITER = 6 (honest, pinned in §5) |
| total | v3_assembly_sound | **55 certified steps, 0 holds, forget = 0, params ≤ 32, 1.87 s** |

> **Theorem (v3_assembly_sound).**
> `Hagi/Theory/AdapterGrowth.lean:884`. The unified
> adapter machine is the CONJUNCTION of the distill branch
> (`distill_coverage_preserved` ⇒ CE = 0 on every cluster) and
> the self-compress branch (`self_compress_loop_sound` ⇒
> objective telescope + params ≤ 2·k·d) — composition with NO
> weakening of the components' hypotheses. No new deep facts:
> this is the reference theorem that the full self-improving
> machine assembles soundly.

Witness (rc = 0): #eval trajectory
checks on run numbers (P3 + P4-it1), params-bounded instance
32 ≤ 32, telescope instance on run numbers, count contrast
32 < 48, negatives (wrong-const 1/256 ≠ 0; head-only CE ≠ 0 on
clusters before distillation).


### 3.17 The consolidated statement: clause map of the certified machine

C600 (v3.1), C614 (v3.2), C622 (v3.3). The consolidation era closes
with ONE statement covering the whole certified machine:
`hagi_master_v33` (`Hagi/Theory/MasterTheoremV3.lean:252`), a
conjunction of eleven clauses, each a DELEGATE to an already-proven
theorem with hypotheses verbatim and no weakening — no new deep
facts, only the conjunction (the `master_theorem_v3` pattern of
C576, `MasterTheoremV3.lean:83`). Hypotheses: the machine block of
v3.1 verbatim, the transfer block (`L G hL`, smoothness + G-bound),
the hier block (`nB B w s'`, `0 < B`, `0 < s'`, `s' ≤ w`), plus
`hw : 0 < w` and `hdiv : w ∣ B`.

| # | clause (Lean-verbatim) | delegate | carrier | since |
|---|---|---|---|---|
| (1) | `params bs.length ≤ 2 * k * dd` — parameter budget at any cycle length | `self_compress_loop_sound` | Hagi/Theory/AdapterGrowth.lean:722 | v3.1 (C600) |
| (2) | `perTaskVec (s τ) a = perTaskVec (s 0) a` — zero forgetting by per-task adapter isolation | `adapter_per_task_sound` | Hagi/Theory/AdapterGrowth.lean:579 | v3.1 |
| (3) | `step bs.length ≤ o0 + bs.sum` — the certified objective telescope | (machine obj bound) | Hagi/Theory/MasterTheoremV3.lean:83 | v3.1 |
| (4) | `coversPrim CovP (st n) i` — coverage is monotone along the append-only cycle | `iterative_loop_sound` | Hagi/Theory/MiniHagiLoop.lean:154 | v3.1 |
| (5) | `quadObj tB θ > quadObj tB 0 ↔ 2 * ⟪θ, tB⟫_ℝ < ‖θ‖^2` — transfer governed by an EXACT iff boundary | `neg_transfer_char` | Hagi/Theory/NegativeTransfer.lean:117 | v3.1 |
| (6) | `snapK Lq dq εq hεq hLd0 = ⌈log₂ (Lq * dq / εq)⌉ - 1` — the snap grid is MINIMAL for the ε-budget | `snap_k_eq_ceil` | Hagi/Theory/GrowSnap.lean:342 | v3.1 |
| (7) | `∀ ib < nc, ∃ sw ∈ covStarts nc kc, sw ≤ ib ∧ ib < sw + kc` — every byte of the input is covered by some lattice window | `covStarts_covers` | Hagi/Theory/CoverageReading.lean:54 | v3.1 |
| (8) | `f z - nE * nlBudget γ L G ≤ f (nlRun nE γ grad z) ∧ f (nlRun nE γ grad z) ≤ f z` — smooth sufficient-transfer bound at equal GD budget, `nlBudget γ L G = γ·G² + L·γ²·G²/2` | `smooth_obj_transfer_bound` | Hagi/Theory/NegativeTransfer.lean:386 | v3.1 |
| (9) | `nlDrop (1 / L) L G = G ^ 2 / (2 * L)` — the certified-optimal single-step drop γ* = 1/L | `nl_drop_optimal` | Hagi/Theory/NegativeTransfer.lean:481 | v3.2 (C614) |
| (10) | `∀ ib < nB, ∃ t ∈ hierStarts nB B w s', t ≤ ib ∧ ib < t + w` — coverage of `[0, nB)` at ANY nB, streaming peak ≤ m windows | `hier_covers_any_n` | Hagi/Theory/CoverageReading.lean:282 | v3.2 |
| (11) | `(hierStarts nB B w w).length = (nB + w - 1) / w ∧ ∀ Ll : List ℕ, (∀ ib < nB, ∃ t ∈ Ll, t ≤ ib ∧ ib < t + w) → (nB + w - 1) / w ≤ Ll.length` — the machine's total at s = w EQUALS ⌈n/w⌉, and no covering list of width-w windows is shorter | `hier_optimal` | Hagi/Theory/CoverageReading.lean:531 | v3.3 (C622) |

Version deltas: `hagi_master_v31` (`MasterTheoremV3.lean:128`) =
(1)–(8); `hagi_master_v32` (`:187`) = v3.1 + (9)(10); `hagi_master_v33`
(`:252`) = v3.2 + (11); `hagi_master_v34` (`:323`) = v3.3 + (12)(13)(14)
(C662): the useful first growth step (`first_step_strict_improves`,
Hagi/Theory/FunctionPreservingGrowth.lean:676), the Adam first step
(`adam_first_step_dot_pos`, Hagi/Step/AdamDirection.lean:85) and the
two-way holdout gate (`holdout_gate_two_way_delta`,
Hagi/Theory/HoldoutGateTwoWay.lean:109), all three with their
hypotheses verbatim. Each version carries the previous statement
unfolded verbatim and discharges it through ONE delegate (`hV31` /
`hV32` + projections); the engineering note of the C614 receipt: a
delegate theorem used AS the statement is ill-typed (a proof term is
not a `Prop`) — clauses live in the statement, delegates in the
proof. Clauses (5)+(8) form the two-level transfer-certified circuit
(an exact quadratic iff plus a conservative smooth sufficient level).
Axioms of every version: `propext`, `Classical.choice`, `Quot.sound`
(3). Witnesses: C600 trajMT31.lean (#check of 8 clauses), C614
trajMT32.lean (applications of (9) to L=2, G=1 — drop = 1/4 — and of
(10) to n=8128, B=4032, w=s'=64), C622 trajMT33.lean (application of
(11) at n=8128, B=4032, w=64 — total 127 = ⌈8128/64⌉, floor against
an arbitrary covering list L); all rc = 0.

### 3.18 The reading era: floor → hierarchy → w-rule → near-const → mixed-w*

C618–C628.
<!-- source: receipt C618, C623, C626, C628;
     CoverageReading.lean (ns WindowTradeoff слит сюда) -->

The formula era made every operating parameter a formula; the
reading era asks the complementary question — what does it COST
to read n bytes with width-w windows, and which w should the
machine choose? The whole line landed in five beats, and this
section states it as one arc.

**(i) The information-theoretic floor (C618).** No coverage of
[0, n) by width-w windows can use fewer than ⌈n/w⌉ windows:

> `theorem hier_total_floor (L : List ℕ) (w n : ℕ) (hw : 0 < w)`
> `(hcover : ∀ i < n, ∃ t ∈ L, t ≤ i ∧ i < t + w) :`
> `n ≤ L.length * w`

(`Hagi.Theory.CoverageReading.hier_total_floor`,
CoverageReading.lean:494). The hierarchy of §3.17 clause map (10)
ATTAINS the floor at `s = w`, `w ∣ B` —
`hier_total_min` (:462): `(hierStarts n B w w).length =
(n + w - 1) / w`, closed by `hier_optimal` (:533): total =
⌈n/w⌉ ∧ every covering list L has `(n + w - 1) / w ≤
L.length`. Geometry, not algorithm: k windows cover at most k·w
bytes (injection i ↦ (window, offset)). Two consequences,
measured: the total is CONSTANT in B at s = w — n = 100000,
w = m = 64 gives 1563 = ⌈100000/64⌉ for every B ∈ {64, 2048,
4032, 4096}, so the hypothesized interior optimum B* = √(nw) is
REFUTED by the telescoping sum; and shrinking the stride
below the width only pays: s = 32, B = 1088 reads 3033 > 1563,
strictly worse than the floor. At n = 8128 the floor-attaining
total is 127 = ⌈8128/64⌉.
<!-- source: receipt C618:47-49 (1563/3033/127); :13-18 (B*) -->

**(ii) Three cost regimes and the w-rule (C623).** With a
per-read window cost c(w), totalCost(w) = ⌈n/w⌉·c(w), and the
certified w-rule has three regimes (Hagi/Theory/
CoverageReading.lean):

- **(a) fixed cost c(w) = c:** totalCost = c·⌈n/w⌉ is
  monotonically non-increasing in w (`windowCost_fixed_mono`,
  :577, core `ceil_div_anti` :555) — the certified choice is
  w = w_max;
- **(b) linear cost c(w) = c·w:** totalCost is nearly
  width-INDEPENDENT — `w·⌈n/w⌉` sits in [n, n + w − 1]
  (`windowCost_linear_bounds`, :586) and any two widths differ
  by less than the cost of one window
  (`windowCost_linear_near_const`, :602) — w is free, choose it
  for accuracy, not budget;
- **(c) mixed cost c(w) = a + c·w^α, α > 1:** at C623 the
  interior optimum w* = (a/(c·(α−1)))^(1/α) was an honest
  Real-arithmetic sketch in STATUS.md, NOT a Lean clause.

The bridge back to (i) is `windowCost_hier` (:613): at
w ∣ B the machine's total IS ⌈n/w⌉ reads, so the certified
hierarchy total and the cost model agree. Measured table
(n = 100000; C623 #eval, re-verified bit-identical by the bench
twin in C626): w ∈ {16, 64, 256} → reads {6250, 1563, 391};
linear-regime totals {100000, 100032, 100096}, each inside the
corridor [100000, 100000 + w).
<!-- source: receipt C623:42-46; receipt C626
     (witness-сверка C623 pinned asserts) -->

**(iii) Near-const is a card (C625).** Regime (b) became
PALOMAR Card 13 (§4.7): width choice cannot buy budget savings
under linear window cost — the lower edge c·n is common to all
w, the gap is < c·w, while the read count ⌈n/w⌉ moves by
orders of magnitude.

**(iv) mixed-w* becomes a theorem (C628).** For the bench
default α = 2 the sketch is now certified (CoverageReading.lean), three clauses, Lean-verbatim:

> `theorem mixedCost_relax_min {a c w : ℝ} (ha : 0 < a)`
> `(hc : 0 < c) (hw : 0 < w) :`
> `2 * Real.sqrt (a * c) ≤ a / w + c * w`

(:630 — AM-GM: (√u − √v)² ≥ 0 at u = a/w, v = c·w);

> `theorem mixedCost_relax_min_eq {a c : ℝ} (ha : 0 < a)`
> `(hc : 0 < c) :`
> `a / Real.sqrt (a / c) + c * Real.sqrt (a / c)`
> `= 2 * Real.sqrt (a * c)`

(:650 — equality at w = √(a/c): both summands equal √(a·c), so
w* = √(a/c), the α = 2 case of w* = (a/(c·(α−1)))^(1/α), is
certified); and the discrete lower bound

> `theorem mixedCost_lower {n w : ℕ} {a c : ℝ} (ha : 0 < a)`
> `(hc : 0 < c) (hw : 0 < w) :`
> `2 * (n : ℝ) * Real.sqrt (a * c)`
> `≤ ((n + w - 1) / w : ℕ) * (a + c * (w : ℝ) ^ 2)`

(:675 — ⌈n/w⌉·(a + c·w²) ≥ 2n·√(a·c) via the ceil-bridge
`windowCost_linear_bounds` + the relaxation ×n). Honest scope:
this is a certified LOWER bound; discrete equality needs
w ∣ n and w = √(a/c) simultaneously, and general α > 1 remains
Real-calculus outside the Nat model of the file — the bench
text says "NOT a Lean clause" for α ≠ 2.
<!-- source: Hagi/Theory/CoverageReading.lean:628/:650/:675
     (statement дословно); receipt C628 -->

**(v) The bench application (C626).** `cost_regime_w` in
scripts/bench_bridge.py is the python twin of the three regimes
(exact `fractions.Fraction` arithmetic, fail-closed asserts:
linear corridor, near-const inequality w1·⌈n/w1⌉ ≤
w2·⌈n/w2⌉ + (w1 − 1), fixed optimality of w_max, mixed argmin),
exposed as `--cost-regime {fixed,linear,mixed}` in
`--mode generate-hier` with telemetry (w_chosen, reads ⌈n/w⌉,
exact total_cost, corridor, w_compare at {16, 64, 256, w_max};
instances n = 540/4032/8128/100000). The C623 numbers above are
pinned asserts in the dispatch — python and Lean #eval agree
verbatim; the C628 landing changed ZERO bench numbers (the
mixed-rule text only gained its Lean anchor at α = 2).
<!-- source: receipt C626; receipt C628 (diff
     cost_mixed.log пуст) -->

The arc closes: reading has a floor (i), the certified
hierarchy attains it, the cost model says which w to pick per
regime (ii), the counter-intuitive regime got its own card
(iii), the last grey element became a theorem (iv), and the
bench consumes all of it fail-closed (v).

### 3.19 The code-bridge era (C638–C648): what the consumer's code inherits

The full map — layer, canon, python `file:line@sha`, status — is the
single table in **§0**; the statements live in the STATUS cards. This
section adds only what a table cannot carry: how the era turned, and
the measured numbers behind the honest-gap cells.
<!-- source: STATUS.md cards C638–C648; era-index #c638-c640, #c642-c644,
     #c646-c648, #c647, #c648; receipts .tmp/C638–C648 -->

**The turn.** Until C637 primes supplied theory and HAGI_v2 consumed it.
From wave 252 the consumer checks itself against the Lean canon (its
commit 4c70f7a: "three certificate defects, found by checking it
against Lean"), and primes answers with **code bridges**: theorems
whose premises are the code's own predicates, anchored to python lines
`file:line@sha` (wave 254 = 1ae924e, wave 255 = ca52eb4; no wave 256+
claim is bridged in this section). Statuses — exact, conditional,
honest gap — are defined in §0.

**Deltas of the era, by step.** (i) Adaptive step: the clamped
multiplier equals the exact kappa only on the window (1e-5, 50]; the
old claim was computed for the unscaled step and was **400/39 ≈
10.26×** too large at lr_scale 0.05 (defect 2 of wave 252). (ii) MGDA:
the code minimizes over NORMALIZED gradients, the canon over raw ones —
literally the same point only at ε = 0 with equal ‖g_j‖; otherwise 2ε
or a different problem, and the Frank-Wolfe rate is not formalized.
(iii) Trunk growth: both Lean files are native to primes, not a port —
a class-(a) verdict, 0 new theorems. (iv) Warm-up: after step 0 Wo ≠ 0,
"function preserved after training" is false and cannot be a theorem;
what is proved is conditional on h1, and in the code h1 is NOT a fact
(warm-up is bare Adam on (W1, b1, Wo), the certified step writes to the
trunk and certifies batch CE). (v) The backtrack predicate is the
code's own (β = 1/2, exactly 9 trials, no σ·γ·⟪g,d⟫ term — "Armijo" did
not survive reading the code). (vi) The CE range lemma is about a shift
of LOGITS, so the certificate does not depend on which parameters carry
the step; the block-only JVP that would feed it is absent from the code.
(vii)–(viii) Batch → global holds deterministically for a fixed batch
and only under an iid / independent-rounds model otherwise; the slack
is k·ebGap(α/k), which the code never evaluates (no b, sig, α/k).

**Measured, behind the honest-gap cells.** On the wave-252 test config
(dim 32, hidden 64, seed 0, 12 steps) the adaptive branch is NEVER taken
(eta* ≈ 203–260 > 1): the certificate of the real code is
`ce_range_code_drop`, 12/12 claim ≤ realised drop (e.g. claim
0.07396868055108989 ≤ 0.07546329498291016). The code builds the
majorizer on the JVP displacement, the theorem is about the exact one:
in a nonlinear LM (dim 16, hidden 32, 5 steps) rollback fired 2/5
(realised drop 0 < claim 0.083/0.095). MGDA stop: float32 gap 0.0 on
all 6 probe cases. Adam is not a certified descent from t = 2, so the
backtracking gate is mandatory.

**The chain in one line.** identity start (literal) → certified step
on the block ⇒ h1 ⇒ obj ≤ fOld under both gate verdicts → batch →
global only probabilistically. Across the era the weak link moved from
"the step is not certified" to "the batch/round model is a hypothesis".
Axioms of every new theorem: propext, Classical.choice, Quot.sound.


### 3.20 Later bridges (C651–C672): deltas on the §0 map

Rows: §0 (repair, archiver, Adam, useful first step, chain rule,
holdout gate, window order; C666–C667: BitAlloc, schedule, LCB gate,
bypass, width growth; C668: first-layer W1 derivative; C669: batch
gradient and Frobenius-optimal step; C670: rank-one spectral optimum; C671: real spectral-norm bridge; C672: full step over the isometry group). Code anchors are `git show`-verified at @e9a96fc
(wave 256–257), @b3740e0 (wave 258) and @bab8aff (wave 258b); the
Nadya.txt anchors are a 2026-11-24 snapshot.
<!-- source: STATUS.md cards C651, C653–C655, C657, C660, C663, C664, C666, C667;
     era-index #c650-c651 .. #c665-c667; receipts .tmp/C651–C667 -->

**(i) Repair (C651) — linear, not geometric.** The loop accepts any
improvement > 1e-4 (no contraction factor ρ), so the theorem gives
z ≤ v − tol·(accepted rounds) and the gate may end above its pre value;
post may remain above pre, the gate is a sample estimate (≤ 8 domains ×
256 positions), and clause (2) of `master_theorem_v3` is not
instantiated (repair writes the shared trunk). Commit-message numbers,
not re-measured: +0.553 → +0.036, 20/89 rounds hit rollback.

**(ii) Archiver (C653) — the ideal coder only.** The code's claim
(archiver.py:1-4 @b3740e0) is "size within o(1) of −log₂ P(data), the
ratio IS the model's CE". Proved for len = ⌈−log₂ p̂⌉₊:
**H(p) ≤ E_p[len] ≤ H(p) + KL(p‖p̂)/log 2 + 1** (Kraft–McMillan +
`ceBits p q = entBits p + klDef p q / log 2`); at p̂ = p: H ≤ E[len] ≤
H + 1. The model is the IDEAL coder; p̂ is the 16-bit CDF
(freq = max(1, round(P·65200))); the round-trip is tests plus a measured
11/11 (5.16 bit/byte vs zlib 2.40).

**(iii) Adam (C655) — a verdict.** ⟨g, d⟩ > 0 is a code fact only at
t = 1; at β₁ = 9/10, β₂ = 999/1000, g₁ = 1, g₂ = −1/10 the second step
has ⟨g, d⟩ < 0. So the Adam step is accepted only by the measured
`backtrackAccept` (selfmodel.py:134-169 @b3740e0), and pin 26's open
lemma closes as a NEGATIVE verdict.

**(iv) Useful first step (C657) — the formula hit.** On a linear logit
carrier, **η* = 4|a|/R² and drop_max = 2a²/R²**: the first step is
certifiably useful iff the residual signal a ≠ 0 and 2a²/R² > stepEps;
at a = 0 nothing commits. Witness (.tmp/C657/traj.lean, rc=0): a = −1,
R = 2 ⇒ η* = 1, drop_max = 1/2. Pin 31 (chain rule a < 0) closed for a
LINEAR carrier in C663 (`chain_linear`, `useful_of_adam_first`) and
for the relu block only as strict descent for small η (C665); the
nonlinear certified drop is open.

**(iv-b) First layer `W1` (C668).** The pin “derivative w.r.t. W1 not
formalized” is closed for a single input x: outside the kink the logits
`reluL (W1ᵀx) b wo` are differentiable in the matrix (`hasFDerivAt_w1L`,
chain rule of the linear `W1 ↦ W1ᵀx` with `hasFDerivAt_reluL`), the
gradient is rank one, `g (i,j) = g i · x j` with
`g i = Σ_v (y v − p v)·mask i·wo i v` (`w1_grad_rank_one`), its pairing
with a perturbation Δ is `⟨p − y, J·Δ⟩ = −Σ_{ij} (g i · x j)·Δ i j`
(`w1_directional_derivative`), Adam-first on the matrix gives strict
descent for small η (`useful_of_adam_first_w1`), and the rank-one update
`(c/Σx²)·(u ⊗ x)` equals the bias shift `b + c·u`
(`w1_rank_one_step_eq_bias`). Witness .tmp/C668/traj.lean, rc = 0
(d = 3, d_ff = 4, one dead unit). Code: `_block_add`, lm.py:586 and the
`W1` parameter, lm.py:594 @ca52eb4. Still open: certified drop on W1,
**(iv-c) Batch gradient and the optimal step (C669).** Over a batch of
inputs x_t the pairing is `Σ_t⟨p_t − y_t, J_t·Δ⟩ = −Σ_{ij} G i j·Δ i j`
with the batch gradient `G i j = Σ_t g_t i · x_t j`, i.e. `Σ_t g_t ⊗ x_t`
(`batch_directional_derivative`). By Cauchy–Schwarz in the Frobenius
form, `⟨G, Δ⟩ ≥ −R·‖G‖_F` for every `Δ` with `‖Δ‖²_F ≤ R²`
(`frob_step_le`), and `Δ = −(R/‖G‖_F)·G` is admissible and attains the
bound (`sgd_step_attains`): the SGD direction is the steepest descent in
the Frobenius ball. Inside the rank-one family `Δ = u ⊗ v` (fixed u) the
pairing is `⟨v, Gᵀu⟩` (`rank_one_inner`), it is at most `‖v‖·‖Gᵀu‖ ≤
‖v‖·‖u‖·‖G‖_F` (`rank_one_le`), and `v = Gᵀu/‖Gᵀu‖` attains `‖Gᵀu‖`
(`rank_one_best_v`). Code: the consumer's Muon step on `W1`,
`W1 -= (cos_lr * 0.7) * newton_schulz_orthogonalize(m1, iters=3)`,
hagi/core.py:1755 with `newton_schulz_orthogonalize` at core.py:1350
@ca52eb4; the loss is the batch `cross_entropy` (lm.py:688 @ca52eb4).
Honest gap: the spectral-norm statement behind Muon (max `⟨G, Δ⟩` over
`‖Δ‖₂ ≤ 1` is `σ_max`, attained at `U Vᵀ`) is not proved — it needs the
spectral/nuclear duality — and the code's `W1` at core.py:1755 is not
the growth-block layer of lm.py:586 (bridge to be made). Witness
.tmp/C669/traj.lean, rc = 0 (batch of 2 inputs).

**(iv-d) The rank-one spectral optimum (C670).** Over the rank-one family
`Δ = u ⊗ v` with unit `u`, `v` (so `‖Δ‖₂ = 1`, `rank_one_spectral_norm`)
the pairing is `⟨G, u ⊗ v⟩ = Σ_i u i·(G v) i` (`rank_one_inner`), the SVD
`G = U Σ Vᵀ` gives `‖G v‖² ≤ σ_max(G)²·‖v‖²` (`rank_one_norm_bound`, the
Courant–Fischer bound for `GᵀG`), hence `⟨G, u ⊗ v⟩ ≤ σ_max(G)` for every
unit pair (`rank_one_inner_le`), and the top pair of singular vectors
attains it (`rank_one_attains`, `rank_one_spectral_step_optimal`). Code: the
consumer's orthogonalizer newton_schulz_orthogonalize (hagi/core.py:1350
@ca52eb4, called at core.py:1755 with iters=3) approximates the polar
factor `U Vᵀ` of the gradient. Honest gap: only the rank-one slice is
proved; the full Muon step (all ranks, von Neumann trace inequality /
spectral–nuclear duality) is not in the Mathlib pin, and `smax G = ‖G‖₂`
for real matrices is not derived here. Witness .tmp/C670/traj.lean, rc = 0.

**(iv-e) The real spectral-norm bridge (C671).** For a real square `G`,
`smax G = ‖G‖₂` (`smax_eq_opNorm`, Hagi/Theory/MuonSpectral.lean:333):
writing `G = U Σ Vᵀ` (`smax_svd`), the operator norm is invariant under the
orthogonal factors (`l2_opNorm_mul_orth`, via `Matrix.l2_opNorm_conjTranspose`
and `l2_opNorm_conjTranspose_mul_self`) and `‖Σ‖₂ = max_i σ i` for `σ ≥ 0`
(`l2_opNorm_diagonal_nonneg`). Consequences: `σ_max(G) ≤ ‖G‖_F`
(`smax_le_frobenius`, :354 — the spectral ball contains the Frobenius ball
of the same radius) and `‖G v‖₂ ≤ σ_max(G)·‖v‖₂` (`opNorm_mulVec_le`, :383).
Route (b) — direct, via the SVD — was used; the transfer of the complex
Flywheel theorem `spectral_norm_eq_max_singularValue` through
`Matrix.map (ofReal)` (route (a)) was not needed. Honest gap: with the bridge,
C670's statement reads «the rank-one step is optimal inside the spectral ball
among rank-one steps»; the full Muon step `U Vᵀ` still needs von Neumann /
spectral–nuclear duality; `‖u ⊗ v‖₂ = ‖u‖₂·‖v‖₂` for non-unit `u`, `v` is
not stated (only the unit case). Witness .tmp/C671/traj.lean, rc = 0.

**(iv-f) The full Muon step over the isometry group (C672).** The
orthogonalizer's ideal output is a matrix with orthonormal columns, i.e.
an isometry `ΔᵀΔ = I`. Over that group the maximum of `⟨G, Δ⟩` equals the
sum of the singular values `ssum G` (the nuclear norm `‖G‖_*`), and it is
attained at `Δ = U Vᵀ` — with no von Neumann inequality. Proof
(Hagi/Theory/MuonIsometry.lean): `⟨G, Δ⟩ = tr(GᵀΔ) = Σ_i σ i·Q i i` with
`Q = UᵀΔV` (`inner_eq_sigma_weighted_diag`, :93); `Q` is again an
isometry (`isometry_conj`, :115), hence `Q i i ≤ 1` because the column is
a unit vector (`isometry_diag_le_one`, :65), and `σ i ≥ 0`. So
`⟨G, Δ⟩ ≤ ssum G` (`isometry_inner_le_ssum`, :128) with equality at
`Δ = U Vᵀ`, where `Q = I` (`uv_transpose_attains_ssum`, :156;
`muon_step_optimal_in_isometry_group`, :175). Code bridge (read-only
@ca52eb4): the iteration `X = 0.5 * (3.0 * I_m - X @ X.T) @ X`
(core.py:1363) is started from the Frobenius-normalised gradient
(`np.linalg.norm`, core.py:1353), not the spectral one, and is run with
`iters = 3` (core.py:1755); the ideal limit is the polar factor `U Vᵀ`.
Honest gap: the theorem is about the exact isometry group — the bound on
how far three iterations are from it (a lower bound on σ_min), the
rectangular case (transpose at core.py:1358) and the convergence of the
iteration to `U Vᵀ` are not formalised; the maximum over the whole
spectral ball `‖Δ‖₂ ≤ 1` still needs von Neumann. Witness
.tmp/C672/traj.lean (rotation picture `⟨diag(3,1), R(θ)⟩ = 4·cos θ`), rc = 0.

**(v) Window order (C651 → C664).** After wave 258 the context is
`idx[p−n .. p)` but the target is `idx[pos + k]` — a k-byte gap;
measured CE 7.307 against 0.181 with the adjacent target
(.tmp/C651/logs/windows_probe.log). Wave 258b fixed the same bug in
three more oldest-first
consumers (`_read_all_windows` left pad, the train_guarded holdout
window, `generate`); commit-message numbers, not re-measured: holdout
CE 3.59..4.23 nats (was 8.13..11.56), generation path 2.25 (was 3.64).
Still open in the code: hagi/unified.py:1010 @bab8aff reads `[::-1]`
with `logits(x)[0]`.

**(vi) The certified warm-up, simulated (C654).** Bench mode
`certified-warmup-sim` (scripts/bench_bridge.py) compares a certified
arm (python twin of `_certified_finite_step`, COMMIT iff drop > 1e-12,
<= 600 steps) with the plain Adam arm of unified.py on the bench
carrier with the trunk frozen - a simulation, not a HAGI_v2 run.

| corpus | fOld | certified | plain Adam (steps) | verdict |
|---|---|---|---|---|
| snapshot (34 pts, T=2, n_params=66) | 3.761650 | 2.783855 (600 COMMIT, 0 HOLD, 0 halvings, sum_drop 0.561600) | 3.583951 (2) | PASS |
| --live-corpus (C610 fallback, T=2, n_params=102) | 4.811144 | 3.394217 (600 COMMIT, 0 HOLD, 0 halvings, sum_drop 0.780696) | 4.444299 (4) | PASS |

The honest fact: plain Adam ALSO lowered the objective - without a
certificate. The certificate is a batch mean over all points, not a
task mean.
<!-- source: .tmp/C654/receipt.md, snap.out, live2.out (C654) -->


## 4. Benchmarks (measured only)

### 4.1 mini-HAGI

3 tasks, 2-block trunk, 2 grow phases, holdout, canonical
objective. Full pipeline (A-trunk2 → C-gpm1 → E-gpm2relax →
F-quant → G-stop): **15 certified steps**; certified objective
chain monotone; gpm2 phase: full-GPM arm 0 committed / 4 honest
HOLDs vs relaxed arm 4 committed (k = 1, eps = 1/10);
zero forgetting in the full-GPM arm; relaxed-arm forgetting ≤
bound at every step (asserts green, exit 0).

### 4.2 vs-trainer certified forecasts

31 measured points (25 train / 6 holdout); 8 committed training
steps; **6/6 holdout predictions certified** (disjoint bands);
accuracy 4/6 (bounded by the model, not the certificate —
certified midpoints agree with the true softmax argmax 6/6);
adaptive band-tightening was available (nm doubling to 1024) but
not needed: all bands disjoint already at n = m = 4.

### 4.3 What self-improvement actually yields on live data

<!-- source: receipt C549; receipt C551 -->

On the full live corpus (§3.14) the loop finds few laws — and
that outcome is itself the honest headline. What
self-improvement demonstrably yields even when "laws are
scarce" are three certified SYSTEM properties:

1. **Isolated memory.** forgetA = 0 structurally — per-task
   adapters need no projections or budgets; measured as
   bit-exact parameter-snapshot asserts after every training
   phase of all 113 domains, 113/113.
2. **Monotone coverage.** Accepted primitives only ADD coverage
   (`coverage_append_monotone`, asserted bit-exact per
   iteration in both C549 and C551) — the loop cannot forget
   what it has covered, whatever the data.
3. **Self-termination under budget.** The EB gate stops the run
   when candidates stop paying (C551 it4: 0 accepted; C549
   iteration 7: 0 accepted with MAX_ITER = 8 unspent;
   n_EB < n_Hoeffding at every iteration) — the stopping rule
   is certified, not a heuristic timeout.

These properties hold on live data regardless of how many laws
the corpus actually contains; the loop measures that number
instead of assuming it.

### 4.4 Impact note: the first external consumer (wave205)

<!-- source: receipt C557 -->

The theory also acquired its first EXTERNAL consumer. The
HAGI_v2 runtime recheck during the C557 phase analysis observed
waves 205–207c, and wave205 synchronized the runtime's theory
state with this repository at commit ab28579e: the
bridge that exports the certified constants to the runtime
went from an unused artifact to a live dependency — the first
real use of this theory by an external system. This is an
existence proof of external synchronization, not yet an
evaluation of downstream benefit (pinned below, §5.17).

### 4.5 From proxies to formulas: the certified-parameters era

<!-- source: receipt C597 (auto-k*, 2788 бит/33 snap); receipt C601 + gate_check.log (certified gate, nlBudget 24/25, G≈0.03, 99.66 vs 5.43); receipt C602 + trajSpan.lean (adaptive span, n≤4032, s=17>w=9, 1152/s17→65 окон); receipt C594 (wave232 round-trip 33 мин); receipt C595 + docs/PREMISES-STATUS.md (premise audit); receipt C596 (bench sweep); .omc/analysis/era-index.md#c599-c602 (эра консолидации) -->

The frontier era replaced hand-set proxies of the runtime era by
FORMULAS imported verbatim from Lean theorems, each landing as a
bench mode with telemetry:

| Proxy (runtime era) | Certified formula (Lean anchor) | Measured effect (receipt) |
|---|---|---|
| manual snap grid `GS_K=40` | `k* = ⌈log₂(L·d/ε)⌉−1` (`snap_k_eq_ceil`, GrowSnap.lean:342, C593) | auto-k* in 4 snap modes (grow-snap k*=18/19/20, trunk-freeze k*=11); **2788 bits saved vs legacy k=40 over 33 snap events** (telemetry bits_saved_vs_legacy, fixture run, C597) |
| warm-start gate `ce ≤ 0.5` (HAGI_v2 wave232 proxy) | warm ⟺ `start_gap = f(θA) − f(0) ≤ n•nlBudget γ L G` (`certified_transfer_gate` ← `sufficient_negative_transfer` C592; `nlBudget = γG² + Lγ²G²/2`) | exact boundary: nlBudget(1/5, 2, 2) = 24/25; gap 24/25 → warm, 25/25 → cold-certified; live bench 3 pairs warm, forgetA = 0, T1-positive (C601) |
| window truncation `windows[-max_span:]` | adaptive step `s = min(w, ⌈(n−w)/(m−2)⌉)` (`covStartsStep_adaptive_covers`, CoverageReading.lean:233, C602) | w=m=64: n=540 → s=8, 61 windows, covered; n=4032 → s=64 (boundary), covered; n=4160+ → honest INFEASIBLE (None) instead of silent truncation (C602) |

**Coverage iff.** `covStartsStep_covers` (CoverageReading.lean:184,
C602) is exact: windows of width w with step s cover `[0, n)` IFF
`s ≤ w` — necessity by witness s=17 > w=9 leaving byte 9 in a hole;
the adaptive budget form keeps windows ≤ m (`covStartsStep_len_le`,
:220).

**The negative-cycle pattern (C598 → C602).** A measured defect
(truncation loses byte 0: `covStarts_trunc_uncovered_zero`,
CoverageReading.lean:130) → negative theorem → exact iff →
fail-closed code with an honest INFEASIBLE branch. This
theory-to-code round trip reproduces the wave232 result — where the
HAGI_v2 runtime integrated the C592 sufficient-transfer gate with a
theory→code round-trip of 33 minutes (C594 receipt) — now fully on
our side of the bridge.

**Debt closure.** The premise debt was audited rather than assumed:
C595 produced docs/PREMISES-STATUS.md (full open-premise table,
classes and discharge routes; PROVEN-NOW 1, PARTIAL 2, DEAD 0); C596
swept all 35 bench modes into either PASS (13) or honest corpus-drift
ABORT (22) with zero tracebacks — no silent failures left in the
harness (see pin 18).

### 4.6 The formula-driven era: every parameter a formula

<!-- source: block — receipt C606 (γ*=1/L, drop G²/(2L),
     witness L=2,G=1 drop 1/4); receipt C609 (γ_auto
     5000000/10470759≈0.477, 13500000/25944901≈0.520,
     156250/234227≈0.667, verdicts идентичны pre); receipt
     receipt.md (B=4032, s=w, per-block 63–64, witness n=8128
     [63,63,1] peak 63; одноуровневый 127 окон > 64);
     receipt C613 (n=100000: 25 блоков, 24×63+51,
     total 1563, peak 63; HierEval #eval 3/[63,63,1]/63);
     receipt C607 (null-ce skip 5 ключей, 18 режимов
     оживлены); receipt C608 (snapshot 35 ключей, live
     45/41-key ABORT); receipt C610 (три уровня,
     fail-closed exit 3); anchors rg 2d619fc8 -->

The proxy→formula program of §4.5 is now COMPLETE for the five
operating parameters of the loop: each is a formula with a Lean
anchor, a bench application, and measured bits —

| Parameter | Certified formula | Lean anchor (file:line) | Bench application | Measured bits |
|---|---|---|---|---|
| snap grid | `k* = ⌈log₂(L·d/ε)⌉ − 1` | `snap_k_eq_ceil`, GrowSnap.lean:342 (C593) | auto-k* in 4 snap modes | 2788 bits saved vs legacy k=40 over 33 snap events (C597) |
| transfer gate | warm ⟺ `start_gap ≤ n•nlBudget γ L G`, `nlBudget = γG² + Lγ²G²/2` | `nlBudget`, NegativeTransfer.lean:242 (C592/C601) | TGC/ATA modes | exact boundary nlBudget(1/5,2,2) = 24/25; 3 warm pairs, forgetA = 0 (C601) |
| window span | `s = min(w, ⌈(n−w)/(m−2)⌉)`; iff `s ≤ w` | `covStartsStep_adaptive_covers`, CoverageReading.lean:233 (C602) | adaptive-span / generate-hier tables | n=540 → s=8, 61 windows; n=4032 boundary s=64; n≥4160 honest INFEASIBLE (C602/C613) |
| step size | `γ* = 1/L`, `nlDrop (1/L) L G = G²/(2L)` | `nl_drop_optimal`, NegativeTransfer.lean:481 (C606) | auto-LR = 1/(2·trace H̄) in ATA/TGC (C609) | γ_auto = 0.477 / 0.520 / 0.667 (exact Fractions) vs old 1/10; verdicts bit-identical to pre (C609) |
| window layout | `B = w(m−1)`, `s = w` ⇒ `(B−w)/s+2 = m`; peak ≤ m | `hier_peak_window_budget`, CoverageReading.lean:314 (C611) | generate-hier mode (C613) | n=100000: 25 blocks, 24×63+51, total 1563, peak 63; single-level n=8128 needs 127 > 64 (INFEASIBLE), hier [63,63,1] peak 63 (C611/C613) |
| window width rule | fixed: w = w_max; linear: near-const corridor [c·n, c·(n+w)); mixed α=2: w* = √(a/c), lower ⌈n/w⌉·(a+c·w²) ≥ 2n·√(a·c) | `windowCost_fixed_mono`/`windowCost_linear_near_const`/`mixedCost_relax_min(_eq)`/`mixedCost_lower`, CoverageReading.lean:575/:602/:630/:650/:675 (C623/C628) | `--cost-regime {fixed,linear,mixed}` in generate-hier (C626) | n=100000, w∈{16,64,256}: reads 6250/1563/391; linear totals 100000/100032/100096 in corridor [100000, 100000+w); fixed optimum w=256 → 391 reads (C623/C626) |
<!-- source: строка w-rule — receipt C623:42-46; receipt C626 (cost_regime_w, pinned asserts, w_max=256→391); receipt C628 (mixedCost_* freeze 8844); якоря WindowTradeoff-блока в CoverageReading.lean rg HEAD (T2 repin) -->

Two structural remarks. First, the optimal-step clause is
self-contained: `φ(1/L) − φ(γ) = (G²/(2L))·(1 − Lγ)² ≥ 0` is a
complete square (`nlDrop_le_optimal`, NegativeTransfer.lean:467),
so γ* = 1/L is the global maximizer of the guaranteed drop on
all of ℝ — not merely on the descent zone [0, 2/L]; the
candidate γ* = 2/(3L) from the draft was REJECTED as an
arithmetic slip (C606 receipt). Second, the hierarchy is exact,
not heuristic: with `s = w`, `B = w·(m−1)` the per-block budget
`(B−w)/s + 2` EQUALS m, so the same peak-m streaming budget that
bounded the single level at `n ≤ w(m−1) = 4032` (w=m=64) now
covers ANY n — the witness n=8128 lands [63, 63, 1] with peak 63
in BOTH Lean (`C611`) and the bench twin
(`HierEval.lean` #eval) — a literal python==Lean match.

**Corpus policy as measurement infrastructure (C607/C608/C610).**
Formula-driven benches are only as good as the corpus they read,
and the live corpus drifts (wave240 of HAGI_v2). Three fixes
landed, in one resolution point of `bench_bridge.py`: (i) null-ce
tolerance — wave `PARTIAL_LAW` records with `ce: null` (5 keys:
law_alphabet, law_double, law_fib_sum, law_plus3, law_xor_ff)
are skip-warned and filtered instead of aborting, reviving 18
modes to exit 0 while keeping content aborts fail-closed;
(ii) snapshot pinning — the default corpus is a pinned 35-key
snapshot (34 ns_* + law_alphabet) selected by grow-snap PASSING
its certified bound; live 45-key and 41-key corpora ABORT on
that same bound — a data property, not timing; (iii)
three-level fallback — default snapshot → structural lack (≥2
const-cluster domains) → stderr WARNING + LIVE-FALLBACK, with
`--snapshot-corpus` fail-closed (exit 3) and `--live-corpus`
opt-in. The result: bench tables are deterministic and
drift-immune by default, and every deviation is an explicit,
telemetered decision.

### 4.7 The PALOMAR niche: an honest external check

<!-- source: receipt C616 + C616
     / palomar_q1.json / palomar_q2.json (API totals {"results":
     1293, "projects": 983}, entries [] по всем запросам;
     revision 1122); receipt C615 + docs/PALOMAR-CARDS.md
     (Cards 9–11, якоря rg HEAD 609726d1); HAGI_v2 recheck ce68e21
     wave240 (C616 receipt) -->

PALOMAR (palomar-registry.org) is a registry of formally
verified results. A direct API check
(`data.palomar-registry.org/api/v1/results`) was run against the
formula-era statements — queries `hier_covers`, `covStartsStep`,
`nlDrop`, `adaptive span`, `optimal step size`, `window coverage
hierarchy` over the full registry (totals 1293 results / 983
projects, revision 1122) returned ZERO entries for every query.
The honest finding, stated as measured: **the niche is empty —
none of the Cards 9–11 statements is absorbed by the registry**,
and uploading them is a user-side step, not claimed here. This
is a one-point-in-time check; the registry grows and the
claim is not that the niche stays empty, only that it was empty
at the checked revision.

The three cards submitted-ready (docs/PALOMAR-CARDS.md, C615;
anchors rg-verified, statements Lean-verbatim):

- **Card 9 — optimal step size.** `nlDrop γ L G = γG² − Lγ²G²/2`;
`nlDrop_le_optimal` (NegativeTransfer.lean:467): `∀ γ,
nlDrop γ L G ≤ nlDrop (1/L) L G` at `L > 0`, via the complete
square `φ(1/L) − φ(γ) = (G²/(2L))(1 − Lγ)²`; `nl_drop_optimal`
(:481): `nlDrop (1/L) L G = G²/(2L)`; `nl_drop_bound` (:443),
`nlDrop` (:434), `nlStep` (:231). Bench numbers: γ_auto =
0.477/0.520/0.667 exact Fractions vs the old constant 1/10
(C609).
- **Card 10 — hierarchical window coverage at any n.**
`hier_covers_any_n` (CoverageReading.lean:282): for `0 < B`,
`0 < s ≤ w`, every `i < n` lies in a window of `hierStarts n B w
s` — no upper bound on n; `hier_peak_window_budget` (:315):
peak windows per block ≤ m (peak ≠ total, stated honestly).
Bench numbers: n=100000 → 25 blocks, 24×63+51, total 1563, peak
63; Lean witness n=8128 → [63, 63, 1], peak 63.
- **Card 11 — adaptive-span iff and its exact budget.**
`covStartsStep_covers` (CoverageReading.lean:184): coverage of
`[0, n)` IFF `s ≤ w` — necessity by witness s=17 > w=9 leaving
byte 9 in a hole; `covStartsStep_len_le` (:220): window count
`(n−w)/s + 2 ≤ m`; boundary `s = w`: `n ≤ w(m−1) = 4032` (w=m=64),
beyond which the single level is honestly INFEASIBLE — removed
by the hierarchy of Card 10.

Two more cards joined the registry draft in the reading era
(docs/PALOMAR-CARDS.md, C621/C625; anchors rg-verified,
statements Lean-verbatim). Honest scope: the C616 niche check
covered Cards 9–11 only; the C630 recheck covered all 13 cards
and C658 all 17 (docs/PALOMAR-CARDS.md) — 0 overlaps.
<!-- source: receipt C621 (Card 12, DocLint/freeze logs);
     receipt C625 (Card 13); receipt C616
     (ниша-проверка — только Cards 9–11) -->

- **Card 12 — information-theoretic floor for reading n bytes
with width-w windows.** Any covering list L of [0, n) by
width-w windows satisfies `n ≤ L.length * w`
(`hier_total_floor`, CoverageReading.lean:494), and the
hierarchy ATTAINS the floor at `s = w`, `w ∣ B`:
`hier_total_min` (:462) — `(hierStarts n B w w).length =
(n + w - 1) / w`; `hier_optimal` (:533) closes the optimum
total = ⌈n/w⌉ ∧ ∀ covering L: ⌈n/w⌉ ≤ L.length. Bench numbers
(C618): n = 100000, w = m = 64 → total 1563 = ⌈100000/64⌉,
constant over B ∈ {64, 2048, 4032, 4096}; s = 32 → 3033 > 1563;
n = 8128 → 127. The interior optimum hypothesis B* = √(nw) is
refuted by the telescoping sum — the total does not depend on
B at s = w.
- **Card 13 — linear window cost makes the total budget nearly
width-independent.** For any `0 < w1, w2`:
`w1 * ((n + w1 - 1) / w1) ≤ w2 * ((n + w2 - 1) / w2) +
(w1 - 1)` (`windowCost_linear_near_const`,
CoverageReading.lean:600) — totalCost(w1) ≤ totalCost(w2) +
c·(w1 − 1) and symmetrically, with the corridor n ≤ w·⌈n/w⌉ ≤
n + w − 1 (`windowCost_linear_bounds`, :586); contrast regime
(a) `windowCost_fixed_mono` (:577): fixed cost makes w = w_max
optimal; bridge `windowCost_hier` (:613). Bench numbers
(C623/C626): n = 100000, w ∈ {16, 64, 256} → reads {6250,
1563, 391}, linear totals {100000, 100032, 100096} — all in
[100000, 100000 + w). Regime (c) mixed cost: at α = 2 the
AM-GM optimum w* = √(a/c) and the lower bound
⌈n/w⌉·(a+c·w²) ≥ 2n·√(a·c) are Lean theorems (C628,
§3.18 (iv)); general α > 1 remains a Real-arithmetic sketch,
not a Lean clause.

## 5. Honest limitations (pins)

1. **Measurement premise.** Certified prediction is conditional
   on `BandDescribes z lo hi` — a MEASUREMENT premise
   (`Hagi/Theory/TrainerBenchmark.lean:60`), not derived from the
   model.
2. **ε-tolerances are measured, not tuned.** eps = 1/10 in
   mini-HAGI is a PIN: eps = 1/100 is impossible at any k < rank
   (tail² budget fails — measured tail2max_by_k telemetry). The
   ε in the cycle theorem is a premise-channel allowance.
3. **Scale.** mini-HAGI: 3 tasks, small d; vs-trainer: 31 points.
   No large-scale claims.
4. **Premise-form channels.** falseCommit bounds are premise-form
   with cited discharge routes; in general they
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
   comparisons (e.g. §3.5 vs §3.6) use each run's own receipted
   measurements; objective values are not comparable across
   corpus versions.

9. **EB contrast is data-dependent.** The live full-loop corpus
   shows an EB-vs-Hoeffding sample contrast of only 1.12×
   (n_EB 9649 ≤ n_Hoeffding 10851) against the 27.49× of
   the C539 calibration point (eps = R/128 on a small residual
   range) — a property of the data, not of the bound form.
10. **Polar-Express upper end.** The certified final spectral
   box is [9/512, 1049/1024] ≈ [0.0176, 1.0244]: the upper end
   exceeds 1 by 2.4% — an honest correction to the expectation
   that minimax Newton–Schulz pins the spectrum top at exactly 1.
11. **OE completeness is probe-relative.** `oe_search_complete`
   guarantees no loss of probe-consistent solutions inside the
   enumerated space; it does not promise that a solution exists
   in the space (one position stayed uncovered in C547 after the
   space was exhausted), nor semantic program equivalence.
12. **Synthetic laws do not transfer.** The layered laws of the
   C549 corpus (const 0, snap(256·x0+32·x3), +32·x2) cover
   0/113 positions of the real full-corpus targets (C551
   c549_stability) — the layered targets were a construction of
   C549. §3.13's compositional chain demonstrates the mechanism,
   not a claim about the live corpus.
13. **Live-corpus coverage is constant clusters only.** The
   93.8% (106/113) coverage of C551 is achieved entirely by
   constant clusters; not one linear law was found (all
   candidates < 5 new positions). Measured applicability
   boundary: the real corpus is less deterministic than any
   synthetic layered corpus we constructed.
14. **EB-stop before budget.** C551 stopped at iteration 4
   (0 accepted) and C549 at iteration 7 (0 accepted, MAX_ITER =
   8 unspent): the certified stop fired as designed, but on
   data this weak it may fire before any non-constant structure
   is found — the stopping rule is data-limited, not
   budget-limited.
15. **The corpus is live and growing.** The `unified_ledger`
   grew from 113 points (C551–C556) to 115 points by C558
   (measured in-run; snapshot frozen per run, lesson C535).
   Cross-era numeric comparisons (e.g. §3.15 vs §3.16) use each
   run's own receipted snapshot; coverage ratios (106/113 vs
   108/115) are not comparable across corpus versions.
16. **The EB-stop did not fire in the v3 assembly.** In the
   C558 trace every iteration committed (drop > 0), so the EB
   branch (commit = 0 ⇒ STOP) never triggered; the actual stop
   was the budget MAX_ITER = 6. The certified stop is exercised
   live only on weaker data (pin 14) — in the v3
   assembly it is budget-limited, honestly.
17. **External consumer is a synchronization event, not a
   result.** The wave205 consumer of §4.4 proves the bridge is
   used; it does not measure any downstream benefit to the
   HAGI_v2 runtime.
18. **Adaptive-span INFEASIBLE boundary.** Full coverage within a
   window budget m is IMPOSSIBLE in principle for n > w + (m−2)·w
   ≈ 4032 at w = m = 64 (`covStartsStep_adaptive_covers` premise,
   C602) — the bench reports INFEASIBLE (None) rather than
   silently truncating; covering longer inputs needs a different
   (e.g. hierarchical) scheme, not this one.
19. **The smooth transfer gate is conservative, not exact.** On a
   measured adversarial pair the quad-iff (clause 5) correctly
   certifies cold while the smooth gate (clause 8) says warm: the
   measured gradient bound G ≈ 0.03 makes the sufficient budget
   99.66 exceed the start_gap 5.43 (C601 bench) — sufficiency, not
   iff; the exact answer is the quadratic clause only. The G
   premise is measured over the realized trajectory.
20. **Open premises are counted, not hidden.** STILL-EXTERNAL:
   46 registry premises (31 empirical + 14 model + 1 mathematical)
   + 11 operational + 11 unprefixed; full budget 106 h_emp-binders
   over 36 files; PROVEN-NOW 1 (h_emp_var), PARTIAL 2
   (h_emp_fiber, h_emp_dist), DEAD 0 (docs/PREMISES-STATUS.md,
   C595 audit).
21. **Bench corpus drift.** The live unified_ledger was pruned
   185 → 11-12 keys before C596; 22 of 35 bench modes honestly
   ABORT (exit 3, corpus-drift) rather than fabricate guarantees
   on a starved corpus (C596/C597 sweeps). Cross-mode numeric
   claims in §4.5 use the C597 fixture run (20 keys) and the C601
   gate_check witnesses.
22. **Code bridges are pinned to a sha, and the code drifts.**
   Every code anchor of §0 is `file:line@sha` (wave 254
   1ae924e, wave 255 ca52eb4). At HAGI_v2 HEAD b3740e0 (wave 258)
   the lines moved (`_certified_finite_step` lm.py:826 → :831, refine
   loop :999 → :1007, `MAX_BLOCKS` 2 → 4, warm-up lr 3e-3 → 1e-3);
   waves 256–258b are bridged at @e9a96fc / @b3740e0 / @bab8aff; the
   Nadya.txt anchors are a 2026-11-24 snapshot, not a git sha. The tree was read-only for primes.
23. **The real certificate is the range branch.** On the wave-252
   test config the adaptive branch of `_adaptive_step` is never taken
   (eta* ≈ 203–260 > 1); `ce_adaptive_code_drop` is a bridge to a
   branch the code does not exercise on that config, and its window
   (1e-5, 50] is a real hypothesis (C638).
24. **Tangent vs exact displacement.** The code builds the CE
   majorizer on a JVP; the theorem is about the exact logits. In the
   nonlinear LM rollback fired on 2/5 steps (C638) — the bridge is
   about the certificate, the rollback is about the residual, and
   the residual is not bounded (C638).
25. **Warm-up is not certified in the code.** h1 of `warmup_safe` is a
   hypothesis: the warm-up of `_maybe_grow` is bare Adam
   (unified.py:423-433 @ca52eb4). The certified-step contract
   (`CertifiedFiniteStep`, lm.py:826) writes to the trunk, not to the
   block. Closing this is an EXTERNAL push
   (`docs/PROPOSAL-certified-warmup.md`, C644; numbers not measured).
26. **Backtracking is not Armijo.** The wave-254 predicate has no
   sufficient-decrease term; `backtrack_accept_drop` is a bridge to
   the code's own accept test, which is called only from the self-test
   (C643). "Adam EMA descent" ⟨g, m̂/√v̂⟩ ≤ 0 is NOT a code fact;
   `adam_inner_nonneg` is unproved and not included. VERDICT (C655,
   §3.20 (iii)): ⟨g, d⟩ > 0 holds only at t = 1; from t = 2 Adam
   is not a certified descent — the lemma is false as stated.
27. **Block-only JVP is implementation.** `certified_step_block_of_range`
   is carrier-free because the range lemma is about logits; the
   range of Δz over the block parameters with a frozen trunk must be
   computed by the code, which has no functional block logits (C646).
   UPDATE (C657): given that range R and a descent signal a < 0, the
   useful step is η* = 4|a|/R² with drop 2a²/R².
28. **iid batch and independent rounds are models, not code facts.**
   The code samples without replacement and updates θ between the 8
   rounds, so the rounds are dependent; `certified_rounds_union` is
   conditional on the product model `roundP`. WOR conservativity
   (FCP ≤ 1) is not formalized — Mathlib has no lemma. The code
   computes neither b/sig nor the per-round level α/k (C647, C648).
29. **Holdout gates are measured.** Both the keep-iff-holdout gate of
   the growth path and the `wb − wa > total_bound` test of the
   controller compare measured holdout values; no theorem relates
   train obj to holdout CE. The "forgetting 4× lower" of wave 255 is
   an A/B on 6 chunks from one checkpoint (commit message), not a
   theorem (C640, C642, C643).
30. **U2: global reachability of a useful block is open.**
   `useful_first_step` proves the LOCAL statement (η* = 4|a|/R²,
   drop_max = 2a²/R²) under a < 0. "An expressive block can reach a
   drop ≥ δ in many steps" needs an optimization guarantee on a
   non-convex landscape plus a UAT on a finite grid; primes has neither
   (no UAT statement at all), and the code's random W1 gives a ≠ 0 only
   probabilistically (C657).
31. **The descent signal a < 0 is a hypothesis.** UPDATE (C663/C665):
   for a LINEAR logit carrier the link is proved (`chain_linear`,
   `useful_of_adam_first`), and for the relu block strict descent for
   small η is proved (`useful_of_adam_first_relu`), and for the first-layer
   matrix W1 as well (C668, `hasFDerivAt_w1L`, `useful_of_adam_first_w1`);
   the certified drop magnitude on the nonlinear carrier is open, and a < 0 still enters
   the useful-step theorem as a hypothesis. hlin (linear logit displacement in η) is a code-side
   JVP fact at Wo = 0, not a theorem (C657).
32. **Without-replacement conservativity is not formalized.** The code
   samples batches without replacement; `batch_drop_generalizes` assumes
   iid. The finite-population factor (N−n)/(N−1) ≤ 1 is intuition only:
   Mathlib has no such lemma (rg), and the price is an
   order-statistics/FCP lemma (C647, C648).
33. **The range-coder round-trip is tests, not a theorem.** The
   codelength bounds (C653) are for the IDEAL coder ⌈−log₂ p̂⌉₊;
   archiver.py has no Lean model (a nonempty-interval invariant, a
   searchsorted lemma and a renorm invariant; est. ≥ 400 lines).
   `trit_roundtrip` is a positional pack. "Within o(1) of −log₂ P" for
   the range coder is a classical fact, not proved here. Lossless =
   11/11 measured + 6 tests (C651, C653).
34. **The certified warm-up is a simulation.** The C654 bench
   (`certified-warmup-sim`) runs the python twin of the certified step
   on the bench carrier, not in HAGI_v2; its PASS is obj_final ≤ fOld by
   construction, and plain Adam also lowered obj in both runs. The
   holdout gate that would accept such a block in the code remains the
   measured test of pin 25 (C654).
<!-- source: STATUS.md cards C638–C657 (pins 22–29: C638–C648; 30–34: C651–C657); era-index
     #c638-c640 / #c642-c644 / #c646-c648 -->

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

## Appendix A: anchor table (all rows re-verified at HEAD e160b7ec)

| Anchor | File:line | Cycle |
|---|---|---|
| certify_then_commit_sound | Hagi/Theory/CertifyThenCommit.lean:327 | C463 |
| adaptive_descent | Hagi/Theory/AdaptiveMajorizer.lean:713 | C462+ |
| kappa_le_expR | Hagi/Theory/AdaptiveMajorizer.lean:309 | C471 |
| fisher_quant_loss_bound | Hagi/Theory/MergeQuant.lean:204 | C472 |
| rank_trunc_forgetting_bound | Hagi/Theory/Continual.lean:239 | C498 |
| gpm_tradeoff | Hagi/Theory/Continual.lean:346 | C498 |
| cert_pred_adaptive | Hagi/Theory/Softmax.lean:810 | C495/C502 |
| grow_blocks_repeat_sound | Hagi/Theory/GrowTrunkBlock.lean:148 | C506 |
| snap_preserves_objective_bound | Hagi/Theory/GrowSnap.lean:81 | C521 |
| grow_snap_cycle_sound | Hagi/Theory/GrowSnap.lean:145 | C521 |
| hybrid_step_sound | Hagi/Theory/Continual.lean:456 | C510 |
| rollback_gate_sound | Hagi/Theory/RollbackGate.lean:99 | C530 |
| adapter_neutral_B | Hagi/Theory/AdapterGrowth.lean:101 | C532 |
| adapter_step_certified | Hagi/Theory/AdapterGrowth.lean:190 | C532 |
| adapter_snap_cycle_sound | Hagi/Theory/AdapterGrowth.lean:281 | C533 |
| rank_select_sound | Hagi/Theory/AdapterGrowth.lean:326 | C535 |
| adapter_stack_rank_bound | Hagi/Theory/AdapterGrowth.lean:414 | C536 |
| adapter_merge_params | Hagi/Theory/AdapterGrowth.lean:441 | C536 |
| adapter_merge_error_bound | Hagi/Theory/AdapterGrowth.lean:455 | C536 |
| naive_decay_leak | Hagi/Theory/WeightDecayLeak.lean:126 | C538 |
| wd_gpm_step_sound | Hagi/Theory/WeightDecayLeak.lean:157 | C538 |
| empirical_bernstein_bound | Hagi/Probability/EmpiricalBernstein.lean:208 | C539 |
| empirical_bernstein_mean_bound | Hagi/Probability/EmpiricalBernstein.lean:286 | C539 |
| oe_search_complete | Hagi/Theory/OEComplete.lean:80 | C540 |
| ce_total_eq_residual | Hagi/Theory/ExactBypass.lean:90 | C541 |
| exact_gate_sound | Hagi/Theory/ExactBypass.lean:97 | C541 |
| adapter_isolation_zero_forgetting | Hagi/Theory/AdapterGrowth.lean:564 | C544 |
| adapter_per_task_sound | Hagi/Theory/AdapterGrowth.lean:579 | C544 |
| trunk_update_needs_projection | Hagi/Theory/AdapterGrowth.lean:614 | C544 |
| polar_express_step3_bound | Hagi/Optimization/PolarExpressCert.lean:372 | C545 |
| full_loop_sound | Hagi/Theory/MiniHagiLoop.lean:64 | C547 |
| IterState | Hagi/Theory/MiniHagiLoop.lean:117 | C549 |
| iterStep | Hagi/Theory/MiniHagiLoop.lean:122 | C549 |
| coversPrim | Hagi/Theory/MiniHagiLoop.lean:128 | C549 |
| coverage_append_monotone | Hagi/Theory/MiniHagiLoop.lean:134 | C549 |
| iterative_loop_sound | Hagi/Theory/MiniHagiLoop.lean:154 | C549 |
| universal_loop_corpus_mono | Hagi/Theory/MiniHagiLoop.lean:190 | C551 |
| selfCompressParams | Hagi/Theory/AdapterGrowth.lean:691 | C555 |
| self_compress_params_bounded | Hagi/Theory/AdapterGrowth.lean:696 | C555 |
| self_compress_params_contrast | Hagi/Theory/AdapterGrowth.lean:706 | C555 |
| self_compress_loop_sound | Hagi/Theory/AdapterGrowth.lean:722 | C555 |
| distillAdapter | Hagi/Theory/AdapterGrowth.lean:773 | C556 |
| constant_distill_exact | Hagi/Theory/AdapterGrowth.lean:782 | C556 |
| distill_prob_one | Hagi/Theory/AdapterGrowth.lean:803 | C556 |
| distill_coverage_preserved | Hagi/Theory/AdapterGrowth.lean:819 | C556 |
| distill_param_count | Hagi/Theory/AdapterGrowth.lean:832 | C556 |
| distill_params_total | Hagi/Theory/AdapterGrowth.lean:839 | C556 |
| symbolic_storage_cheaper | Hagi/Theory/AdapterGrowth.lean:848 | C556 |
| v3_assembly_sound | Hagi/Theory/AdapterGrowth.lean:884 | C558 |
| master_theorem_v3 | Hagi/Theory/MasterTheoremV3.lean:83 | C576 |
| auto_transfer_gate_sound | Hagi/Theory/AutoTransferGate.lean:139 | C577 |
| fact_append_preserves | Hagi/Theory/FactLedger.lean:59 | C579 |
| fact_lookup_monotone | Hagi/Theory/FactLedger.lean:67 | C579 |
| rangeWrap_inrange | Hagi/Theory/RangeWrap.lean:43 | C581 |
| rangeWrap_fixed_point | Hagi/Theory/RangeWrap.lean:53 | C581 |
| selectW_spec | Hagi/Theory/AdaptiveContext.lean:51 | C582 |
| selectW_occam_minimal | Hagi/Theory/AdaptiveContext.lean:73 | C582 |
| selectW_budget_bound | Hagi/Theory/AdaptiveContext.lean:101 | C582 |
| consolidate_prompt_empty | Hagi/Theory/KnowledgeConsolidation.lean:66 | C584 |
| remember_preserves_pages | Hagi/Theory/KnowledgeConsolidation.lean:72 | C584 |
| learn_from_dialog_archives | Hagi/Theory/KnowledgeConsolidation.lean:79 | C584 |
| covStarts_covers | Hagi/Theory/CoverageReading.lean:54 | C598 |
| covStarts_trunc_uncovered_zero | Hagi/Theory/CoverageReading.lean:130 | C598 |
| covStartsStep_covers | Hagi/Theory/CoverageReading.lean:184 | C602 |
| covStartsStep_adaptive_covers | Hagi/Theory/CoverageReading.lean:233 | C602 |
| hagi_master_v31 | Hagi/Theory/MasterTheoremV3.lean:128 | C600 |
| snap_k_eq_ceil | Hagi/Theory/GrowSnap.lean:342 | C593 |
| nlBudget | Hagi/Theory/NegativeTransfer.lean:242 | C592 |
| smooth_obj_transfer_bound | Hagi/Theory/NegativeTransfer.lean:386 | C592 |
| covStartsStep_len_le | Hagi/Theory/CoverageReading.lean:220 | C602 |
| hagi_master_v32 | Hagi/Theory/MasterTheoremV3.lean:187 | C614 |
| nlStep | Hagi/Theory/NegativeTransfer.lean:231 | C606 |
| nlDrop | Hagi/Theory/NegativeTransfer.lean:434 | C606 |
| nl_drop_bound | Hagi/Theory/NegativeTransfer.lean:443 | C606 |
| nlDrop_le_optimal | Hagi/Theory/NegativeTransfer.lean:467 | C606 |
| nl_drop_optimal | Hagi/Theory/NegativeTransfer.lean:481 | C606 |
| hierBlockLen | Hagi/Theory/CoverageReading.lean:268 | C611 |
| hierStarts | Hagi/Theory/CoverageReading.lean:273 | C611 |
| hier_covers_any_n | Hagi/Theory/CoverageReading.lean:282 | C611 |
| hier_peak_window_budget | Hagi/Theory/CoverageReading.lean:314 | C611 |
| ce_adaptive_code_drop | Hagi/Theory/AdaptiveMajorizer.lean:1473 | C638 |
| ce_range_code_drop | Hagi/Theory/AdaptiveMajorizer.lean:1497 | C638 |
| adaptive_claim_scaled_bounds | Hagi/Theory/AdaptiveMajorizer.lean:1525 | C638 |
| mgda_eq_of_stationary | Hagi/Model/BatchCEDescentMgdaCode.lean:126 | C639 |
| batchGradientMinimizer_eq_mgdaCodeDirection_of_stationary | Hagi/Model/BatchCEDescentMgdaCode.lean:146 | C639 |
| grow_block_bench_sound | Hagi/Theory/GrowTrunkBlock.lean:123 | C640 |
| function_preserving_growth | Hagi/Theory/FunctionPreservingGrowth.lean:200 | C640 |
| warmup_safe | Hagi/Theory/FunctionPreservingGrowth.lean:303 | C642 |
| post_warmup_growth_safe | Hagi/Theory/FunctionPreservingGrowth.lean:352 | C642 |
| backtrack_accept_drop | Hagi/Theory/RollbackGate.lean:261 | C643 |
| warmup_h1_of_certified_steps | Hagi/Theory/FunctionPreservingGrowth.lean:410 | C644 |
| batch_drop_not_global | Hagi/Theory/FunctionPreservingGrowth.lean:464 | C644 |
| certified_step_block_of_range | Hagi/Theory/FunctionPreservingGrowth.lean:491 | C646 |
| batch_drop_generalizes | Hagi/Contracts/BatchGlobalTelescope.lean:122 | C647 |
| certified_batch_drop_global | Hagi/Contracts/BatchGlobalTelescope.lean:178 | C647 |
| rounds_union | Hagi/Contracts/BatchGlobalTelescope.lean:300 | C648 |
| certified_rounds_union | Hagi/Contracts/BatchGlobalTelescope.lean:367 | C648 |

| RepairRun | Hagi/Theory/RepairForgetting.lean:61 | C651 |
| acceptedCount | Hagi/Theory/RepairForgetting.lean:69 | C651 |
| repair_drop_bound | Hagi/Theory/RepairForgetting.lean:78 | C651 |
| accepted_le_budget | Hagi/Theory/RepairForgetting.lean:93 | C651 |
| repair_sound | Hagi/Theory/RepairForgetting.lean:105 | C651 |
| slot | Hagi/Theory/CoverageReading.lean:707 | C651 |
| slotRev | Hagi/Theory/CoverageReading.lean:712 | C651 |
| slot_last | Hagi/Theory/CoverageReading.lean:720 | C651 |
| slotRev_first | Hagi/Theory/CoverageReading.lean:732 | C651 |
| slot_mono | Hagi/Theory/CoverageReading.lean:716 | C651 |
| slotRev_last | Hagi/Theory/CoverageReading.lean:726 | C651 |
| codelength_ge_entropy_of_kraft | Hagi/Theory/ArchiverCodeLength.lean:55 | C653 |
| codelength_ge_entropy_of_uniquelyDecodable | Hagi/Theory/ArchiverCodeLength.lean:106 | C653 |
| idealLen_kraft | Hagi/Theory/ArchiverCodeLength.lean:150 | C653 |
| idealLen_ge_entropy | Hagi/Theory/ArchiverCodeLength.lean:157 | C653 |
| idealLen_le_ce_add_one | Hagi/Theory/ArchiverCodeLength.lean:164 | C653 |
| ceBits_eq_entBits_add_kl | Hagi/Theory/ArchiverCodeLength.lean:194 | C653 |
| idealLen_self_bounds | Hagi/Theory/ArchiverCodeLength.lean:208 | C653 |
| ema_one_unbiased | Hagi/Step/AdamDirection.lean:67 | C655 |
| adam_first_step_dot_nonneg | Hagi/Step/AdamDirection.lean:74 | C655 |
| adam_first_step_dot_pos | Hagi/Step/AdamDirection.lean:85 | C655 |
| adam_coord_sign_flip_neg | Hagi/Step/AdamDirection.lean:106 | C655 |
| adam_step_not_always_descent | Hagi/Step/AdamDirection.lean:116 | C655 |
| ema_sign_flip_negative | Hagi/Step/AdamDirection.lean:125 | C655 |
| linDrop | Hagi/Theory/FunctionPreservingGrowth.lean:579 | C657 |
| useful_first_step | Hagi/Theory/FunctionPreservingGrowth.lean:584 | C657 |
| useful_first_step_pos | Hagi/Theory/FunctionPreservingGrowth.lean:590 | C657 |
| useful_eta_le | Hagi/Theory/FunctionPreservingGrowth.lean:597 | C657 |
| exists_useful_eta | Hagi/Theory/FunctionPreservingGrowth.lean:620 | C657 |
| no_signal_no_drop | Hagi/Theory/FunctionPreservingGrowth.lean:629 | C657 |
| first_step_useful_certified | Hagi/Theory/FunctionPreservingGrowth.lean:641 | C657 |
| first_step_strict_improves | Hagi/Theory/FunctionPreservingGrowth.lean:676 | C657 |
| identityBlock | Hagi/Theory/FunctionPreservingGrowth.lean:137 | C640 |
| trunk_function_preserving | Hagi/Theory/FunctionPreservingGrowth.lean:166 | C640 |
| lmLogits_grow_identity | Hagi/Theory/FunctionPreservingGrowth.lean:176 | C640 |
| warmup_telescope | Hagi/Theory/FunctionPreservingGrowth.lean:288 | C642 |
| warmup_strict | Hagi/Theory/FunctionPreservingGrowth.lean:318 | C642 |
| uncertified_step_can_worsen | Hagi/Theory/FunctionPreservingGrowth.lean:335 | C642 |
| CertifiedFiniteStep | Hagi/Theory/FunctionPreservingGrowth.lean:402 | C644 |
| block_step_certified_of_range_bound | Hagi/Theory/FunctionPreservingGrowth.lean:507 | C646 |
| block_step_commit_of_range_bound | Hagi/Theory/FunctionPreservingGrowth.lean:521 | C646 |
| block_range_bound_violated_not_certified | Hagi/Theory/FunctionPreservingGrowth.lean:536 | C646 |
| growthGate | Hagi/Theory/NegativeTransfer.lean:570 | C640 |
| neg_transfer_char | Hagi/Theory/NegativeTransfer.lean:117 | C572 |
| hagi_master_v33 | Hagi/Theory/MasterTheoremV3.lean:252 | C622 |
| hagi_master_v34 | Hagi/Theory/MasterTheoremV3.lean:323 | C662 |
| holdout_gate_two_way | Hagi/Theory/HoldoutGateTwoWay.lean:52 | C660 |
| holdout_gate_two_way_delta | Hagi/Theory/HoldoutGateTwoWay.lean:109 | C660 |
| chain_linear | Hagi/Theory/FunctionPreservingGrowth.lean:721 | C663 |
| useful_of_adam_first | Hagi/Theory/FunctionPreservingGrowth.lean:746 | C663 |
| padSlot | Hagi/Theory/CoverageReading.lean:741 | C664 |
| padSlot_tail | Hagi/Theory/CoverageReading.lean:746 | C664 |
| padSlot_last | Hagi/Theory/CoverageReading.lean:754 | C664 |
| padSlot_full | Hagi/Theory/CoverageReading.lean:763 | C664 |
| mgda_norm_sq_le_of_stationary | Hagi/Model/BatchCEDescentMgdaCode.lean:102 | C639 |

<!-- Appendix A: every row re-verified by .tmp/C659/audit.py on HEAD 4e4ef126
     (freeze 9043 at e160b7ec): the declaration must start at the cited line. History:
     rows to C614 at 7ea1ee87 (+W2), C638–C648 at 551c8025, C651 at 8fb0f1fa.
     v1.0: FunctionPreservingGrowth.lean rows moved +12 lines (C657 section
     inserted at :40/:65/:79 before them); self_compress_loop_sound :708 ->
     :726 (§3.15, stale since v0.8); rows C653/C655/C657 added. IterState :117
     re-verified (structure on a `-/ structure` line).
     v1.1 (C664): rows of FunctionPreservingGrowth.lean moved +11 lines
     (C663), MasterTheoremV3.lean +11 (C662) — repinned by
     .tmp/C664/repin.py against 85c7c670; rows C660/C662/C663/C664 added.
     v1.1a (C667): FunctionPreservingGrowth.lean rows +22 (C665) at e160b7ec.
     v1.1b (C668): FunctionPreservingGrowth.lean rows +5 (docstring C668);
     row C668 (FirstLayerGrad.lean) added. -->