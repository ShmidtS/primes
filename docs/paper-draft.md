# Certify-Then-Commit: A Formally Verified Self-Improving Learning System

Draft v0.5 (C559). Все утверждения — либо Lean-якорь (FQN, файл,
строка на HEAD e40aa426), либо измеренный результат прогона с
указанием витка (Cn), либо явный PIN в §Limitations. Никаких
недоказанных клеймов.

## Abstract

We present **certify-then-commit (CTC)**, a discipline in which a
learning system takes a step only after a machine-checked
certificate: the loop **PROPOSE → CERTIFY → ADMIT →
COMMIT/HOLD/ROLLBACK → LOG**. Every accepted step is backed by a
Lean 4 theorem proved against Mathlib; the corpus currently
counts **543 modules / 12 875 theorems / 0 `sorry`** (generated
theorem index at HEAD e40aa426, regen C558). The cycle-level soundness theorem
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
restoring the full pre-step state (C530). Since v0.2 the loop has
been extended along two further axes: certified LoRA-style
adapter growth with snap-folding reaches trunk depth 10 at 64
parameters with 13-digit denominators (C532–C536, incl. an exact
rank-2 merge to 16 parameters, −75%, at certified bound 6.6e-8);
and five external HAGI_v2 observations were absorbed as theorems
(C537–C545), including the exact weight-decay leak factor (1−ηλ)
and an Empirical-Bernstein sample saving of 27.49×. The era
closes with a full self-improving loop in a single trace (C547):
26 certified steps, 10 adapter
parameters, zero-forgetting exact, and exact-bypass coverage
99.1%. Since v0.3 the loop has become iterative and universal:
repeated certified self-improvement grows coverage monotonically
over a space built from its own accepted primitives (7
iterations, 54.9% → 93.8%, compositional necessity proven by
in-run negatives), and the same loop on the full live corpus
(113 domains, real targets) reaches 93.8% coverage by constant
clusters with per-domain zero forgetting (bit-exact, 113/113) —
while honestly measuring that no linear law exists on live
data and that synthetic-layered laws do not transfer (0/113).
We state honest pins
(`BandDescribes`), measured ε-compromises, hybrid degeneration,
corpus drift, and mini-scale. Since v0.4 the adapter era has
been UNIFIED into one machine: a self-compressing loop keeps
parameters bounded at 2·k·d = 32 across unlimited certified
growth (measured drop monotone 0.158→0.364, residual CE −84%),
and constant clusters distill losslessly into rank-1 adapters
(CE = 0 bit-exact, exact-gate branches 113→0, honest contrast:
48 adapter parameters vs 6 symbolic values). The unification
era closes with mini-HAGI v3 — a full certified assembly of
the self-improving machine in ONE live trace (108/115 covered:
bypass → distill → 7 certified fd-steps on the residual, CE
3.80→0.51→0.0733, params ≤ 32, forget = 0; C558) — and with
the first EXTERNAL consumer: the wave205 bridge synchronization
between the HAGI_v2 runtime and this theory (C557).

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

<!-- source: .tmp/C506/receipt.md; .omc/analysis/period-c506-508-analysis.md §(а); файл удалён в c442e69, история: git show c442e69^:.omc/analysis/period-c506-508-analysis.md -->

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

<!-- source: .tmp/C508/receipt.md; .tmp/C510/receipt.md; decision table: .omc/analysis/period-c506-508-analysis.md §(б); файл удалён в c442e69, история: git show c442e69^:.omc/analysis/period-c506-508-analysis.md -->

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

### 3.5 Rank-truncation escape

In the mini-HAGI gpm2 phase, full-GPM honestly HOLDs (4 HOLD
rounds, first delta exactly zero on the 1/10000 grid — exact
replica of the C494 phenomenon), and the relaxed rank-truncated
projection escapes: minimal k with max sigmaTail² ≤ eps², eps =
1/10 (PIN, §5), gives 4 committed steps with per-step forgetting
≤ ‖delta‖·sigmaTail (assert-checked). Measured run: C500.

### 3.10 Adapter era: four certified growth mechanisms (C532–C536)

<!-- source: .tmp/C532/receipt.md; .tmp/C533/receipt.md; .tmp/C535/receipt.md; .tmp/C536/receipt.md -->

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
`adapter_neutral_B` (:84) — B = 0 makes the side-branch EXACTLY
neutral for arbitrary A; `adapter_step_certified` (:173) —
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
`adapter_snap_cycle_sound` (:264).

**Rank-adaptive selector (C535).** At each level the selector
PROBEs r=1 and r=2 on a copy (exact C530 rollback — the live
state never moves) and selects by measured score =
probe_drop/params (ties → r=1). `rankSelect` is a deterministic
function of the measured state (`rank_select_deterministic`);
`rank_select_sound` (:309) keeps the full guarantee of whichever
branch is chosen. Measured: score(r=2) ≤ score(r=1) at all 8
levels, so the selector honestly picks r=1 every time (adaptive
≡ fix-r1 bit-for-bit, 64 params, drop/param 0.035310, 17 steps);
the r=2 arm reaches the same drop at ×2 parameters (128, 10
steps) and is correctly rejected — no degradation.

**SVD-Matryoshka merge (C536).** After the 8-level stack, an
exact rational Gauss-Jordan rank/ factorization merges the
stack into a single adapter on the original trunk features:
`adapter_stack_rank_bound` (:397, rank(Π(I+Eᵢ) − 1) ≤ Σ rank Eᵢ),
`adapter_merge_error_bound` (:438, σ_tail + ℓ¹-Lipschitz),
`adapter_merge_params` (:424). Measured (exact rank of Δ = 2):

| model | params | matvec | obj change | certified bound |
|---|---|---|---|---|
| stack 8×r=1 | 64 | 8 | final 1.02460e-2 | cycle bound holds |
| merged k=ρ=2 | 16 (−75%) | 1 | −6.7e-11 (improvement) | 6.60e-8 |
| merged k=1 | 8 (−87.5%) | 1 | ~0.51 degradation | holds, usable=False |

Honest: k=1 (σ_tail ≈ 0.998) is correctly reported unusable;
the data gave rank 2 < min(d,L) = 4, so the bound is not vacuum.
17 certified steps, ~3.6 s, bit-identical repeat.

### 3.11 External absorption: five HAGI_v2 observations as theorems (C537–C545)

<!-- source: .tmp/C538..C541,C544,C545 receipts; plan: .omc/analysis/external-plan-c537-mapping.md (файл удалён в c442e69, история: git show c442e69^:.omc/analysis/external-plan-c537-mapping.md); delivery: docs/PROPOSAL-external-plan.md (C543) -->

A mapping audit (C537) inverted the bridge: instead of porting
HAGI_v2 code, its top observed defects were formalized as
theorems (C538–C541, C545) and delivered back with exact
code-fix mappings (docs/PROPOSAL-external-plan.md, C543).

**(1) Weight-decay leak (C538, P4).** `wd_proj_preserves`:
projected decay W′ = W − ηλ·(W − W·P) keeps W·P EXACTLY (the
measured projected leak 5.68e-15 is a machine zero = exact
zero); naive decay (1−ηλ)·W has the EXACT leak factor (1−ηλ) on
the protected component (`naive_decay_parallel`,
`naive_decay_norm`), leaks strictly (`naive_decay_leak`, :128;
measured naive leak 1.945); `wd_gpm_step_sound` (:159) composes
a black-box complement step with projected decay.

**(2) Empirical-Bernstein radius (C539, P1).**
`empirical_bernstein_bound` / `_mean_bound` (+
`freedman_tail_two_sided`, `eb_radius_algebra`): with measured
σ̂² and range b, |μ̂| < √(2σ̂²L/n) + 2bL/n at ≥ 1−α. Witness
contrast (ΔCE=0.04, R=11.09, α=0.01): n_Hoeffding = 176 995 vs
n_EB(MP form) = 6439 — a **27.49×** sample saving (our form:
4267, 41.5×). Honest: σ̂ is a runtime premise (no MP λ-trick).

**(3) Observational-equivalence search completeness (C540, P6).**
`oe_search_complete` (:82): OE-dedup search never loses a
solution that matches the target on the probes — completeness
is RELATIVE TO THE PROBES, no semantic equivalence claimed.
Witness: toy space 343 → 4 visits (~86×); the HAGI_v2 analogue
compressed 6478 → 896 candidates (7.2×).

**(4) Exact bypass, zero cross-entropy (C541, P8).** On a
PROVEN_EXACT coverage, CE contribution is EXACTLY zero:
`ce_pointwise_of_prob_one`, `ce_total_eq_residual` (:92) —
total = residual, bit-for-bit (witness 4.264244 == 4.264244);
`exact_gate_sound` (:99) and the negative `exact_gate_rejects_zero`
(p = 0 ⇒ rejected, junk log never used).

**(5) Polar-Express interval certificate (C545, P3).** A
scalar, SVD-free interval certificate for the minimax
Newton–Schulz iteration: three rationalized p(x) = ax+bx³+cx⁵
polynomials map the spectral box by EXACT rational bounds:
[1/1000, 1] → [1/256, 1313/1024] → [5/512, 601/512] → final
[9/512, 1049/1024] ≈ [0.0176, 1.0244] (`polar_express_step3_bound`,
Hagi/Optimization/PolarExpressCert.lean:373). Honest correction:
the upper end is 1.0244, i.e. within 2.5% of 1 — no spectral
explosion, but the iteration does not pin the top of the
spectrum to exactly 1.

**Adapter continual isolation (C544).** Composing adapters with
the continual line: per-task adapters give zero forgetting
STRUCTURALLY — `adapter_isolation_zero_forgetting` (:548) and
`adapter_per_task_sound` (:563) need no projections or budgets.
Measured head-to-head (conflict-pinned task B, same
trunk/data/eta/grid): ISO forgetA = 0 EXACT (bit-exact assert)
vs SHARED +0.2331 vs naive-trunk +5.5757 (the scenario of
`trunk_update_needs_projection`, :599, composed with C538).
PIN: on a same-distribution B the measured forgetting was
negative (SHARED −0.304 / TRUNK −0.753) — forgetting is a
conflict phenomenon; the conflict pin is documented in code.

### 3.12 The full self-improving loop in one trace (C547)

<!-- source: .tmp/C547/receipt.md -->

The era closes with all certified components composed into ONE
live run (`--mode mini-hagi-loop`, real unified_ledger, 113
points): a single trace, a single JSON, one theorem.

> **Theorem (full_loop_sound).**
> `Hagi/Theory/MiniHagiLoop.lean:64` (C547).
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

### 3.13 Iterative self-improvement (C549)

<!-- source: .tmp/C549/receipt.md -->

The full loop of §3.12 becomes ITERATIVE: one run executes 7
iterations in a single trace (one run / telemetry / JSON /
witness; budget MAX_ITER = 8 never exhausted — the stop is the
EB gate). Each iteration: OE-search in a space GROWN from the
accepted primitives → EXACT coverage extension (monotonicity
asserted bit-exact) → adapter retraining on the shrinking
residual (certified snap-GD, 10 steps/iteration, drop > 0 /
HOLD) → EB telemetry (n_EB < n_Hoeffding at every iteration).

> **Theorem (iterative_loop_sound).**
> `Hagi/Theory/MiniHagiLoop.lean:154` (C549). Induction over
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

### 3.14 Universal loop on the full live corpus (C551) — an honest measurement

<!-- source: .tmp/C551/receipt.md -->

The C549 compromise "the laws live in the corpus" is lifted:
the loop runs on ALL 113 live points of ALL domain keys of the
live `unified_ledger` (domain = ledger key; 114 keys / 113
live; the task-statement "~185 points" was rejected by direct
file read, recorded in research). Targets are REAL
snap(ce_i, 1/16). OE-search is honest: constants from real t;
linear p + a·x_j on real features (grid 1/16..256). If a law is
not found, that IS the result.

> **Theorem (universal_loop_corpus_mono).**
> `Hagi/Theory/MiniHagiLoop.lean:190` (C551). Union-additivity
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

### 3.15 Unification: one adapter machine for the whole knowledge lifecycle (C554–C556)

<!-- source: .tmp/C555/receipt.md; .tmp/C556/receipt.md; .tmp/C557/receipt.md -->

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
> `Hagi/Theory/AdapterGrowth.lean:708` (C555). The loop
> telescopes the objective (delegate of grow_snap_cycle_sound,
> generalized to a merge cycle) AND keeps params ≤
> selfCompressParams k d = 2·k·d for ANY number of iterations
> (`self_compress_params_bounded`, :682; strict contrast
> `self_compress_params_contrast`, :692).

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
> `Hagi/Theory/AdapterGrowth.lean:769` / `:806` (C556). The
> distilled readout is exactly c (construction), so coverage
> and CE = 0 are PRESERVED — composition with exact_gate_sound
> (C541), not a duplicate.

**The honest parameter contrast** (a Lean fact, not a claim):
the distillate costs 6×2d = 48 parameters while symbolic
storage needs only the 6 VALUES — symbolic is strictly cheaper
(`symbolic_storage_cheaper`, :835: J < 2·J·d for d ≥ 2). The
value of distillation is UNIFICATION of paths (0 branches, one
matmul path, exact-bypass merged into the adapter residual),
not memory.

### 3.16 Mini-HAGI v3: the full certified assembly in one trace (C558) — the headline result

<!-- source: .tmp/C558/receipt.md -->

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
> `Hagi/Theory/AdapterGrowth.lean:871` (C558). The unified
> adapter machine is the CONJUNCTION of the distill branch
> (`distill_coverage_preserved` ⇒ CE = 0 on every cluster) and
> the self-compress branch (`self_compress_loop_sound` ⇒
> objective telescope + params ≤ 2·k·d) — composition with NO
> weakening of the components' hypotheses. No new deep facts:
> this is the reference theorem that the full self-improving
> machine assembles soundly.

Witness (.tmp/C558/trajV3.lean, rc = 0): #eval trajectory
checks on run numbers (P3 + P4-it1), params-bounded instance
32 ≤ 32, telescope instance on run numbers, count contrast
32 < 48, negatives (wrong-const 1/256 ≠ 0; head-only CE ≠ 0 on
clusters before distillation).

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

### 4.3 What self-improvement actually yields on live data

<!-- source: .tmp/C549/receipt.md; .tmp/C551/receipt.md -->

On the full live corpus (§3.14) the loop finds few laws — and
that outcome is itself the honest headline. What
self-improvement demonstrably yields even when "laws are
scarce" are three certified SYSTEM properties:

1. **Isolated memory.** forgetA = 0 structurally — per-task
   adapters need no projections or budgets (C544); measured as
   bit-exact parameter-snapshot asserts after every training
   phase of all 113 domains (C551), 113/113.
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

### 4.4 Impact note: the first external consumer (wave205, C557)

<!-- source: .tmp/C557/receipt.md -->

The theory also acquired its first EXTERNAL consumer. The
HAGI_v2 runtime recheck during the C557 phase analysis observed
waves 205–207c, and wave205 synchronized the runtime's theory
state with this repository at commit ab28579e (C555): the
bridge that exports the certified constants to the runtime
went from an unused artifact to a live dependency — the first
real use of this theory by an external system. This is an
existence proof of external synchronization, not yet an
evaluation of downstream benefit (pinned below, §5.17).

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

9. **EB contrast is data-dependent.** The live full-loop corpus
   shows an EB-vs-Hoeffding sample contrast of only 1.12×
   (n_EB 9649 ≤ n_Hoeffding 10851, C547) against the 27.49× of
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
   live only on weaker data (C549/C551, pin 14) — in the v3
   assembly it is budget-limited, honestly.
17. **External consumer is a synchronization event, not a
   result.** The wave205 consumer of §4.4 proves the bridge is
   used; it does not measure any downstream benefit to the
   HAGI_v2 runtime.

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

## Appendix A: anchor table (verified at HEAD 977c930b)

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
| adapter_neutral_B | Hagi/Theory/AdapterGrowth.lean:84 | C532 |
| adapter_step_certified | Hagi/Theory/AdapterGrowth.lean:173 | C532 |
| adapter_snap_cycle_sound | Hagi/Theory/AdapterGrowth.lean:264 | C533 |
| rank_select_sound | Hagi/Theory/AdapterGrowth.lean:309 | C535 |
| adapter_stack_rank_bound | Hagi/Theory/AdapterGrowth.lean:397 | C536 |
| adapter_merge_params | Hagi/Theory/AdapterGrowth.lean:424 | C536 |
| adapter_merge_error_bound | Hagi/Theory/AdapterGrowth.lean:438 | C536 |
| naive_decay_leak | Hagi/Theory/WeightDecayLeak.lean:128 | C538 |
| wd_gpm_step_sound | Hagi/Theory/WeightDecayLeak.lean:159 | C538 |
| empirical_bernstein_bound | Hagi/Probability/EmpiricalBernstein.lean:208 | C539 |
| empirical_bernstein_mean_bound | Hagi/Probability/EmpiricalBernstein.lean:286 | C539 |
| oe_search_complete | Hagi/Theory/OEComplete.lean:82 | C540 |
| ce_total_eq_residual | Hagi/Theory/ExactBypass.lean:92 | C541 |
| exact_gate_sound | Hagi/Theory/ExactBypass.lean:99 | C541 |
| adapter_isolation_zero_forgetting | Hagi/Theory/AdapterGrowth.lean:548 | C544 |
| adapter_per_task_sound | Hagi/Theory/AdapterGrowth.lean:563 | C544 |
| trunk_update_needs_projection | Hagi/Theory/AdapterGrowth.lean:599 | C544 |
| polar_express_step3_bound | Hagi/Optimization/PolarExpressCert.lean:373 | C545 |
| full_loop_sound | Hagi/Theory/MiniHagiLoop.lean:64 | C547 |
| IterState | Hagi/Theory/MiniHagiLoop.lean:117 | C549 |
| iterStep | Hagi/Theory/MiniHagiLoop.lean:122 | C549 |
| coversPrim | Hagi/Theory/MiniHagiLoop.lean:128 | C549 |
| coverage_append_monotone | Hagi/Theory/MiniHagiLoop.lean:134 | C549 |
| iterative_loop_sound | Hagi/Theory/MiniHagiLoop.lean:154 | C549 |
| universal_loop_corpus_mono | Hagi/Theory/MiniHagiLoop.lean:190 | C551 |
| selfCompressParams | Hagi/Theory/AdapterGrowth.lean:677 | C555 |
| self_compress_params_bounded | Hagi/Theory/AdapterGrowth.lean:682 | C555 |
| self_compress_params_contrast | Hagi/Theory/AdapterGrowth.lean:692 | C555 |
| self_compress_loop_sound | Hagi/Theory/AdapterGrowth.lean:708 | C555 |
| distillAdapter | Hagi/Theory/AdapterGrowth.lean:760 | C556 |
| constant_distill_exact | Hagi/Theory/AdapterGrowth.lean:769 | C556 |
| distill_prob_one | Hagi/Theory/AdapterGrowth.lean:790 | C556 |
| distill_coverage_preserved | Hagi/Theory/AdapterGrowth.lean:806 | C556 |
| distill_param_count | Hagi/Theory/AdapterGrowth.lean:819 | C556 |
| distill_params_total | Hagi/Theory/AdapterGrowth.lean:826 | C556 |
| symbolic_storage_cheaper | Hagi/Theory/AdapterGrowth.lean:835 | C556 |
| v3_assembly_sound | Hagi/Theory/AdapterGrowth.lean:871 | C558 |
| master_theorem_v3 | Hagi/Theory/MasterTheoremV3.lean:57 | C576 |
| auto_transfer_gate_sound | Hagi/Theory/AutoTransferGate.lean:139 | C577 |
| fact_append_preserves | Hagi/Theory/FactLedger.lean:59 | C579 |
| fact_lookup_monotone | Hagi/Theory/FactLedger.lean:67 | C579 |
| rangeWrap_inrange | Hagi/Theory/RangeWrap.lean:43 | C581 |
| rangeWrap_fixed_point | Hagi/Theory/RangeWrap.lean:53 | C581 |
| selectW_spec | Hagi/Theory/AdaptiveContext.lean:49 | C582 |
| selectW_occam_minimal | Hagi/Theory/AdaptiveContext.lean:71 | C582 |
| selectW_budget_bound | Hagi/Theory/AdaptiveContext.lean:99 | C582 |
| consolidate_prompt_empty | Hagi/Theory/KnowledgeConsolidation.lean:66 | C584 |
| remember_preserves_pages | Hagi/Theory/KnowledgeConsolidation.lean:72 | C584 |
| learn_from_dialog_archives | Hagi/Theory/KnowledgeConsolidation.lean:79 | C584 |

<!-- Appendix A rows up to C551 verified at HEAD 977c930b
     (C552); C555/C556/C558 rows verified at HEAD e40aa426
     (C559); anchor lines via rg on Hagi/**/*.lean -->
