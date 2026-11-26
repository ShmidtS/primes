# Certify-Then-Commit: A Formally Verified Self-Improving Learning System

Draft v1.4 (release). Every claim in this paper is one of three things: a
Lean anchor (declaration, file, line), a measured number of a run (with
what was measured), or an open premise listed in §5. A conditional
certificate is never stated as an unconditional claim.

## Abstract

**Certified HAGI** is a self-improving learning system in which no step is
taken before a machine-checked certificate exists:
PROPOSE → CERTIFY → ADMIT → COMMIT/HOLD/ROLLBACK → LOG, formalized in
Lean 4 against Mathlib (12 875 theorems in 543 modules, 0 `sorry`).

The cycle theorem `certify_then_commit_sound` gives, per T-round run,
objective telescoping, a 1 − δtotal bound on false commits, an ε-bound on
holdout-risk growth and exact budget balance. The consolidated statement
`hagi_master_v34` covers the machine in fourteen clauses; `hagi_master_v35`
(Hagi/Theory/MasterTheoremV3.lean:458) adds the optimizer block under one
premise contract `OptimizerPremises` — the contract (O7) and six clauses
(O1)–(O6).

Measured end to end: mini-HAGI v3 covers 108/115 targets in one live
trace (26 certified steps, forget = 0 bit-exact); the reading floor
⌈nB/w⌉ is attained and a 2-level hierarchy cuts the peak window budget
127 → 63 at n = 8128.

The formula hits of the paper are closed form and proved: the optimal
snap grid k* = ⌈log₂(L·d/ε)⌉ − 1, the useful first warm-up step
**η* = 4|a|/R² with drop_max = 2a²/R²**, and the codelength sandwich
**H(p) ≤ E[len] ≤ H(p) + KL(p‖p̂)/log 2 + 1** via Kraft–McMillan.

Optimizer side: for the first layer `W1` the consumer's Muon step
`W1 − η·ns₃(Ĝ)` is a proved strict descent step with first-order drop
≥ ‖G‖_F, and the three-iteration Newton–Schulz iterate keeps ≥ 39/40 of
the optimum on the spectrum σ ≥ ½‖G‖_F. The rectangular iteration is the
same proved step on `m×n`: it keeps the singular bases, the optimum over
row isometries `ΔΔᵀ = I` is `Σ σ i`, the wide SVD it needs is a theorem,
and for a `G ≠ 0` of any shape `⟨G, wide_iter k Ĝ⟩ ≥ ‖G‖_F` with no
structural hypothesis; for the code-shaped layer `W1` of ANY shape the
Muon update is a proved strict descent of the CE outside the kink.

The release also contains 19 PALOMAR cards (docs/PALOMAR-CARDS.md) and a
§2.2 map of code bridges in which the consumer's own code (HAGI_v2,
python `file:line@sha`) is checked against the canon and labelled exact,
conditional or honest-gap. The open hypotheses are stated in §5.

## 1. Problem

A growing language model is changed by many mechanisms at once: new
blocks are added, old knowledge must not be forgotten, knowledge is
compressed and distilled, and the optimizer takes the steps. In a plain
training loop each of these decisions is a heuristic: a growth gate
compares measured losses, an optimizer step is trusted, a rollback is
best-effort. None of them carries a guarantee that relates what the code
does to what the theory proves.

The problem of this paper: make every step of such a loop conditional on
a certificate, prove the resulting cycle sound end to end, and say
exactly where the consumer's code satisfies the theorem's hypotheses and
where it does not. Three questions organize the paper.

- What is proved without any code hypothesis (the cycle theorem and its
  consolidation, §4.1)?
- Which formulas are closed form (§4.2–§4.4)?
- What does the code inherit, and what stays a hypothesis (§2.2, §5)?

## 2. Model and architecture

### 2.1 The machine

The model is a causal language model over a ternary target alphabet. Its
parts, as they appear in the theorems:

- **Trunk.** A stack of blocks; the first layer of a block is the matrix
  `W1 : ι → δ → ℝ` (code shape `dim × hidden`), followed by a relu and a
  readout `wo`. The logits feed a softmax and the cross-entropy `Hagi.ceOneHot`.
- **Growth.** A new block starts as an identity (objective invariant
  exactly), then is trained by certified steps while the old blocks stay
  frozen. A low-rank adapter (down `A : r×d`, up `B : d×r`) is the cheap
  alternative; `B = 0` makes it exactly neutral.
- **Continual learning.** Per-task adapters, GPM projections, a
  rank-truncated projection and A-GEM, selected per step.
- **Compression.** Weights and features are snapped to the grid q/2^k;
  a stack of adapters is merged exactly; constant clusters are distilled
  into rank-1 adapters; an archiver codes with a model-derived CDF.
- **Reading.** The input is read through windows of width w, step s,
  grouped in blocks of length B; the machine chooses w, s and B by formula.
- **Optimizer.** Adam for warm-up, Muon (Newton–Schulz-orthogonalized
  momentum) for the layer update.

### 2.2 Code bridges: machine layer ↔ theorem ↔ code

The table maps each layer to its canon (Lean `file:line`), to the
consumer's code (HAGI_v2 python `file:line@sha`, or the primes bench
twin) and to a status: **exact** (the code's statement at the cited lines
is an instance of the theorem), **conditional** (holds under a model
hypothesis the code does not check), **honest gap** (the code does
something the theorem does not cover).

| Layer | Canon (Lean file:line) | Code anchor | Status |
|---|---|---|---|
| growth | `grow_block_bench_sound` (Hagi/Theory/GrowTrunkBlock.lean:123); `function_preserving_growth` (Hagi/Theory/FunctionPreservingGrowth.lean:199) | `_block_add`/`grow`, hagi/lm.py:581-601 @ca52eb4 | exact |
| growth | `grow_blocks_repeat_sound` (Hagi/Theory/GrowTrunkBlock.lean:148) | `MAX_BLOCKS = 2`, hagi/unified.py:381 @ca52eb4 | exact (2 blocks) |
| growth | `growthGate` (Hagi/Theory/NegativeTransfer.lean:570) | `_maybe_grow`, hagi/unified.py:383-440 @ca52eb4 | honest gap: heuristic signal, not the canonical gate |
| growth | `snap_k_eq_ceil` (Hagi/Theory/GrowSnap.lean:342); `grow_snap_cycle_sound` (:145) | no snap grid in HAGI_v2; bench twin `--mode grow-snap` | honest gap: no consumer code |
| growth | `adapter_step_certified` (Hagi/Theory/AdapterGrowth.lean:190) | bench twin `--mode adapter-grow` | conditional (bench carrier) |
| step | `ce_range_code_drop` (Hagi/Theory/AdaptiveMajorizer.lean:1409) | range branch, hagi/lm.py:1313-1324 @1ae924e | exact |
| step | `ce_adaptive_code_drop` (Hagi/Theory/AdaptiveMajorizer.lean:1429) | `_adaptive_step`, hagi/lm.py:1261 @1ae924e | conditional (window (1e-5, 50]) |
| step | `CertifiedFiniteStep` (Hagi/Theory/FunctionPreservingGrowth.lean:401); `warmup_h1_of_certified_steps` (:410) | `_certified_finite_step`, hagi/lm.py:826-879 @ca52eb4 | conditional (one objective) |
| step | `useful_first_step` (Hagi/Theory/FunctionPreservingGrowth.lean:583); `first_step_useful_certified` (:637) | block `grow()`, hagi/lm.py:589-601 @ca52eb4 | conditional (a < 0, hlin) |
| step | `adam_first_step_dot_pos` (Hagi/Step/AdamDirection.lean:85); `ema_sign_flip_negative` (:125) | `torch.optim.Adam`, hagi/lm.py:349 @b3740e0 | exact as a verdict: descent only at t = 1 |
| step | `mgda_eq_of_stationary` (Hagi/Model/BatchCEDescentMgdaCode.lean:126) | `mgda_weights`, hagi/selfmodel.py:35-60 @ca52eb4 | exact at ε = 0, equal ‖g‖ |
| reading | `covStartsStep_covers` (Hagi/Theory/CoverageReading.lean:184); `hier_covers_any_n` (:283) | bench twin `--mode adaptive-span`, `generate-hier` | honest gap: no consumer code |
| reading | `slot_last` (Hagi/Theory/CoverageReading.lean:720); `slotRev_first` (:734) | `_windows`, hagi/unified.py:297-316 @b3740e0 | exact for order; honest gap: target adjacency |
| reading | `slot_last` (Hagi/Theory/CoverageReading.lean:720); `padSlot_tail` (:748); `padSlot_last` (:756); `padSlot_full` (:765) | train_guarded holdout, hagi/lm.py:905-907 @bab8aff; `_read_all_windows`, hagi/lm.py:1041-1054 @bab8aff; `generate`, hagi/lm.py:1126-1127 @bab8aff | exact for order; honest gap: `unified.py:1010` @bab8aff still reads `[::-1]` |
| step | `chain_linear` (Hagi/Theory/FunctionPreservingGrowth.lean:720); `useful_of_adam_first` (:741) | block `grow()`, hagi/lm.py:581/:594-596 @ca52eb4 | conditional (linear carrier; nonlinear: strict descent only) |
| probability | `holdout_gate_two_way` (Hagi/Theory/HoldoutGateTwoWay.lean:52); `holdout_gate_two_way_delta` (:109) | growth gate, hagi/unified.py:536-543/:563-567/:577 @b3740e0 | conditional (iid slice; k = 512 near-vacuous) |
| transfer | `neg_transfer_char` (Hagi/Theory/NegativeTransfer.lean:117); `nl_drop_optimal` (:481) | `_fit_domain_adapter`, hagi/unified.py:360/:367 @b3740e0 | conditional (quad model) |
| transfer | `auto_transfer_gate_sound` (Hagi/Theory/AutoTransferGate.lean:139) | bench twin `--mode transfer-gate-certified` | honest gap: no consumer code |
| compression | `constant_distill_exact` (Hagi/Theory/AdapterGrowth.lean:782); `distill_coverage_preserved` (:824) | bench twin `--mode distill` | honest gap: no consumer code |
| compression | `codelength_ge_entropy_of_kraft` (Hagi/Theory/ArchiverCodeLength.lean:55); `idealLen_le_ce_add_one` (:164) | `probs_to_cdf`/`encode_step`, hagi/archiver.py:33-70 @b3740e0 | conditional (ideal coder, not range coder) |
| compression | `trit_roundtrip` (Hagi/Theory/TritCodec.lean:117) | `decode_step`, hagi/archiver.py:96-118 @b3740e0 | honest gap: positional pack, not a range coder |
| probability | `empirical_bernstein_mean_bound` (Hagi/Probability/EmpiricalBernstein.lean:286); `batch_drop_generalizes` (Hagi/Contracts/BatchGlobalTelescope.lean:122) | refine loop, hagi/lm.py:978-1008 @ca52eb4 | conditional (iid batch) |
| probability | `certified_rounds_union` (Hagi/Contracts/BatchGlobalTelescope.lean:367) | 8-round loop, hagi/lm.py:978-1008 @ca52eb4 | conditional (independent rounds; WOR open) |
| rollback | `rollback_gate_sound` (Hagi/Theory/RollbackGate.lean:99); `backtrack_accept_drop` (:262) | `guarded_optimizer_step`, hagi/selfmodel.py:78-180 @ca52eb4 | exact as a predicate |
| rollback | `repair_sound` (Hagi/Theory/RepairForgetting.lean:105); `repair_drop_bound` (:78) | `_repair_forgetting`, hagi/unified.py:408-454 @e9a96fc | exact for control flow; linear bound only |
| compression | `trit5_roundtrip` (Hagi/Theory/NadyaOptimal.lean:79); `int4_roundtrip` (:98); `exists_best_mse_scale` (:126) | `trit5Pack`/`_pack_int4`/`_best_mse_ternary`, Надя.txt:390-440 (snapshot 2026-11-24) | exact for the pack; honest gap: list-level int4 padding, candidate list |
| step | `cosine_sched_bounds` (Hagi/Theory/NadyaOptimal.lean:143); `muon_step_norm_bound` (:201) | HybridMuon schedule, Надя.txt:120-152 | conditional (polar norm c is a hypothesis; momentum and weight decay outside) |
| probability | `paired_lcb_false_grow_bound` (Hagi/Theory/NadyaOptimal.lean:270) | LCB gate, Надя.txt:109-112/:884-890 | conditional (deterministic radius r; code uses z·σ̂/√n) |
| compression | `bypass_reaches_compression_limit` (Hagi/Theory/NadyaOptimal.lean:304); `ce_covered_zero` (Hagi/Theory/ExactBypass.lean:70) | EXACT_BYPASS, Надя.txt:695-750 | exact for the ideal coder (q = 1 on the support) |
| growth | `wlogits_width_preserved` (Hagi/Theory/WidthGrowth.lean:597); `attn_score_scale_preserved` (:329); `rotary_old_pairs_unchanged` (:266) | `grow_width`, Надя.txt (function name) | exact for nh = 1, even width; honest gap: nh > 1, odd width, clip are hypotheses `WGrowth` |
| step | `hagi_master_v35` (Hagi/Theory/MasterTheoremV3.lean:458); premise contract `OptimizerPremises` (Hagi/Theory/MasterTheoremV3.lean:428) | Muon layer update `W1 -= (cos_lr*0.7)*newton_schulz_orthogonalize(m1, iters=3)` (hagi/core.py:1755 @ca52eb4) | exact as a consolidation (§4.1); the optimizer bridges, row by row, are the table of §4.5 |
| rollback | `post_warmup_growth_safe` (Hagi/Theory/FunctionPreservingGrowth.lean:351) | keep-iff-holdout, hagi/unified.py:435-437 @ca52eb4 | conditional (h1) |
| step | `descentPath_apply_pos` (Hagi/Optimization/PercolationPath.lean:238); `exists_descentGraph_edge_of_useful_step` (Hagi/Optimization/PercolationPath.lean:230); `crosses_pos` (Hagi/Optimization/PercolationPath.lean:125) | no graph routing in HAGI_v2; HedgeRouter branches by loss weights, hagi/core.py:1809-1810 @ca52eb4 | honest gap: no consumer code |

**What is proved end to end.** Inside Lean, with no code hypothesis: the
cycle theorem (`certify_then_commit_sound`,
Hagi/Theory/CertifyThenCommit.lean:327) and its fourteen-clause
consolidation (`hagi_master_v34`, Hagi/Theory/MasterTheoremV3.lean:323;
v3.5 = these fourteen + the premise contract (O7) + the optimizer clauses
(O1)–(O6), `hagi_master_v35`, Hagi/Theory/MasterTheoremV3.lean:458) —
budget, zero-forgetting under a frozen task, objective telescoping,
coverage monotonicity, the exact transfer iff, the minimal snap grid, the
coverage floor and peak window budget. Against the consumer's code, the
exact bridges are the range branch of the certified step, identity growth
of the trunk, the MGDA direction at ε = 0, three control-flow predicates
(backtracking, repair — with a linear bound — and window order), the
verdicts "window fix leaves a k-byte gap" and "Adam descends only at
t = 1", and the Muon chain (§4.5), the one bridge that reaches the
consumer's optimizer.

**What remains a hypothesis or a model.** (1) h1 for the real warm-up:
the code warms the block with bare Adam and never calls the certified
step (pin 25). (2) Batch → global: iid sampling and independent rounds,
while the code samples without replacement and updates θ between rounds;
WOR conservativity is an unproved intuition (pins 28, 32). (3) The
descent signal a < 0 of the useful first step is a hypothesis; its
chain-rule link to `adam_first_step_dot_pos` is proved for a linear
carrier only (pins 30, 31). (4) Codelength bounds are for the ideal coder
⌈−log₂ p̂⌉₊; the range coder has no Lean model (pin 33). (5) Every
holdout gate compares measured values (pin 29). (6) No bridge at all for
the snap grid, adaptive-span and hierarchical reading, the auto transfer
gate, or constant distillation — bench twins only. (7) The Muon step
size merely exists; the code-side guards are proposed, not implemented
(docs/PROPOSAL-muon-guards.md).

### 2.3 Related work

- **Continual learning / GPM.** Gradient Projection Memory constrains
  updates to directions orthogonal to the old-task input span. The
  `Hagi/Step` GPM line formalizes zero-forgetting (`gpm_zero_forgetting`)
  and its rank-truncated relaxation (§4.2), including the
  machine-checked form of the all-HOLD phenomenon (`gpm_hold_when_covered`).
- **Anytime-valid inference.** Sequential tests with Ville-type master
  bounds; the discharge routes cite the stitched-Ville master
  `adaptive_anytime_valid` and the stop-mediated `false_stop_bound`.
- **Certified descent / majorizers.** Quadratic majorization with safe
  step sizes; the tight Bennett multiplier κ (§4.2) sharpens the classical
  e^R multiplier (measured e^R/κ(R): 2.77× / 3.79× / 6.73× at
  R = 0.5 / 1 / 2).
- **Verified ML.** This work contributes the cycle-level end-to-end
  theorem plus SVD infrastructure prepared for Mathlib upstream
  (docs/UPSTREAM-SVD.md).

The transfer line replaces heuristic warm-start gates by an exact
quadratic iff plus a smooth sufficient budget `n•nlBudget` (clauses 5+8),
fixed quantization grids by `k* = ⌈log₂(L·d/ε)⌉−1` (`snap_k_eq_ceil`), and
truncated windows by the coverage iff `s ≤ w` with adaptive step and
honest INFEASIBLE (`covStartsStep_covers`/`_adaptive_covers`).

## 3. Algorithm: the certified training loop

A T-round cycle over system states with per-round proposals,
certificates, admission gates, commit/hold/rollback decisions and a
budget ledger.

> **Theorem (certify_then_commit_sound).**
> `Hagi/Theory/CertifyThenCommit.lean:327`.
> For any T-round CTC cycle, under per-round false-commit measure
> premises (μ{falseCommit i} ≤ δ i) with Σδ i ≤ δtotal and per-round
> holdout allowances Σ e i ≤ ε:
>
> (b) objective telescopes: `obj (t T) ≤ obj (t 0) − Σ drops` over
> committed ledger entries;
> (c) with probability ≥ 1 − δtotal no commit is false (union bound
> over T false-commit events);
> (d) holdout risk grows by at most ε;
> (e) the budget ledger balances exactly
> (`budget (t T) + Σ spends = budget (t 0)`), stays nonnegative, and the
> floors are kept.

Discharge routes for the false-commit premises: `adaptive_anytime_valid`,
`false_stop_bound`.

The COMMIT/HOLD decision is closed under failure: HOLD restores the
EXACT pre-step state — parameters, optimizer state and RNG — and COMMIT
requires a measured weighted validation gain above the full error budget
(e_gen + e_quant + e_route + m_safety).

> **Theorem (rollback_gate_sound).** `Hagi/Theory/RollbackGate.lean:99`.
> gate = false ⟹ the guarded step equals the incoming state exactly
> (with per-component params/optimizer/RNG corollaries).

`rollback_obj_exact` (`:127`): any objective is unchanged by a rollback.
`commit_certified_gain` (`:177`): a commit implies wa < wb − errBound, so
the δ-budget is spent only on commits (`rollback_budget_unspent`).
`weak_gate_loses`: forcing a commit without the gate strictly worsens
the objective.

The loop as a whole: identity start (literal) → certified step on the
block ⇒ h1 ⇒ obj ≤ fOld under both gate verdicts → batch → global only
probabilistically. The weak link is not "the step is not certified" but
"the batch/round model is a hypothesis" (§5).

## 4. Main results

Each result: statement in words, hypotheses, Lean anchor, what it does
not claim. Axioms of every theorem: `propext`, `Classical.choice`,
`Quot.sound`.

### 4.1 The consolidated statement

One theorem covers the whole certified machine. Hypotheses: the machine
block of v3.1 verbatim, the transfer block (`L G hL`, smoothness +
G-bound), the hier block (`nB B w s'`, `0 < B`, `0 < s'`, `s' ≤ w`), plus
`hw : 0 < w` and `hdiv : w ∣ B`. Each clause is a delegate to an
already-proven theorem with hypotheses verbatim and no weakening.

| # | clause (Lean-verbatim) | delegate | carrier | since |
|---|---|---|---|---|
| (1) | `params bs.length ≤ 2 * k * dd` — parameter budget at any cycle length | `self_compress_loop_sound` | Hagi/Theory/AdapterGrowth.lean:722 | v3.1 |
| (2) | `perTaskVec (s τ) a = perTaskVec (s 0) a` — zero forgetting by per-task adapter isolation | `adapter_per_task_sound` | Hagi/Theory/AdapterGrowth.lean:579 | v3.1 |
| (3) | `step bs.length ≤ o0 + bs.sum` — the certified objective telescope | (machine obj bound) | Hagi/Theory/MasterTheoremV3.lean:83 | v3.1 |
| (4) | `coversPrim CovP (st n) i` — coverage is monotone along the append-only cycle | `iterative_loop_sound` | Hagi/Theory/MiniHagiLoop.lean:154 | v3.1 |
| (5) | `quadObj tB θ > quadObj tB 0 ↔ 2 * ⟪θ, tB⟫_ℝ < ‖θ‖^2` — transfer governed by an EXACT iff boundary | `neg_transfer_char` | Hagi/Theory/NegativeTransfer.lean:117 | v3.1 |
| (6) | `snapK Lq dq εq hεq hLd0 = ⌈log₂ (Lq * dq / εq)⌉ - 1` — the snap grid is MINIMAL for the ε-budget | `snap_k_eq_ceil` | Hagi/Theory/GrowSnap.lean:342 | v3.1 |
| (7) | `∀ ib < nc, ∃ sw ∈ covStarts nc kc, sw ≤ ib ∧ ib < sw + kc` — every byte of the input is covered by some lattice window | `covStarts_covers` | Hagi/Theory/CoverageReading.lean:54 | v3.1 |
| (8) | `f z - nE * nlBudget γ L G ≤ f (nlRun nE γ grad z) ∧ f (nlRun nE γ grad z) ≤ f z` — smooth sufficient-transfer bound at equal GD budget, `nlBudget γ L G = γ·G² + L·γ²·G²/2` | `smooth_obj_transfer_bound` | Hagi/Theory/NegativeTransfer.lean:386 | v3.1 |
| (9) | `nlDrop (1 / L) L G = G ^ 2 / (2 * L)` — the certified-optimal single-step drop γ* = 1/L | `nl_drop_optimal` | Hagi/Theory/NegativeTransfer.lean:481 | v3.2 |
| (10) | `∀ ib < nB, ∃ t ∈ hierStarts nB B w s', t ≤ ib ∧ ib < t + w` — coverage of `[0, nB)` at ANY nB, streaming peak ≤ m windows | `hier_covers_any_n` | Hagi/Theory/CoverageReading.lean:282 | v3.2 |
| (11) | `(hierStarts nB B w w).length = (nB + w - 1) / w ∧ ∀ Ll : List ℕ, (∀ ib < nB, ∃ t ∈ Ll, t ≤ ib ∧ ib < t + w) → (nB + w - 1) / w ≤ Ll.length` — the machine's total at s = w EQUALS ⌈n/w⌉, and no covering list of width-w windows is shorter | `hier_optimal` | Hagi/Theory/CoverageReading.lean:531 | v3.3 |
| (12) | the useful first growth step | `first_step_strict_improves` | Hagi/Theory/FunctionPreservingGrowth.lean:675 | v3.4 |
| (13) | the Adam first step | `adam_first_step_dot_pos` | Hagi/Step/AdamDirection.lean:85 | v3.4 |
| (14) | the two-way holdout gate | `holdout_gate_two_way_delta` | Hagi/Theory/HoldoutGateTwoWay.lean:109 | v3.4 |

Versions: `hagi_master_v31` (`Hagi/Theory/MasterTheoremV3.lean:128`) = (1)–(8);
`hagi_master_v32` (`:187`) = v3.1 + (9)(10); `hagi_master_v33` (`:252`)
= v3.2 + (11); `hagi_master_v34` (`:323`) = v3.3 + (12)(13)(14), all
three with their hypotheses verbatim. Each version carries the previous
statement unfolded verbatim and discharges it through ONE delegate
(`hV31` / `hV32` + projections); the `master_theorem_v3` pattern is
`Hagi/Theory/MasterTheoremV3.lean:83`. Clauses (5)+(8) form the two-level
transfer-certified circuit: an exact quadratic iff plus a conservative
smooth sufficient level.

Witnesses: clause (9) applied to L=2, G=1 gives drop = 1/4; clause (10)
to n=8128, B=4032, w=s'=64; clause (11) at n=8128, B=4032, w=64 — total
127 = ⌈8128/64⌉, floor against an arbitrary covering list.

**v3.5 — optimizer clauses.** `hagi_master_v35`
(Hagi/Theory/MasterTheoremV3.lean:458) = v3.4 + the optimizer block as
trailing clauses: (O7) = the premise contract `OptimizerPremises` itself,
then six clauses (O1)–(O6), discharged through ONE delegate (`hV34`) plus
one proved theorem per clause.

| Clause | Statement | Delegate |
|---|---|---|
| (O7) | the single premise contract `OptimizerPremises` (kink-free, `G ≠ 0`, equal masks, `S_batch > 0`) holds — first conjunct of the block | the structure itself |
| (O1) | grad structure: `∇_{W1} CE` of one input is rank one (`g ⊗ x`); over a batch `D CE[Δ] = −⟨Σ_t g_t ⊗ x_t, Δ⟩` | `w1_grad_rank_one` (Hagi/Theory/FirstLayerGrad.lean:123); `batch_directional_derivative` (Hagi/Theory/BatchRankOne.lean:65) |
| (O2) | smooth step: at `γ* = 1/S_batch` the batch CE sum drops by `‖D‖²/(2·S_batch)`; along any `d ≠ 0`: `γ* = a/(L‖d‖²)`, drop `a²/(2L‖d‖²)` | `w1BatchCE_optimal_step_drop` (Hagi/Theory/FirstLayerLipBatch.lean:218); `dir_drop_optimal` (Hagi/Theory/MomentumAlign.lean:112) |
| (O3) | Muon optimality: `⟨G, Δ⟩ ≤ Σσ` over the isometries (`ΔᵀΔ = 1`; wide: `ΔΔᵀ = 1`), the maximum attained | `muon_step_optimal_in_isometry_group` (Hagi/Theory/MuonIsometry.lean:175); `wide_step_optimal'` (Hagi/Theory/WideSVD.lean:317) |
| (O4) | NS approximation: `σ₀ ∈ [1/2, 1] ⇒ σ₃ ≥ 39/40`; `⟨G, ns_k G⟩ = Σ σ i·ns_seq k (σ i)` | `ns_sigma_min_three` (Hagi/Theory/NewtonSchulzSigma.lean:126); `muon_alignment_exact` (Hagi/Theory/MuonAlignment.lean:104); `wide_alignment_exact'` (Hagi/Theory/WideSVD.lean:306) |
| (O5) | descent certificate: `∃ η > 0` with strict CE decrease after `W1 − η·ns_k(Ĝ)`, layer of ANY shape, one input and batch | `muon_step_useful_w1_rect'` (Hagi/Theory/MuonDescentW1Rect.lean:348); `muon_step_useful_w1_rect_batch'` (:369) |
| (O6) | momentum: `⟨G,m⟩ ≥ (1−μ)‖G‖² − μ‖G‖‖m_prev‖` always, `≥ ‖G‖²` if `⟨G,m_prev⟩ ≥ ‖G‖²`; Muon with momentum: `⟨G,Xₖ⟩ ≥ ‖m‖_F − ‖G−m‖_F‖Xₖ‖_F` | `momentum_align_cs` (Hagi/Theory/MomentumAlign.lean:149); `momentum_align_ge_grad` (:179); `muon_momentum_bound` (:419) |

(O1)–(O6) are conditioned on (O7). The layer premises live in ONE
contract, the structure `OptimizerPremises`
(Hagi/Theory/MasterTheoremV3.lean:428: `S_batch > 0`, equal relu masks
before/after the `1/S_batch` step, outside the kink, batch gradient
`≠ 0`, and for the single input `g ≠ 0`, `x ≠ 0`); the remaining
hypotheses (`d ≠ 0`, `0 ≤ μ`, `⟪grad z, m_prev⟫ ≥ ‖grad z‖²`,
`card m ≤ card n`, `σ ∈ [1/2, 1]`, `m ≠ 0`) are the delegates' premises
verbatim. The batch mean form of the code is proved separately
(`w1MeanCE_optimal_step_drop`, Hagi/Theory/FirstLayerLipBatch.lean:247)
and is not a clause of v3.5. Witness: ι = Fin 3, δ = Fin 2,
`S_batch = 49`, outside the kink; `σ = 1/2 ⇒ σ₃ ≥ 39/40`.

Does not claim: no new proof in any version; each clause holds only
under its own hypotheses; the code's step size and momentum value are not
related to the clauses.

### 4.2 Certified step, continual learning, prediction

**Adaptive majorizer with tight κ.**

> **Theorem (adaptive_descent).** `Hagi/Theory/AdaptiveMajorizer.lean:669`.
> If `next η ≤ L − η·A + η²·C` for all η ∈ [0,1] with A ≥ 0, C > 0, and
> η* = A/(2C) ≤ 1, then `next η* ≤ L − A²/(4C)`.

The tight Bennett multiplier κ(R) = (e^R − 1 − R)/R² satisfies
1/2 ≤ κ(R) ≤ e^R for R > 0 (`kappa_ge_half`, :294; `kappa_le_expR`,
:310; monotone `kappa_mono`, :267). Does not claim: that the consumer's
adaptive branch is taken on any given config (pin 23).

**Fisher-quantized updates.**

> **Theorem (fisher_quant_loss_bound).** `Hagi/Theory/MergeQuant.lean:204`.
> If the loss has coordinatewise-bounded second-order curvature
> (premise `hcurv`) and per-coordinate quantization |δ_j| ≤ ε_j, then
> `L(θ0+δ0) − L(θ0) ≤ Σ|g_j|ε_j + ½Σ c_j ε_j²`.

At a stationary point the price is purely second-order
(`fisher_quant_loss_bound_opt`, :226); curvature-weighted budgets
dominate uniform ones (`fisher_beats_lipschitz`, :316; `fisher_alloc_mono`,
:350).

**GPM-relaxed with σ_tail.**

> **Theorem (rank_trunc_forgetting_bound).**
> `Hagi/Theory/Continual.lean:239`. A rank-truncated GPM step changes
> the response on an old input by at most `‖row‖ · sigmaTail` — the
> forgetting budget is tail energy leakage, not zero.

> **Theorem (gpm_tradeoff).** `Hagi/Theory/Continual.lean:346`.
> Old-input forgetting and new-input progress are both bounded by the
> same `‖row‖·sigmaTail` product. The ε² compromise is exact.

At full projection P = 1 the tail vanishes and the relaxed theory
degenerates to exact zero-forgetting (`gpm_full_zero`, :284). When the
projection covers the new input, every admissible step has exactly zero
progress — the machine-checked all-HOLD phenomenon (`gpm_hold_when_covered`,
:370).

**Per-step selector over four mechanisms** (zero-GPM, full-GPM,
rank-trunc, A-GEM), driven by measured state (conflict sign ⟨g, g_old⟩,
span fullness). The deterministic selector `hybrid_step_sound`
(`Hagi/Theory/Continual.lean:456`) picks the branch with NO weakening of
its guarantee.

| measured state | mechanism | what it gives |
|---|---|---|
| no conflict (dot ≥ 0) | A-GEM free step | full gradient, zero price |
| rare conflicts at task start | A-GEM | progress 0.267 vs 0.050 |
| per-point forgetting bound required | rank-trunc | forgetA −0.0013 vs −0.140 |
| span(A) exhausted | rank-trunc | only escape |
| strict zero influence on old task | full-GPM | exact, expensive |
| non-conflicting task allows zero step | zero-GPM | cheap, no progress guarantee |

Head-to-head, same task/wA/budget/eta/grid (24 steps, exact `Fraction`s):

| arm | B_progress | forgetA | committed | holds |
|---|---|---|---|---|
| rank-trunc | 0.0499 | −0.0013 | 24 | 0 |
| A-GEM | 0.2667 | −0.1402 | 24 | 0 |

A-GEM advances ×5.3 faster; all 18 conflict projections had interference
EXACTLY zero (`agem_step_nonneg_interf`, `Hagi/Theory/Continual.lean:326`).
A-GEM guarantees only first-order non-interference. On the measured
selector snapshot conflicts were 0/24, so the hybrid degenerated to the
free A-GEM policy (progress 0.4322, forgetA −0.3831), while the degenerate
rank-trunc arm (k=2=rank) kept forgetA exactly 0 (pin 7).

**Sandwich-softmax certified prediction.**

> **Theorem (cert_pred_adaptive).** `Hagi/Theory/Softmax.lean:810`.
> If every class's certified band around the softmax is at most 2ε wide
> and the true softmax gap exceeds 2ε, the band midpoint argmax is
> certified.

Refining the walls (larger n, m) never un-certifies a prediction
(`cert_pred_adaptive_mono`, :833; `bandWidth_mono`, :781), built on
`sandwich_mid_acc` (`Hagi/Theory/Softmax.lean:406`) and `sandwich_descent`
(`Hagi/Theory/CertSandwichBench.lean:65`). Does not claim: accuracy — the
band premise `BandDescribes z lo hi` is a measurement premise
(`Hagi/Theory/TrainerBenchmark.lean:60`, pin 1).

### 4.3 Growth, compression and the self-improving loop

**Repeated certified trunk growth.** Three identity-grow events in one
run grow the trunk depth 2 → 3 → 4 → 5, each grow asserting the EXACT
objective invariant (residual-zero identity, γ=0; neutral admission +
negative control ε=1/10 ⇒ REJECT), followed by certified
finite-difference training of the new block only. Soundness:
`grow_blocks_repeat_sound` (`Hagi/Theory/GrowTrunkBlock.lean:148`) and
`grow_blocks_obj_invariant_repeat` (`:164`).

| depth | max feature denominator (digits) | certified steps |
|---|---|---|
| 3 | 280 | 4 (block 3) |
| 4 | 840 | 4 (block 4) |
| 5 | 2520 | 4 (block 5) |

16 certified steps, objective strictly decreasing between grow-trainings
and exactly invariant at each grow. Limit: denominators grow ×~3.2 per
grow, so depth 6 projects to ~8000 digits.

**Snap-rational grow.** After a block is certified-trained, its weights
and features snap to q/2^40 (banker's rounding, exact `Fraction`
arithmetic, per-value error ≤ 2^-41) with a certified per-point error
bound (2|s−y| + |ds|)·|ds| and a telescoped final guarantee
obj_final ≤ obj_cycle_start + Σ bounds (cumulative ~2.7e-38). Lean:
`snap_preserves_objective_bound` (`Hagi/Theory/GrowSnap.lean:81`),
`snap_denominator_reset` (`:119`), `grow_snap_cycle_sound` (`:145`).

| | exact arithmetic | snap q/2^40 |
|---|---|---|
| max trunk depth reached | 5 | 8 (6 grow events, 28 certified steps) |
| feature denominators | 2520 digits (depth 5) | 13 digits (bounded 2^40, asserted at every grow) |
| cycle time | 62 s | 8.1 s |

Does not claim: snap is not objective-monotone — the certified state
carries a bound, not a drop; 3 of the 6 snaps actually improved the
objective.

**Four certified growth mechanisms.** All admit new capacity by an EXACT
objective-invariant admission and train only the new parameters by
certified steps.

| mechanism | new params/grow | max depth | maxden |
|---|---|---|---|
| identity/fiber block | 21 (block) | 8 (snap) | 13 digits (snap) |
| adapter r=1/r=2 (LoRA side-branch) | 8/16 (2·r·d) | — | exact Fractions |
| adapter + snap composite (8 levels r=1) | 8/level, 64 total | 10 | 13 digits (≤2^40, every level) |
| SVD-Matryoshka merge (stack → single) | 16 (rank ρ=2) | 10 → 1 matvec | 13 digits |

Core theory (Hagi/Theory/AdapterGrowth.lean): `adapter_neutral_B` (:103)
— B = 0 makes the side-branch EXACTLY neutral for arbitrary A;
`adapter_step_certified` (:190) — COMMIT
only on a measured strict drop; `adapter_param_count` (2·r·d) with
`adapter_param_count_le_block` (2rd ≤ d² at 2r ≤ d). Measured: adapter
r=1 = 8 and r=2 = 16 parameters vs 21 for the identity block; 12
certified steps, 0 holds.

*Composite stack.* 8 admission-train-snap levels of r=1 adapters grow
the trunk depth 2 → 10 at 8 parameters per level (64 total). Each level
snaps to q/2^40 and folds into the features, so every level restarts
from the grid — denominator compounding is structurally excluded.
Canonical run: start ≈ 2.283, total certified drop 2.271, 21 steps,
bit-identical deterministic repeat; cumulative snap error bound ≈
2.98e-13 against a certified drop of 2.27. Lean: `adapter_snap_cycle_sound`
(:283).

*Rank-adaptive selector.* At each level the selector PROBEs r=1 and r=2
on a copy (exact rollback; the live state never moves) and selects by
measured score = probe_drop/params (ties → r=1). `rank_select_deterministic`;
`rank_select_sound` (:328) keeps the full guarantee of whichever branch is
chosen. Measured: score(r=2) ≤ score(r=1) at all 8 levels, so the selector
picks r=1 every time (64 params, drop/param 0.035310, 17 steps); the r=2
arm reaches the same drop at ×2 parameters (128, 10 steps) and is
rejected.

*SVD-Matryoshka merge.* An exact rational Gauss-Jordan rank-ρ
factorization merges the stack into a single adapter:
`adapter_stack_rank_bound` (:416, rank(Π(I+Eᵢ) − 1) ≤ Σ rank Eᵢ),
`adapter_merge_error_bound` (:457, σ_tail + ℓ¹-Lipschitz),
`adapter_merge_params` (:443). Measured (exact rank of Δ = 2):

| model | params | matvec | obj change | certified bound |
|---|---|---|---|---|
| stack 8×r=1 | 64 | 8 | final 1.02460e-2 | cycle bound holds |
| merged k=ρ=2 | 16 (−75%) | 1 | −6.7e-11 (improvement) | 6.60e-8 |
| merged k=1 | 8 (−87.5%) | 1 | ~0.51 degradation | holds, unusable |

k=1 (σ_tail ≈ 0.998) is correctly reported unusable; the data gave
rank 2 < min(d,L) = 4, so the bound is not vacuum.

**External observations as theorems.** Instead of porting the consumer's
code, its top observed defects were formalized (docs/PROPOSAL-external-plan.md).

*(1) Weight-decay leak.* `wd_proj_preserves`: projected decay
W′ = W − ηλ·(W − W·P) keeps W·P EXACTLY (measured leak 5.68e-15 =
machine zero); naive decay (1−ηλ)·W has the EXACT leak factor (1−ηλ) on
the protected component (`naive_decay_parallel`, `naive_decay_norm`),
leaks strictly (`naive_decay_leak`, :128; measured naive leak 1.945);
`wd_gpm_step_sound` (:159) composes a black-box complement step with
projected decay.

*(2) Empirical-Bernstein radius.* `empirical_bernstein_bound` /
`_mean_bound` (+ `freedman_tail_two_sided`, `eb_radius_algebra`): with
measured σ̂² and range b, |μ̂| < √(2σ̂²L/n) + 2bL/n at ≥ 1−α. Witness
contrast (ΔCE=0.04, R=11.09, α=0.01): n_Hoeffding = 176 995 vs
n_EB(MP form) = 6439 — 27.49× fewer samples (our form: 4267, 41.5×).
Does not claim: σ̂ is a runtime premise (no MP λ-trick).

*(3) Observational-equivalence search completeness.* `oe_search_complete`
(:80): OE-dedup search never loses a solution that matches the target on
the probes. Witness: toy space 343 → 4 visits (~86×); the consumer's
analogue compressed 6478 → 896 candidates (7.2×). Does not claim:
completeness is RELATIVE TO THE PROBES, no semantic equivalence (pin 11).

*(4) Exact bypass, zero cross-entropy.* On a PROVEN_EXACT coverage the CE
contribution is EXACTLY zero: `ce_pointwise_of_prob_one`,
`ce_total_eq_residual` (:90) — total = residual (witness 4.264244 ==
4.264244); `exact_gate_sound` (:97) and the negative `exact_gate_rejects_zero`
(p = 0 ⇒ rejected).

*(5) Polar-Express interval certificate.* A scalar, SVD-free interval
certificate for the minimax Newton–Schulz iteration: three rationalized
polynomials p(x) = ax+bx³+cx⁵ map the spectral box by EXACT rational
bounds: [1/1000, 1] → [1/256, 1313/1024] → [5/512, 601/512] → final
[9/512, 1049/1024] ≈ [0.0176, 1.0244] (`polar_express_step3_bound`,
Hagi/Optimization/PolarExpressCert.lean:372). Does not claim: the upper
end is 1.0244, i.e. the iteration does not pin the top of the spectrum to
exactly 1 (pin 10).

**Adapter continual isolation.** Per-task adapters give zero forgetting
STRUCTURALLY — `adapter_isolation_zero_forgetting` (Hagi/Theory/AdapterGrowth.lean:564)
and `adapter_per_task_sound` (Hagi/Theory/AdapterGrowth.lean:579) need no projections
or budgets. Measured head-to-head (conflict-pinned task B, same
trunk/data/eta/grid): ISO forgetA = 0 EXACT vs SHARED +0.2331 vs
naive-trunk +5.5757 (`trunk_update_needs_projection`, :618). On a
same-distribution B the measured forgetting was negative (SHARED −0.304 /
TRUNK −0.753): forgetting is a conflict phenomenon.

**The full loop in one trace** (`--mode mini-hagi-loop`, real
unified_ledger, 113 points).

> **Theorem (full_loop_sound).** `Hagi/Theory/MiniHagiLoop.lean:64`.
> Composition of `exact_gate_sound` + `adapter_step_certified` +
> `adapter_isolation_zero_forgetting` + `oe_search_complete` +
> `empirical_bernstein_mean_bound` — no new deep facts, only certified
> composition.

One trace: the exact gate covers 107/113 (const 3/2, CE of covered = 0
EXACT, wrong-const negative err = 1/4); adapter A takes 10 certified
steps (CE 4 → 0.1216, a HOLD negative leaves the state unchanged); a
grow with neutral admission + snap is objective-invariant bit-for-bit (6
steps); per-task isolation gives forgetA = 0 EXACT while the SHARED
negative leaks 1.386; OE dedup + the EB gate accept a const-2 law (+5
EXACT, coverage 112/113, n_EB 9649 ≤ n_Hoeffding 10851). Total: 26
certified steps, 1 hold, 10 parameters (2 adapters).

Limits: the EB contrast on this corpus is 1.12× (vs 27.49× in the
calibration instance) — a property of the data (pin 9); one position
remains uncovered after the OE space was exhausted.

**Iterative self-improvement.** One run executes 7 iterations: OE-search
in a space GROWN from the accepted primitives → EXACT coverage extension →
adapter retraining on the shrinking residual (certified snap-GD, 10
steps/iteration) → EB telemetry.

> **Theorem (iterative_loop_sound).** `Hagi/Theory/MiniHagiLoop.lean:154`.
> Coverage at step k is a subset of coverage at step n for all k ≤ n. The
> only new mathematical fact is monotonicity: `coverage_append_monotone`
> (`:134`, via `coversPrim` `:128`, `iterStep` `:122`, `IterState` `:117`);
> per-iteration soundness is `full_loop_sound` with no weakening.

Coverage 0 → 54.9 → 71.7 → 78.8 → 85.0 → 89.4 → 93.8% over six
iterations (accepted: const, affine on p1, affine² on p3, then real
tau-clusters); iteration 7 accepts 0 and stops by the EB gate. Residual
CE is certified per iteration; e.g. 1504.8 → 1153.0 at iteration 1.

60 certified steps, 0 holds. In-run negatives: law 2 is NOT found without
block 1, law 3 NOT without block 2 — the chain p1 (const) → p3 (aff) →
p5 (aff²) is genuinely compositional. Does not claim: these synthetic laws
do not transfer to the real corpus (pin 12).

**Universal loop on the full live corpus** (all 113 live points of all
domain keys; targets are REAL snap(ce_i, 1/16)).

> **Theorem (universal_loop_corpus_mono).**
> `Hagi/Theory/MiniHagiLoop.lean:190`. Union-additivity of coverage over
> corpus concatenation lA ++ lB, composed with `iterative_loop_sound`.

Iterations: it1 — 4 constant clusters, 0 → 64/113; it2 — const 3/2 →
86/113; it3 — const 23/16 → 106/113 (93.8%); it4 — 0 accepted, EB-gate
STOP. 1826 adapter steps (drop > 0), 134 HOLD; forgetA = 0 on ALL 113
domains (bit-exact parameter-snapshot asserts). The honest part: the
93.8% coverage is achieved ENTIRELY by constant clusters; NOT ONE linear
law was found (every candidate < 5 new positions) — a measured
applicability boundary of the loop, not a failure of the search; the
synthetic laws above cover 0/113 of the real targets.

**Unification: one adapter machine** for the knowledge lifecycle (admit,
learn, merge, distill, cover), a rank-bounded adapter stack.

*Self-compressing loop.* The loop learn→merge→learn admits rank-1 levels
with an EXACT objective invariant (B = 0), trains all live parameters by
certified fd-steps, and merges exactly (Gauss–Jordan over Fractions).
Measured on the full live corpus (113 domains): parameters after EVERY
merge ≤ 2·K·d = 32 while the no-merge contrast grows linearly to 2·L·d =
48; cumulative certified drop monotone 0.158→0.364; residual CE
0.4354→0.0717 (−84%); 56 certified steps / 0 HOLD.

> **Theorem (self_compress_loop_sound).**
> `Hagi/Theory/AdapterGrowth.lean:722`. The loop telescopes the objective
> (delegate of grow_snap_cycle_sound, generalized to a merge cycle) AND
> keeps params ≤ selfCompressParams k d = 2·k·d for ANY number of
> iterations (`self_compress_params_bounded`, :700; strict contrast
> `self_compress_params_contrast`, :710).

Negative: squeezing below k = d destroys knowledge on this corpus
(matryoshka k = 3 degrades to 5.44, k = 2 to 1.22 — both covered by the
certified bound marking them unusable).

*Lossless distillation of constant clusters.* The constant clusters are
distilled into rank-1 adapters θ(c) = (A := 0, B := const c): the output
≡ c on ANY input, EXACTLY, with zero training steps. Measured: cluster CE
0.7831 → 0 BIT-EXACT; exact-gate branches 113 → 0.

> **Theorem (constant_distill_exact / distill_coverage_preserved).**
> `Hagi/Theory/AdapterGrowth.lean:782` / `:824`. The distilled readout is
> exactly c, so coverage and CE = 0 are PRESERVED.

Does not claim memory savings: the distillate costs 6×2d = 48 parameters
while symbolic storage needs only the 6 values (`symbolic_storage_cheaper`,
:853: J < 2·J·d for d ≥ 2). The value is UNIFICATION of paths.

**Mini-HAGI v3: the full certified assembly in one trace** (live corpus
snapshot, 115 points).

| phase | mechanism | measured result |
|---|---|---|
| P1 bypass | exact-gate const clusters | 6 clusters, 108/115, coverage monotone bit-exact |
| P2 distill | θ(c_j) rank-1 adapters, certified init | cluster CE = 0 BIT-EXACT; gate branches 115 → 0 |
| P3 adapter residual | certified fd-steps | 7/7 committed, residual CE 3.8022 → 0.5120 |
| P4 self-compress | admit→learn→exact-merge, K=d=4 | params ≤ 32 after EVERY merge; obj 0.5120 → 0.0733; merge telescope = 0 |
| P5 EB stop | commit = 0 ⇒ STOP | branch active; actual stop = budget MAX_ITER = 6 (pin 16) |
| total | v3_assembly_sound | 55 certified steps, 0 holds, forget = 0, params ≤ 32, 1.87 s |

> **Theorem (v3_assembly_sound).** `Hagi/Theory/AdapterGrowth.lean:884`.
> The unified adapter machine is the CONJUNCTION of the distill branch
> and the self-compress branch — composition with NO weakening of the
> components' hypotheses. No new deep facts.

### 4.4 Reading: cost of n bytes with width-w windows

**(i) The information-theoretic floor.** No coverage of [0, n) by width-w
windows can use fewer than ⌈n/w⌉ windows:

> `theorem hier_total_floor (L : List ℕ) (w n : ℕ) (hw : 0 < w)`
> `(hcover : ∀ i < n, ∃ t ∈ L, t ≤ i ∧ i < t + w) : n ≤ L.length * w`

(`Hagi.Theory.CoverageReading.hier_total_floor`, Hagi/Theory/CoverageReading.lean:494).
The hierarchy of clause (10) ATTAINS the floor at `s = w`, `w ∣ B` —
`hier_total_min` (:462): `(hierStarts n B w w).length = (n + w - 1) / w`,
closed by `hier_optimal` (:533). Geometry, not algorithm: k windows cover
at most k·w bytes. Measured: the total is CONSTANT in B at s = w — n =
100000, w = m = 64 gives 1563 = ⌈100000/64⌉ for every B ∈ {64, 2048,
4032, 4096}, so a hypothesized interior optimum B* = √(nw) is REFUTED;
shrinking the stride below the width only pays (s = 32, B = 1088 reads
3033 > 1563); at n = 8128 the floor-attaining total is 127.

**(ii) Three cost regimes.** With per-read window cost c(w), totalCost(w)
= ⌈n/w⌉·c(w) (Hagi/Theory/CoverageReading.lean):

- (a) fixed cost c(w) = c: totalCost = c·⌈n/w⌉ is monotonically
  non-increasing in w (`windowCost_fixed_mono`, :577, core `ceil_div_anti`
  :555) — the certified choice is w = w_max;
- (b) linear cost c(w) = c·w: totalCost is nearly width-INDEPENDENT —
  `w·⌈n/w⌉` sits in [n, n + w − 1] (`windowCost_linear_bounds`, :586)
  and any two widths differ by less than the cost of one window
  (`windowCost_linear_near_const`, :602) — w is free, choose it for
  accuracy;
- (c) mixed cost c(w) = a + c·w^α, α > 1: certified at α = 2 only (iv).

The bridge back to (i) is `windowCost_hier` (:613): at w ∣ B the
machine's total IS ⌈n/w⌉ reads. Measured (n = 100000): w ∈ {16, 64, 256}
→ reads {6250, 1563, 391}; linear-regime totals {100000, 100032,
100096}, each inside the corridor [100000, 100000 + w).

**(iv) mixed-w* at α = 2, three clauses (Lean-verbatim).**

> `theorem mixedCost_relax_min {a c w : ℝ} (ha : 0 < a)` `(hc : 0 < c)`
> `(hw : 0 < w) : 2 * Real.sqrt (a * c) ≤ a / w + c * w`

(:630 — AM-GM at u = a/w, v = c·w);

> `theorem mixedCost_relax_min_eq {a c : ℝ} (ha : 0 < a)` `(hc : 0 < c) :`
> `a / Real.sqrt (a / c) + c * Real.sqrt (a / c) = 2 * Real.sqrt (a * c)`

(:650 — equality at w = √(a/c), the α = 2 case of
w* = (a/(c·(α−1)))^(1/α)); and the discrete lower bound

> `theorem mixedCost_lower {n w : ℕ} {a c : ℝ} (ha : 0 < a)` `(hc : 0 < c)`
> `(hw : 0 < w) : 2 * (n : ℝ) * Real.sqrt (a * c)`
> `≤ ((n + w - 1) / w : ℕ) * (a + c * (w : ℝ) ^ 2)`

(:675 — via the ceil-bridge `windowCost_linear_bounds` + the relaxation
×n). Does not claim: this is a LOWER bound; discrete equality needs
w ∣ n and w = √(a/c) simultaneously; general α > 1 remains
Real-calculus outside the Nat model of the file.

**Bench application.** `cost_regime_w` in scripts/bench_bridge.py is the
python twin of the three regimes (exact `fractions.Fraction` arithmetic,
fail-closed asserts), exposed as `--cost-regime {fixed,linear,mixed}` in
`--mode generate-hier` (instances n = 540/4032/8128/100000). The numbers
above are pinned asserts: python and Lean #eval agree verbatim.

### 4.5 Optimizer theory: the Muon chain

Optimizer bridges, one row per module. **Code** is the consumer's line
the row is checked against; **status** is exact, conditional or honest gap
as in §2.2. Each row states a theorem, not a code fact.

| module | declarations (Lean anchor) | fact | code | status |
|---|---|---|---|---|
| GradLayer | `hasFDerivAt_w1L` (Hagi/Theory/FirstLayerGrad.lean:87); `w1_grad_rank_one` (:123); `batch_directional_derivative` (Hagi/Theory/BatchRankOne.lean:65); `sgd_step_attains` (:136) | outside the kink `f'(W1)[Δ] = ⟨G, Δ⟩` with the rank-one `G = g ⊗ x` (batch `Σ_t g_t ⊗ x_t`); −G/‖G‖_F is the steepest step in the Frobenius ball | first layer `W1`, hagi/lm.py:586/:594 @ca52eb4 | honest gap: strict descent only (no certified drop) |
| OptimalStep | `rank_one_inner_le` (Hagi/Theory/MuonSpectral.lean:156); `rank_one_attains` (:231); `smax_eq_opNorm` (Hagi/Theory/MuonSpectral.lean:333); `smax_le_frobenius` (:354) | the rank-one step attains σ_max (Courant–Fischer) = `‖G‖₂` ≤ `‖G‖_F` | `newton_schulz_orthogonalize` (hagi/core.py:1350, iters=3 at core.py:1755 @ca52eb4) | honest gap: rank-one slice of the spectral ball |
| Muon | `muon_step_optimal_in_isometry_group` (Hagi/Theory/MuonIsometry.lean:175); `ns_defect_bound` (Hagi/Theory/NewtonSchulzSigma.lean:83), `ns_sigma_min_three` (Hagi/Theory/NewtonSchulzSigma.lean:126); `muon_alignment_exact` (Hagi/Theory/MuonAlignment.lean:104); `normed_sigma_le_one` (Hagi/Theory/MuonDescent.lean:122), `muon_step_useful` (Hagi/Theory/MuonDescent.lean:176) | `max_{ΔᵀΔ = I} ⟨G, Δ⟩ = ssum G` at `U Vᵀ`, no von Neumann; the code's scheme σ ↦ σ(3 − σ²)/2 keeps the singular vectors of `G` and gives σ₃ ≥ 39/40 for σ₀ ≥ 1/2, `⟨G, ns₃(Ĝ)⟩ ≥ ‖G‖_F` | Newton–Schulz iteration (hagi/core.py:1363, Frobenius normalisation core.py:1353) | honest gap: `η` only exists |
| W1 (square) | `w1_fderiv_apply` (Hagi/Theory/MuonDescentW1.lean:65); `muon_step_useful_w1` (:104); `muon_step_useful_w1_batch` (:193) | derivative identity for the square layer `W1` (one input, batch); certificate instantiated | batch cross_entropy mean lm.py:688 | honest gap: momentum `m1`, `cos_lr·0.7`, Lipschitz bound, convergence |
| Rectangular iterate | `code_step_eq_ns_step` (Hagi/Theory/MuonWide.lean:52); `ns_step_wide_svd` (:61); `ns_iter_wide_svd` (:116); `wide_alignment_exact` (:163); `wide_alignment_ge_gradient` (:178); `wide_step_optimal` (:245) | the code line equals the proved rectangular step `ns_step` for `m×n`; given `G = U·diag σ·Vᵀ`, `UᵀU = VᵀV = I`, every iterate keeps the singular bases, `⟨G, X_k⟩ = Σ σ i·ns_seq k (σ i)`, `≥ ⟨G, G⟩` for `σ i ≤ 1`; max over row isometries `ΔΔᵀ = I` is `Σ σ i` at `U Vᵀ` | transpose when rows > columns (hagi/core.py:1358), `X = 0.5 * (3.0 * I_m - X @ X.T) @ X` (core.py:1363), transpose back; zero-norm guard core.py:1355; iters = 4 by default, 3 at core.py:1755 @ca52eb4 | honest gap: zero-norm guard is a code fact without a theorem |
| WideSVD | `exists_wide_svd` (Hagi/Theory/WideSVD.lean:155); `wide_alignment_exact'` (:306); `wide_step_optimal'` (:317); `wfrobSq_eq_sum_sigma_sq` (Hagi/Theory/WideSVD.lean:372); `wnormed_sigma_le_one` (:391); `wide_alignment_ge_gradient'` (:418); `muon_step_useful_wide` (:446) | every real `m×n` matrix with `m ≤ n` is `U·diag σ·Vᵀ`, `UᵀU = VᵀV = I` — the alignment statements hold without a decomposition hypothesis; the normalised wide gradient has `σ i ≤ 1`, so `⟨G, wide_iter k Ĝ⟩ ≥ ‖G‖_F` with no structural hypothesis on `G` | transposition (hagi/core.py:1358 @ca52eb4) | honest gap: certificate on the coordinate carrier `m → n → ℝ` |
| Tall buffer | `ns_step_transpose`, `code_ns_eq_wide_iter` (Hagi/Theory/MuonWide.lean:261/:286) | the code's transpose–iterate–transpose equals `wide_iter k G` for a buffer of any shape: an efficiency device only | transposition of a tall buffer (hagi/core.py:1358–1361 @ca52eb4); Frobenius normalisation core.py:1353 | exact for the step; honest gap: descent certificate not instantiated on this carrier |
| W1, `card ι ≤ card δ` | `w1_fderiv_apply_R` (Hagi/Theory/MuonDescentW1Rect.lean:63); `muon_step_rect_of_fderiv` (:113); `muon_step_useful_w1_rect` (:134); `muon_step_useful_w1_rect_batch` (:203) | for `W1 : ι → δ → ℝ` with `card ι ≤ card δ`, outside the kink, `G ≠ 0`, CE strictly decreases along `W1 − η·wide_iter k Ĝ` | rectangular first layer `W1 : dim × hidden` (hagi/lm.py:586 @ca52eb4) | honest gap: mean loss |
| W1, any shape | `fdot_transpose` (Hagi/Theory/MuonDescentW1Rect.lean:248); `wnormed_transpose` (:264); `tall_alignment_ge_gradient` (:276); `alignment_ge_gradient_any` (:300); `w1StepR_eq_code_ns` (:321); `muon_step_useful_w1_rect'` (:348); `muon_step_useful_w1_rect_batch'` (:369) | the dimension premise removed: for the layer of ANY shape, outside the kink, `G ≠ 0`, `⟨G, wide_iter k Ĝ⟩ ≥ ‖G‖_F` and CE strictly decreases, any `k`; the theorem's step equals the code's output `code_ns` | Muon update hagi/core.py:1755 | honest gap: von Neumann, `η`, momentum, mean loss |
| SmoothLip | `w1CE_lipschitz_param` (Hagi/Theory/FirstLayerLip.lean:182); `w1CE_descent_lemma` (:258); `w1CE_drop_of_step` (:339); `w1CE_optimal_step_drop` (:392) | the CE of the relu block is globally 2·‖wo‖_F·‖x‖₂-Lipschitz in `W1`; inside one activation region the gradient is ‖wo‖_F²·‖x‖₂²-Lipschitz; the plain-GD step γ* = 1/S with drop ‖D‖²/(2S) is a computable number | growth gate L := CE value (hagi/unified.py:400 @ca52eb4); certified-step curvature denom = Q' + 4·curv_reg (hagi/core.py:1314 @ca52eb4); Adam lr 3e-3 | honest gap: no global smoothness across the kink, one input; the code logs neither ‖wo‖_F nor ‖x‖₂ and its Adam step is normalised; the step's directional curvature `denom` is a different, already measured quantity (`ce_range_code_drop`) |
| SmoothBatch | `w1BatchCE_descent_lemma` (Hagi/Theory/FirstLayerLipBatch.lean:113); `w1BatchCE_optimal_step_drop` (:218); `w1MeanCE_optimal_step_drop` (:247); `S_batch_le_max` (:86) | `S_batch = ‖wo‖_F²·Σ_t‖x t‖₂²` (≤ `B·‖wo‖_F²·max_t‖x t‖₂²`); the batch-gradient step drops at least `nlDrop γ S_batch ‖D_batch‖_F` with `γ*_batch = 1/S_batch`; for the mean loss `S_mean = S_batch/B`, `γ*_mean = B/S_batch` | `ce(reduction="mean")` (hagi/lm.py:299 @ca52eb4) | honest gap: no smoothness across the kink; the code's direction is Muon/Adam on `m1`; telemetry not in the code |
| MomentumAlign | `dir_drop_optimal` (Hagi/Theory/MomentumAlign.lean:112); `momentum_align` (:140); `momentum_align_ge` (:169); `momentum_dir_drop_le_gd` (:207); `w1BatchCE_dir_optimal_step_drop` (:261); `muon_momentum_bound` (:419); `muon_momentum_third` (:442) | see **Momentum** below | momentum buffer `m1 = 0.85·m1 + 0.15·gW1` (hagi/core.py:1754 @ca52eb4, EMA without Nesterov term or bias correction); Muon update core.py:1755 orthogonalises `m1` | honest gap: the residual condition is not checked by the code, `cos_lr·0.7`, kink, telemetry |

The last three rows sit at the layer `W1` of the growth block (hagi/lm.py:586).

**Result (final for the code dimension).** For the first layer
`W1 : ι → δ → ℝ` of the growth block (ANY shape — wide, square or tall),
outside the relu kink, with the batch gradient `G = −Σ_t g_t ⊗ x_t ≠ 0`
(one input: `g ≠ 0`, `x ≠ 0`), for any `k`:

1. `CE(W1 − η·wide_iter k (Ĝ)) < CE(W1)` for all small `η > 0`,
   `Ĝ = G/‖G‖_F` (`muon_step_useful_w1_rect'`,
   Hagi/Theory/MuonDescentW1Rect.lean:348; batch
   `muon_step_useful_w1_rect_batch'`, :369; versions with the premise
   `card ι ≤ card δ`: :134 and :203).
2. First-order drop: `f'(W1)[−η·ns_k(Ĝ)] ≤ −η·‖G‖_F`
   (`alignment_ge_gradient_any`, Hagi/Theory/MuonDescentW1Rect.lean:300;
   wide form `wide_alignment_ge_gradient'`, Hagi/Theory/WideSVD.lean:418;
   square case `muon_step_inner_ge_frob`, Hagi/Theory/MuonDescent.lean:136);
   the sign step gives the same bound in the square case
   (`muon_vs_sign_first_order`, Hagi/Theory/MuonDescent.lean:196).
3. Three iterations vs the optimum: on the part of the spectrum with
   `σ i ≥ 1/2` (in Ĝ units, i.e. `σ i(G) ≥ ½‖G‖_F`),
   `⟨Ĝ, ns₃(Ĝ)⟩ ≥ (39/40)·Σ_{σ i ≥ 1/2} σ i` (`muon_near_optimal`,
   Hagi/Theory/MuonAlignment.lean:131; `ns_sigma_min_three`,
   Hagi/Theory/NewtonSchulzSigma.lean:126). The ideal `U Vᵀ` is optimal on
   the whole isometry group (`muon_step_optimal_in_isometry_group`,
   Hagi/Theory/MuonIsometry.lean:175). On the row isometries of a
   rectangular `G` the optimum is the same `Σ σ i`, attained at `U Vᵀ`
   (`wide_step_optimal'`, Hagi/Theory/WideSVD.lean:317).

Witnesses (Lean #eval): `σ₀ = 1/2 ⇒ σ₃ ≈ 0.975300`; on
diag(1, 3/4, 1/2, 1/10) the bound is `(39/40)·(9/4) = 351/160` and
`⟨G, X₃⟩ ≈ 2.270356` against `ssum G = 2.35`; on `G = diag(3, 3/2, 1/2, 1/5)`
`‖G‖_F² = 577/50`, `⟨G, sign G⟩ = 26/5` (external floating-point, not in
Lean: `⟨Ĝ, X₃⟩ = 1.38284`, per unit of step norm Muon 0.941038 against
sign 0.765368).

**Rectangular iterate.** The code does not apply the square iteration to
the gradient: `newton_schulz_orthogonalize` (hagi/core.py:1349 @ca52eb4)
returns `X` unchanged when `norm(X) < 1e-12` (core.py:1355), transposes to
the wide shape when rows > columns (core.py:1358), iterates
`X = 0.5 * (3.0 * I_m - X @ X.T) @ X` (core.py:1363), transposes back.
In Hagi/Theory/MuonWide.lean `(3I − XXᵀ)X = X(3I − XᵀX)`, so the code
line is the rectangular `ns_step` (`code_step_eq_ns_step`, :52); given
`G = U·diag σ·Vᵀ`, the step multiplies each singular value by `ns_p`
(`ns_step_wide_svd`, :61), hence `X_k = U·diag (ns_seq k∘σ)·Vᵀ`
(`ns_iter_wide_svd`, :116) and `⟨G, X_k⟩ ≥ ⟨G, G⟩` for `σ i ≤ 1`
(`wide_alignment_ge_gradient`, :178). For `ΔΔᵀ = I`,
`(UᵀΔV) i i = ⟨Δᵀu_i, v_i⟩ ≤ 1`, so `⟨G, Δ⟩ ≤ Σ σ i` (`wide_step_optimal`,
:245). Witness: on diag(3/4, 1/2) padded with a zero column, Lean checks
`ns_step G = U·diag(117/128, 11/16)·Vᵀ`, `⟨G, G⟩ = 13/16`,
`⟨G, UVᵀ⟩ = 3/4 + 1/2`.

The wide SVD is a theorem (`exists_wide_svd`: pad `G` to `n×n`, square
SVD, the `≥ n − m` zero singular values through `rank (GᵀG) = rank G ≤ m`,
then a square SVD of `G·V₀`). The last premise closes for a wide `G`:
`‖G‖_F² = Σ σ i²` (`wfrobSq_eq_sum_sigma_sq`, Hagi/Theory/WideSVD.lean:372), hence `Ĝ` has
`σ i ≤ 1` and `⟨G, wide_iter k Ĝ⟩ ≥ ‖G‖_F` with no structural hypothesis;
`muon_step_useful_wide` (:446) gives the descent certificate on the
premises of `muon_step_useful`. A tall buffer is the same `wide_iter k G`:
`ns_step Xᵀ = (ns_step X)ᵀ`, so the transposition is an efficiency device
only. Witness: `G = diag(3, 4)`, `‖G‖_F² = 25`, `σ(Ĝ) = (3/5, 4/5)`.

**Bridge to the rectangular layer.** `w1_fderiv_apply_R` (:63) and
`w1Batch_fderiv_apply_R` (:166) go through verbatim with
`Matrix ι δ ℝ`; no sup-versus-ℓ² issue arises because the descent lemma is
one-dimensional along the ray `W1 − η·d`
(`MuonDescent.useful_of_neg_fderiv`, generic in `E`). The core
`muon_step_rect_of_fderiv` (:113) gives `muon_step_useful_w1_rect` (:134)
and `muon_step_useful_w1_rect_batch` (:203) (witness, Float replica: a
`3×4` layer, `⟨G, wide_iter 3 Ĝ⟩ = ‖G‖_F = 1.870829`). **Tall layer.**
`⟨Gᵀ, Hᵀ⟩ = ⟨G, H⟩` (`fdot_transpose`, :248), `wnormed Gᵀ = (wnormed G)ᵀ`
(`wnormed_transpose`, :264) and `wide_iter k Xᵀ = (wide_iter k X)ᵀ`
carry the wide certificate over (`tall_alignment_ge_gradient`, :276;
`alignment_ge_gradient_any`, :300); the step of the theorem is the code's
output (`w1StepR_eq_code_ns`, :321). Witness: a `4×3` layer, `‖G‖_F² =
7.2`, `⟨G, wide_iter 3 Ĝ⟩ = ‖G‖_F = 2.683282`. The zero-norm guard and
`iters = 3` remain code facts without a theorem.

**Lipschitz constants of the first layer.** For the relu block
`relu(W1ᵀx + b)ᵀ wo` the CE loss is globally 2·‖wo‖_F·‖x‖₂-Lipschitz in
`W1`, and inside one activation region its gradient is
‖wo‖_F²·‖x‖₂²-Lipschitz (`lse_descent` + Cauchy–Schwarz), so the
plain-GD step γ* = 1/S with drop ‖D‖²/(2S) is a computable number
(`w1CE_optimal_step_drop`, :392). Batch: `S_batch = ‖wo‖_F²·Σ_t‖x t‖₂²`
(at most `B·‖wo‖_F²·max_t‖x t‖₂²`, `S_batch_le_max` :86), `γ*_batch =
1/S_batch`; for the code's mean loss `γ*_mean = B/S_batch`
(`w1MeanCE_optimal_step_drop`, :247). Any direction `d ≠ 0`: `γ* =
a/(L‖d‖²)`, drop `a²/(2L‖d‖²)`, `a = −⟪∇f,d⟫` (`dir_drop_optimal`,
:112; `nlDrop` is the case `d ∝ ∇f`); for the layer with `S_batch`
(`w1BatchCE_dir_optimal_step_drop`, :261).

**Momentum.** `⟪G,m⟫ = 0.15‖G‖² + 0.85⟪G,m_prev⟫`, at least `0.15‖G‖²`
when `⟪G,m_prev⟫ ≥ 0` and at least `‖G‖²` when `⟪G,m_prev⟫ ≥ ‖G‖²`
(`momentum_align`, :140; `momentum_align_ge`, :169; not when merely `≥ 0`:
the unconditional bound `(1−μ)‖G‖²` is false). With `X = ns_k(m̂)`:
`‖m‖_F − ‖G−m‖_F·‖X‖_F ≤ ⟨G, X⟩` (`muon_momentum_bound`, :419), hence
`‖G‖_F/3 ≤ ⟨G, X⟩` whenever `‖G−m‖_F‖X‖_F ≤ ‖m‖_F/2` (a half is
impossible: `‖G‖ ≤ (3/2)‖m‖`; `muon_momentum_third`, :442); the certified
drop along `m` never exceeds `‖G‖²/(2L)` (`momentum_dir_drop_le_gd`,
:207). Not in the code: the value `0.85`, a check of the residual
condition, `cos_lr·0.7`, telemetry of `⟨G,m1⟩` and `‖G−m1‖_F`.

**What the optimizer theory does not claim.** (a) An explicit `η` (it only
exists; the code's `cos_lr·0.7` is not related to it), the momentum
value 0.85, the zero-norm guard and `iters = 3` (code facts), the relu
kink (a premise). (b) The maximum over the whole spectral ball `‖Δ‖₂ ≤ 1`
(von Neumann); the optimum is proved over the isometries only. (c)
Convergence; a Lipschitz descent lemma is in the theorem for `W1` only.
(d) The loss is the CE of one input or the batch sum; the batch mean has
a theorem of its own outside the master statement; in the batch theorem
`G ≠ 0` is a premise. (e) Singular values below `1/2` carry no lower
bound after three iterations. (f) Muon versus sign is compared by the
first-order drop, not per unit of step norm. Adam: only the first step is
in the theorem. The guards this gap asks of the code are in
docs/PROPOSAL-muon-guards.md (code-side pending).

### 4.6 Code bridges: what the consumer's code inherits

Statuses are defined in §2.2. This subsection states only what a table
cannot carry.

**Deltas, by step.** (i) Adaptive step: the clamped multiplier equals the
exact kappa only on the window (1e-5, 50]; the earlier claim, computed for
the unscaled step, was 400/39 ≈ 10.26× too large at lr_scale 0.05.
(ii) MGDA: the code minimizes over NORMALIZED gradients, the canon over
raw ones — the same point only at ε = 0 with equal ‖g_j‖; the Frank-Wolfe
rate is not formalized. (iii) Trunk growth: a verdict, 0 new theorems.
(iv) Warm-up: after step 0 Wo ≠ 0, "function preserved after training" is
false and cannot be a theorem; what is proved is conditional on h1, and in
the code h1 is NOT a fact (warm-up is bare Adam on (W1, b1, Wo), the
certified step writes to the trunk and certifies batch CE). (v) The
backtrack predicate is the code's own (β = 1/2, exactly 9 trials, no
σ·γ·⟪g,d⟫ term — not Armijo). (vi) The CE range lemma is about a shift of
LOGITS, so the certificate does not depend on which parameters carry the
step; the block-only JVP that would feed it is absent from the code.
(vii) Batch → global holds deterministically for a fixed batch and only
under an iid / independent-rounds model otherwise; the slack is
k·ebGap(α/k), which the code never evaluates.

**Measured, behind the honest-gap cells.** On the test config (dim 32,
hidden 64, seed 0, 12 steps) the adaptive branch is NEVER taken (eta* ≈
203–260 > 1): the certificate of the real code is `ce_range_code_drop`,
12/12 claim ≤ realised drop (e.g. claim 0.07396868055108989 ≤
0.07546329498291016). The code builds the majorizer on the JVP
displacement, the theorem is about the exact one: in a nonlinear LM (dim
16, hidden 32, 5 steps) rollback fired 2/5 (realised drop 0 < claim
0.083/0.095). MGDA stop: float32 gap 0.0 on all 6 probe cases. Adam is
not a certified descent from t = 2, so the backtracking gate is mandatory.

**Repair.** The loop accepts any improvement > 1e-4 (no contraction
factor ρ), so the theorem gives z ≤ v − tol·(accepted rounds) and the
gate may end above its pre value; the gate is a sample estimate (≤ 8
domains × 256 positions), and clause (2) of `master_theorem_v3` is not
instantiated (repair writes the shared trunk). Reported by the consumer's
commit, not re-measured: +0.553 → +0.036, 20/89 rounds hit rollback.

**Archiver — the ideal coder only.** The code's claim (archiver.py:1-4
@b3740e0) is "size within o(1) of −log₂ P(data), the ratio IS the model's
CE". Proved for len = ⌈−log₂ p̂⌉₊: **H(p) ≤ E_p[len] ≤ H(p) + KL(p‖p̂)/log 2
+ 1** (Kraft–McMillan + `ceBits p q = entBits p + klDef p q / log 2`); at
p̂ = p: H ≤ E[len] ≤ H + 1. The model is the IDEAL coder; p̂ is the 16-bit
CDF (freq = max(1, round(P·65200))); the round-trip is tests plus a
measured 11/11 (5.16 bit/byte vs zlib 2.40).

**Adam — a verdict.** ⟨g, d⟩ > 0 is a code fact only at t = 1; at β₁ =
9/10, β₂ = 999/1000, g₁ = 1, g₂ = −1/10 the second step has ⟨g, d⟩ < 0.
So the Adam step is accepted only by the measured `backtrackAccept`
(selfmodel.py:134-169 @b3740e0).

**Useful first step — the formula hit.** On a linear logit carrier,
**η* = 4|a|/R² and drop_max = 2a²/R²**: the first step is certifiably
useful iff the residual signal a ≠ 0 and 2a²/R² > stepEps; at a = 0
nothing commits. Witness: a = −1, R = 2 ⇒ η* = 1, drop_max = 1/2. The
chain rule a < 0 is proved for a LINEAR carrier (`chain_linear`,
`useful_of_adam_first`), for the relu block only as strict descent for
small η (`useful_of_adam_first_relu`), and for the first-layer matrix W1
(`hasFDerivAt_w1L`, `useful_of_adam_first_w1`); the nonlinear certified
drop is open (pin 31). hlin (linear logit displacement in η) is a
code-side JVP fact at Wo = 0, not a theorem.

**Window order.** After the consumer's window fix the context is
`idx[p−n .. p)` with the adjacent target; before it the target was
`idx[pos + k]` — a k-byte gap; measured CE 7.307 against 0.181 with the
adjacent target. The same bug was fixed in three more oldest-first
consumers (`_read_all_windows` left pad, the train_guarded holdout
window, `generate`); commit-message numbers, not re-measured: holdout CE
3.59..4.23 nats (was 8.13..11.56), generation path 2.25 (was 3.64). Still
open in the code: hagi/unified.py:1010 @bab8aff reads `[::-1]` with
`logits(x)[0]`.

**Certified warm-up, simulated.** Bench mode `certified-warmup-sim`
(scripts/bench_bridge.py) compares a certified arm (python twin of
`_certified_finite_step`, COMMIT iff drop > 1e-12, ≤ 600 steps) with the
plain Adam arm on the bench carrier with the trunk frozen — a simulation,
not a consumer run.

| corpus | fOld | certified | plain Adam (steps) | verdict |
|---|---|---|---|---|
| snapshot (34 pts, T=2, n_params=66) | 3.761650 | 2.783855 (600 COMMIT, 0 HOLD, 0 halvings, sum_drop 0.561600) | 3.583951 (2) | PASS |
| live corpus (T=2, n_params=102) | 4.811144 | 3.394217 (600 COMMIT, 0 HOLD, 0 halvings, sum_drop 0.780696) | 4.444299 (4) | PASS |

Does not claim: plain Adam ALSO lowered the objective — without a
certificate; the certificate is a batch mean over all points, not a task
mean (pin 34).

### 4.7 Benchmarks (measured only)

**mini-HAGI.** 3 tasks, 2-block trunk, 2 grow phases, holdout. Full
pipeline (A-trunk2 → C-gpm1 → E-gpm2relax → F-quant → G-stop): 15
certified steps; objective chain monotone; gpm2 phase: full-GPM arm 0
committed / 4 honest HOLDs vs relaxed arm 4 committed (k = 1, eps = 1/10);
zero forgetting in the full-GPM arm; relaxed-arm forgetting ≤ bound at
every step.

**vs-trainer certified forecasts.** 31 measured points (25 train / 6
holdout); 8 committed training steps; 6/6 holdout predictions certified
(disjoint bands); accuracy 4/6 (bounded by the model, not the certificate
— certified midpoints agree with the true softmax argmax 6/6, pin 6).

**From proxies to formulas.** Each operating parameter is a formula with
a Lean anchor, a bench application and measured bits.

| Parameter | Certified formula | Lean anchor | Measured effect |
|---|---|---|---|
| snap grid | `k* = ⌈log₂(L·d/ε)⌉−1` | `snap_k_eq_ceil`, `Hagi/Theory/GrowSnap.lean:342` | auto-k* in 4 snap modes (k*=18/19/20; trunk-freeze k*=11); 2788 bits saved vs legacy k=40 over 33 snap events |
| transfer gate | warm ⟺ `start_gap = f(θA) − f(0) ≤ n•nlBudget γ L G` (`certified_transfer_gate` ← `sufficient_negative_transfer`; `nlBudget = γG² + Lγ²G²/2`) | `nlBudget`, `Hagi/Theory/NegativeTransfer.lean:242` | exact boundary nlBudget(1/5, 2, 2) = 24/25; gap 24/25 → warm, 25/25 → cold-certified; 3 pairs warm, forgetA = 0 |
| window span | `s = min(w, ⌈(n−w)/(m−2)⌉)` | `covStartsStep_adaptive_covers`, `Hagi/Theory/CoverageReading.lean:233` | w=m=64: n=540 → s=8, 61 windows; n=4032 → s=64 (boundary); n≥4160 → honest INFEASIBLE (None) instead of silent truncation |
| step size | `γ* = 1/L`, `nlDrop (1/L) L G = G²/(2L)` | `nl_drop_optimal`, `Hagi/Theory/NegativeTransfer.lean:481` | auto-LR = 1/(2·trace H̄): γ_auto = 0.477 / 0.520 / 0.667 (exact Fractions) vs old 1/10; verdicts bit-identical |
| window layout | `B = w(m−1)`, `s = w` ⇒ `(B−w)/s+2 = m`; peak ≤ m | `hier_peak_window_budget`, `Hagi/Theory/CoverageReading.lean:314` | n=100000: 25 blocks, 24×63+51, total 1563, peak 63; single-level n=8128 needs 127 > 64 (INFEASIBLE), hier [63,63,1] peak 63 |
| window width rule | fixed: w = w_max; linear: corridor [c·n, c·(n+w)); mixed α=2: w* = √(a/c), lower ⌈n/w⌉·(a+c·w²) ≥ 2n·√(a·c) | `windowCost_fixed_mono`/`windowCost_linear_near_const`/`mixedCost_relax_min(_eq)`/`mixedCost_lower`, `Hagi/Theory/CoverageReading.lean:575`/:602/:630/:650/:675 | n=100000, w∈{16,64,256}: reads 6250/1563/391; linear totals 100000/100032/100096; fixed optimum w=256 → 391 reads |

Two structural remarks. The optimal-step clause is self-contained:
`φ(1/L) − φ(γ) = (G²/(2L))·(1 − Lγ)² ≥ 0` is a complete square
(`nlDrop_le_optimal`, Hagi/Theory/NegativeTransfer.lean:467), so γ* = 1/L is the
global maximizer of the guaranteed drop on all of ℝ — not merely on
[0, 2/L]. The hierarchy is exact, not heuristic: with `s = w`,
`B = w·(m−1)` the per-block budget `(B−w)/s + 2` EQUALS m, so the same
peak-m streaming budget that bounded the single level at n ≤ w(m−1) =
4032 (w=m=64) now covers ANY n — the witness n=8128 lands [63, 63, 1]
with peak 63 in both Lean and the bench twin (`HierEval.lean` #eval).

**Coverage iff.** `covStartsStep_covers` (Hagi/Theory/CoverageReading.lean:184) is
exact: windows of width w with step s cover `[0, n)` IFF `s ≤ w` —
necessity by the witness s=17 > w=9 leaving byte 9 in a hole; the adaptive
budget form keeps windows ≤ m (`covStartsStep_len_le`, :220). The
negative twin: truncation loses byte 0 (`covStarts_trunc_uncovered_zero`,
Hagi/Theory/CoverageReading.lean:130).

**Certified capacity gate.** `growthGate pb c = decide (c < pb)`: grow ⟺
c < pb. If `n·G²/(2L) ≤ c`, then `f z − f (nlRun n (1/L) grad z) ≤ c`
(`growth_gate_sound`): when even n optimal steps cannot pay for the added
capacity, growth cannot pay back. The stay branch is certified; the grow
branch is only a permission.

**Corpus policy.** The live corpus drifts, so the bench (i) skip-warns
records with `ce: null`, (ii) pins the default corpus to a 35-key snapshot
(live 45-key and 41-key corpora ABORT on the same bound — a data
property), (iii) falls back in three levels with `--snapshot-corpus`
fail-closed (exit 3) and `--live-corpus` opt-in. Result: bench tables are
deterministic by default and every deviation is a telemetered decision.

**The PALOMAR niche.** PALOMAR (palomar-registry.org) is a registry of
formally verified results. A direct API check
(`data.palomar-registry.org/api/v1/results`) against the statements of
the cards returned ZERO thematic entries at every checked revision (1293
results / 983 projects at the first check; 1331 / 1011 at the last). As
measured: the niche was empty at the checked revisions; uploading is a
user-side step. The nineteen cards are in docs/PALOMAR-CARDS.md.

Cards 9–13 restate the optimal step size, hierarchical coverage, the
adaptive-span iff, the reading floor and the linear window cost of
§4.4 and §4.7, with the extra anchors `nl_drop_bound` (:443), `nlDrop`
(:434), `nlStep` (Hagi/Theory/NegativeTransfer.lean:231);
`hier_total_formula` (Hagi/Theory/CoverageReading.lean:440),
`hier_blocks_sum_tiling` (:389), `covStartsStep_len_tiling` (:354).

**First external consumer.** The consumer's runtime synchronized its
theory state with this repository: the bridge that exports the certified
constants went from an unused artifact to a live dependency. This is an
existence proof of external synchronization, not an evaluation of
downstream benefit (pin 17).

## 5. Limitations and open premises

Each limit is stated once.

1. **Measurement premise.** Certified prediction is conditional on
   `BandDescribes z lo hi` — a MEASUREMENT premise
   (`Hagi/Theory/TrainerBenchmark.lean:60`), not derived from the model.
2. **ε-tolerances are measured, not tuned.** eps = 1/10 in mini-HAGI is a
   PIN: eps = 1/100 is impossible at any k < rank (tail² budget fails).
   The ε in the cycle theorem is a premise-channel allowance.
3. **Scale.** mini-HAGI: 3 tasks, small d; vs-trainer: 31 points. No
   large-scale claims.
4. **Premise-form channels.** falseCommit bounds are premise-form with
   cited discharge routes; in general they assume honest reporting of the
   measurement layer.
5. **Telemetry is runtime-asserted, not Lean-IO.** "Machine checked"
   refers to Lean proofs; the live-loop telemetry is checked by per-step
   Python asserts against the theorem bounds (exit 0), a strictly weaker
   guarantee.
6. **Prediction accuracy is a model property** (§4.7).
7. **Hybrid degeneration.** On the measured snapshot the hybrid selector
   saw 0/24 conflicts and degenerated to the free A-GEM policy (forgetA
   −0.3831); selector branches other than agemFree are covered by probe +
   Lean theorem but not by live telemetry. rank(A∪B)=4=dim makes the
   full-GPM branch unreachable live.
8. **Corpus drift.** The live `unified_ledger` corpus drifts between runs
   (46 → 51 → 53 points; 113 → 115). Cross-run numeric comparisons use
   each run's own measurements; objective values and coverage ratios
   (106/113 vs 108/115) are not comparable across corpus versions.
9. **EB contrast is data-dependent.** The live full-loop corpus shows an
   EB-vs-Hoeffding sample contrast of only 1.12× (n_EB 9649 ≤ n_Hoeffding
   10851) against the 27.49× calibration point — a property of the data,
   not of the bound form.
10. **Polar-Express upper end.** The certified final spectral box is
    [9/512, 1049/1024]: the upper end exceeds 1 by 2.4%.
11. **OE completeness is probe-relative** (§4.3).
12. **Synthetic laws do not transfer.** The layered laws cover 0/113
    positions of the real full-corpus targets; §4.3's compositional chain
    demonstrates the mechanism, not a claim about the live corpus.
13. **Live-corpus coverage is constant clusters only** (§4.3).
14. **EB-stop before budget.** The certified stop fired as designed, but
    on data this weak it may fire before any non-constant structure is
    found — the stopping rule is data-limited, not budget-limited.
15. **The corpus is live and growing** (see 8).
16. **The EB-stop did not fire in the v3 assembly.** Every iteration
    committed (drop > 0), so the actual stop was the budget MAX_ITER = 6.
17. **External consumer is a synchronization event, not a result.**
18. **Adaptive-span INFEASIBLE boundary.** Full coverage within a window
    budget m is IMPOSSIBLE in principle for n > w + (m−2)·w ≈ 4032 at
    w = m = 64 (`covStartsStep_adaptive_covers` premise); covering longer
    inputs needs a hierarchical scheme.
19. **The smooth transfer gate is conservative, not exact.** On a measured
    adversarial pair the quad-iff (clause 5) correctly certifies cold
    while the smooth gate (clause 8) says warm: the measured gradient
    bound G ≈ 0.03 makes the sufficient budget 99.66 exceed the start_gap
    5.43 — sufficiency, not iff. The G premise is measured over the
    realized trajectory.
20. **Open premises are counted, not hidden.** STILL-EXTERNAL: 46 registry
    premises (31 empirical + 14 model + 1 mathematical) + 11 operational
    + 11 unprefixed; full budget 106 h_emp-binders over 36 files;
    PROVEN-NOW 1 (h_emp_var), PARTIAL 2 (h_emp_fiber, h_emp_dist), DEAD 0
    (docs/PREMISES-STATUS.md).
21. **Bench corpus drift.** The live unified_ledger was pruned 185 →
    11-12 keys; 22 of 35 bench modes ABORT (exit 3, corpus-drift) rather
    than fabricate guarantees on a starved corpus.
22. **Code bridges are pinned to a sha, and the code drifts.** Every code
    anchor of §2.2 is `file:line@sha`. At HAGI_v2 HEAD b3740e0 the lines
    moved (`_certified_finite_step` lm.py:826 → :831, refine loop :999 →
    :1007, `MAX_BLOCKS` 2 → 4, warm-up lr 3e-3 → 1e-3); the Надя.txt
    anchors are a 2026-11-24 snapshot, not a git sha. The tree was
    read-only for primes.
23. **The real certificate is the range branch.** On the test config the
    adaptive branch of `_adaptive_step` is never taken (eta* ≈ 203–260 >
    1); `ce_adaptive_code_drop` is a bridge to a branch the code does not
    exercise on that config, and its window (1e-5, 50] is a real
    hypothesis.
24. **Tangent vs exact displacement.** The code builds the CE majorizer
    on a JVP; the theorem is about the exact logits. The bridge is about
    the certificate, the rollback is about the residual, and the residual
    is not bounded.
25. **Warm-up is not certified in the code.** h1 of `warmup_safe` is a
    hypothesis: the warm-up of `_maybe_grow` is bare Adam
    (unified.py:423-433 @ca52eb4). The certified-step contract
    (`CertifiedFiniteStep`, lm.py:826) writes to the trunk, not to the
    block. Closing this is an EXTERNAL push
    (docs/PROPOSAL-certified-warmup.md; numbers not measured).
26. **Backtracking is not Armijo.** The predicate has no
    sufficient-decrease term; `backtrack_accept_drop` is a bridge to the
    code's own accept test, called only from the self-test. "Adam EMA
    descent" ⟨g, m̂/√v̂⟩ ≤ 0 is NOT a code fact; `adam_inner_nonneg` is
    unproved and not included. ⟨g, d⟩ > 0 holds only at t = 1; from t = 2
    Adam is not a certified descent — the lemma is false as stated.
27. **Block-only JVP is implementation.** `certified_step_block_of_range`
    is carrier-free because the range lemma is about logits; the range of
    Δz over the block parameters with a frozen trunk must be computed by
   the code, which has no functional block logits. Given that range R and
   a descent signal a < 0, the useful step is η* = 4|a|/R² with drop
   2a²/R².
28. **iid batch and independent rounds are models, not code facts.** The
    code samples without replacement and updates θ between the 8 rounds,
    so the rounds are dependent; `certified_rounds_union` is conditional
    on the product model `roundP`. WOR conservativity (FCP ≤ 1) is not
    formalized — Mathlib has no lemma. The code computes neither b/sig
    nor the per-round level α/k.
29. **Holdout gates are measured.** Both the keep-iff-holdout gate of the
    growth path and the `wb − wa > total_bound` test of the controller
    compare measured holdout values; no theorem relates train obj to
    holdout CE. The "forgetting 4× lower" of the consumer is an A/B on 6
    chunks from one checkpoint, not a theorem.
30. **U2: global reachability of a useful block is open.**
    `useful_first_step` proves the LOCAL statement (η* = 4|a|/R²,
    drop_max = 2a²/R²) under a < 0. "An expressive block can reach a drop
    ≥ δ in many steps" needs an optimization guarantee on a non-convex
    landscape plus a UAT on a finite grid; primes has neither (no UAT
    statement at all), and the code's random W1 gives a ≠ 0 only
    probabilistically.
31. **The descent signal a < 0 is a hypothesis** (§4.6).
32. **Without-replacement conservativity is not formalized.** The finite-
    population factor (N−n)/(N−1) ≤ 1 is intuition only; the price is an
    order-statistics/FCP lemma.
33. **The range-coder round-trip is tests, not a theorem.** archiver.py
    has no Lean model (a nonempty-interval invariant, a searchsorted lemma
    and a renorm invariant; est. ≥ 400 lines). `trit_roundtrip` is a
    positional pack. "Within o(1) of −log₂ P" for the range coder is a
    classical fact, not proved here. Lossless = 11/11 measured + 6 tests.
34. **The certified warm-up is a simulation** (§4.6).

Open experiment plan: scale mini-HAGI (tasks 3 → 8+, deeper trunk);
vs-trainer with a larger holdout (6 → 50+) exercising the nm-doubling
path; exercise ROLLBACK on an injected premise violation; measure κ
tightness (e^R/κ(R)) end to end on the live loop; independent
re-verification (fresh checkout, axiom check, external statement audit);
SVD upstream landing (docs/UPSTREAM-SVD.md).

## Appendix A: anchor table

Anchors not already cited in the body. Line numbers are re-anchored
centrally.

| Anchor | File:line |
|---|---|
| kappa_le_expR | Hagi/Theory/AdaptiveMajorizer.lean:309 |
| grow_snap_cycle_sound | Hagi/Theory/GrowSnap.lean:145 |
| adapter_neutral_B | Hagi/Theory/AdapterGrowth.lean:101 |
| adapter_snap_cycle_sound | Hagi/Theory/AdapterGrowth.lean:281 |
| rank_select_sound | Hagi/Theory/AdapterGrowth.lean:326 |
| adapter_stack_rank_bound | Hagi/Theory/AdapterGrowth.lean:414 |
| adapter_merge_params | Hagi/Theory/AdapterGrowth.lean:441 |
| adapter_merge_error_bound | Hagi/Theory/AdapterGrowth.lean:455 |
| naive_decay_leak | Hagi/Theory/WeightDecayLeak.lean:126 |
| wd_gpm_step_sound | Hagi/Theory/WeightDecayLeak.lean:157 |
| empirical_bernstein_bound | Hagi/Probability/EmpiricalBernstein.lean:208 |
| oe_search_complete | Hagi/Theory/OEComplete.lean:80 |
| ce_total_eq_residual | Hagi/Theory/ExactBypass.lean:90 |
| exact_gate_sound | Hagi/Theory/ExactBypass.lean:97 |
| adapter_isolation_zero_forgetting | Hagi/Theory/AdapterGrowth.lean:564 |
| trunk_update_needs_projection | Hagi/Theory/AdapterGrowth.lean:614 |
| IterState | Hagi/Theory/MiniHagiLoop.lean:117 |
| iterStep | Hagi/Theory/MiniHagiLoop.lean:122 |
| coversPrim | Hagi/Theory/MiniHagiLoop.lean:128 |
| coverage_append_monotone | Hagi/Theory/MiniHagiLoop.lean:134 |
| selfCompressParams | Hagi/Theory/AdapterGrowth.lean:691 |
| self_compress_params_bounded | Hagi/Theory/AdapterGrowth.lean:696 |
| self_compress_params_contrast | Hagi/Theory/AdapterGrowth.lean:706 |
| distillAdapter | Hagi/Theory/AdapterGrowth.lean:773 |
| distill_prob_one | Hagi/Theory/AdapterGrowth.lean:803 |
| distill_coverage_preserved | Hagi/Theory/AdapterGrowth.lean:819 |
| distill_param_count | Hagi/Theory/AdapterGrowth.lean:832 |
| distill_params_total | Hagi/Theory/AdapterGrowth.lean:839 |
| symbolic_storage_cheaper | Hagi/Theory/AdapterGrowth.lean:848 |
| fact_append_preserves | Hagi/Theory/FactLedger.lean:59 |
| fact_lookup_monotone | Hagi/Theory/FactLedger.lean:67 |
| rangeWrap_inrange | Hagi/Theory/RangeWrap.lean:43 |
| rangeWrap_fixed_point | Hagi/Theory/RangeWrap.lean:53 |
| selectW_spec | Hagi/Theory/AdaptiveContext.lean:51 |
| selectW_occam_minimal | Hagi/Theory/AdaptiveContext.lean:73 |
| selectW_budget_bound | Hagi/Theory/AdaptiveContext.lean:101 |
| consolidate_prompt_empty | Hagi/Theory/KnowledgeConsolidation.lean:66 |
| remember_preserves_pages | Hagi/Theory/KnowledgeConsolidation.lean:72 |
| learn_from_dialog_archives | Hagi/Theory/KnowledgeConsolidation.lean:79 |
| covStarts_trunc_uncovered_zero | Hagi/Theory/CoverageReading.lean:130 |
| covStartsStep_adaptive_covers | Hagi/Theory/CoverageReading.lean:233 |
| hagi_master_v31 | Hagi/Theory/MasterTheoremV3.lean:128 |
| nlBudget | Hagi/Theory/NegativeTransfer.lean:242 |
| covStartsStep_len_le | Hagi/Theory/CoverageReading.lean:220 |
| hagi_master_v32 | Hagi/Theory/MasterTheoremV3.lean:187 |
| nlStep | Hagi/Theory/NegativeTransfer.lean:231 |
| nlDrop | Hagi/Theory/NegativeTransfer.lean:434 |
| nl_drop_bound | Hagi/Theory/NegativeTransfer.lean:443 |
| nlDrop_le_optimal | Hagi/Theory/NegativeTransfer.lean:467 |
| hierBlockLen | Hagi/Theory/CoverageReading.lean:268 |
| hierStarts | Hagi/Theory/CoverageReading.lean:273 |
| hier_peak_window_budget | Hagi/Theory/CoverageReading.lean:314 |
| adaptive_claim_scaled_bounds | Hagi/Theory/AdaptiveMajorizer.lean:1437 |
| batchGradientMinimizer_eq_mgdaCodeDirection_of_stationary | Hagi/Model/BatchCEDescentMgdaCode.lean:146 |
| warmup_safe | Hagi/Theory/FunctionPreservingGrowth.lean:302 |
| backtrack_accept_drop | Hagi/Theory/RollbackGate.lean:261 |
| warmup_h1_of_certified_steps | Hagi/Theory/FunctionPreservingGrowth.lean:408 |
| batch_drop_not_global | Hagi/Theory/FunctionPreservingGrowth.lean:463 |
| certified_step_block_of_range | Hagi/Theory/FunctionPreservingGrowth.lean:490 |
| certified_batch_drop_global | Hagi/Contracts/BatchGlobalTelescope.lean:178 |
| rounds_union | Hagi/Contracts/BatchGlobalTelescope.lean:300 |
| RepairRun | Hagi/Theory/RepairForgetting.lean:61 |
| acceptedCount | Hagi/Theory/RepairForgetting.lean:69 |
| repair_drop_bound | Hagi/Theory/RepairForgetting.lean:78 |
| accepted_le_budget | Hagi/Theory/RepairForgetting.lean:93 |
| slot | Hagi/Theory/CoverageReading.lean:707 |
| slotRev | Hagi/Theory/CoverageReading.lean:712 |
| slotRev_first | Hagi/Theory/CoverageReading.lean:732 |
| slot_mono | Hagi/Theory/CoverageReading.lean:716 |
| slotRev_last | Hagi/Theory/CoverageReading.lean:726 |
| codelength_ge_entropy_of_uniquelyDecodable | Hagi/Theory/ArchiverCodeLength.lean:106 |
| idealLen_kraft | Hagi/Theory/ArchiverCodeLength.lean:150 |
| idealLen_ge_entropy | Hagi/Theory/ArchiverCodeLength.lean:157 |
| idealLen_le_ce_add_one | Hagi/Theory/ArchiverCodeLength.lean:164 |
| ceBits_eq_entBits_add_kl | Hagi/Theory/ArchiverCodeLength.lean:194 |
| idealLen_self_bounds | Hagi/Theory/ArchiverCodeLength.lean:208 |
| ema_one_unbiased | Hagi/Step/AdamDirection.lean:67 |
| adam_first_step_dot_nonneg | Hagi/Step/AdamDirection.lean:74 |
| adam_coord_sign_flip_neg | Hagi/Step/AdamDirection.lean:106 |
| adam_step_not_always_descent | Hagi/Step/AdamDirection.lean:116 |
| ema_sign_flip_negative | Hagi/Step/AdamDirection.lean:125 |
| linDrop | Hagi/Theory/FunctionPreservingGrowth.lean:578 |
| useful_first_step_pos | Hagi/Theory/FunctionPreservingGrowth.lean:589 |
| useful_eta_le | Hagi/Theory/FunctionPreservingGrowth.lean:596 |
| exists_useful_eta | Hagi/Theory/FunctionPreservingGrowth.lean:619 |
| no_signal_no_drop | Hagi/Theory/FunctionPreservingGrowth.lean:628 |
| first_step_useful_certified | Hagi/Theory/FunctionPreservingGrowth.lean:640 |
| identityBlock | Hagi/Theory/FunctionPreservingGrowth.lean:136 |
| trunk_function_preserving | Hagi/Theory/FunctionPreservingGrowth.lean:165 |
| lmLogits_grow_identity | Hagi/Theory/FunctionPreservingGrowth.lean:175 |
| warmup_telescope | Hagi/Theory/FunctionPreservingGrowth.lean:287 |
| warmup_strict | Hagi/Theory/FunctionPreservingGrowth.lean:317 |
| uncertified_step_can_worsen | Hagi/Theory/FunctionPreservingGrowth.lean:334 |
| block_step_certified_of_range_bound | Hagi/Theory/FunctionPreservingGrowth.lean:506 |
| block_step_commit_of_range_bound | Hagi/Theory/FunctionPreservingGrowth.lean:520 |
| block_range_bound_violated_not_certified | Hagi/Theory/FunctionPreservingGrowth.lean:535 |
| hagi_master_v33 | Hagi/Theory/MasterTheoremV3.lean:252 |
| useful_of_adam_first | Hagi/Theory/FunctionPreservingGrowth.lean:744 |
| padSlot | Hagi/Theory/CoverageReading.lean:741 |
| padSlot_tail | Hagi/Theory/CoverageReading.lean:746 |
| padSlot_last | Hagi/Theory/CoverageReading.lean:754 |
| padSlot_full | Hagi/Theory/CoverageReading.lean:763 |
| mgda_norm_sq_le_of_stationary | Hagi/Model/BatchCEDescentMgdaCode.lean:102 |
