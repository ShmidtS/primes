# PROPOSAL index — HAGI_v2 port packages from primes

Twelve self-contained proposals for the HAGI_v2 implementation
agent. Each cites Lean anchors proved and frozen in primes
(anchors to re-verify before port), a minimal Python diff, sanity numbers, a validation
criterion, and limits. Proposals are mutually independent —
apply in any order.

| # | Document | Status | One-liner |
|---|----------|--------|-----------|
| 2 | [PROPOSAL-tight-kappa.md](PROPOSAL-tight-kappa.md) | Proposed | Tight Bennett κ(R)=(e^R−1−R)/R² curvature for the CE adaptive step: 2.77×/3.79×/6.73× larger certified drops at R=0.5/1/2, weaker dominance premise. |
| 3 | [PROPOSAL-fisher-quant.md](PROPOSAL-fisher-quant.md) | Proposed | Curvature (Fisher/Gershgorin) per-coordinate quantization budgets for the ternary jump and self-edit weight prune: quadratic ΔL ≤ Σ\|g\|ε + ½Σcε², allocation monotone in curvature. |
| 4 | [PROPOSAL-joint-step.md](PROPOSAL-joint-step.md) | Proposed | Simultaneous trunk+head certified step CE ≤ −2A²/R² + 2·HL·dd with measured trunk displacement; strict-commit criterion and the joint-vs-alternating window. |
| 5 | [PROPOSAL-merge-meas.md](PROPOSAL-merge-meas.md) | Proposed | Measured (δ-gated) expert merge for MDL-prune: linResidualGrid on a rational t-grid replaces the δ-free quadratic gate; negative theorem pins why measurement is mandatory. |
| 6 | [PROPOSAL-external-plan.md](PROPOSAL-external-plan.md) | Proposed | The external optimization plan top-4 ported: projected weight decay (leak factor (1−ηλ) exact), Empirical-Bernstein validation radius (27.49× samples), OE hash-consing prune completeness (relative to probes), PROVEN_EXACT bypass with CE = 0 on covered positions (gate rejects p = 0). |
| 7 | [PROPOSAL-certified-warmup.md](PROPOSAL-certified-warmup.md) | Theory implemented in primes; code-side pending in HAGI_v2 | Warm-up of a grown block via the `_certified_finite_step` mechanism (COMMIT iff drop > 1e-12, else exact-rollback HOLD) on ONE fixed objective instead of plain Adam: closes the h1 premise of `warmup_safe`, so train-objective ≤ fOld becomes certified for any holdout-gate verdict; cost = one forward per trial; per-batch drops still do not telescope (negative theorem). |
| 8 | [PROPOSAL-holdout-size.md](PROPOSAL-holdout-size.md) | Theory implemented in primes; code-side pending in HAGI_v2 | Holdout slice size for a non-trivial growth-gate certificate: k ≥ ln(2N/δ)/(2(ε/B)²); at ε=0.05B, δ=0.05 → k ≥ 1199 (N=10) / 877 (N=2) vs ≤512 in code (2ε ≈ 0.13–0.15B); holdout ≥ 1200 windows or fewer checkpoint peeks. |
| 9 | [PROPOSAL-muon-guards.md](PROPOSAL-muon-guards.md) | Theory implemented in primes; code-side pending in HAGI_v2 | Changed algorithm: NO — guards and telemetry for the Muon step on the growth-block layer W1: skip if ‖G‖_F ≤ eps, warn if σ_max(X₃) > 1+1e-6, accept the step only if the loss decreases on a small batch (operational ∃η), log ⟨G,X₃⟩/‖X₃‖_F and ‖G‖₁/√(mn). |
| 10 | [DERIVED-CONFIG.md](DERIVED-CONFIG.md) | Proposed (derivation only) | Every training parameter is DERIVED (formula + number) or HONEST-GAP; code gaps: cosine floor 3/20 vs eta_min = 0, LCB probe and holdout below derived sizes, growth L is the CE value, not a Lipschitz constant. Script `scripts/derive_config.py`. |
| 11 | [PROPOSAL-smoothness-logging.md](PROPOSAL-smoothness-logging.md) | Theory implemented in primes; code-side pending in HAGI_v2 | Changed algorithm: NO, guards: NO — two telemetry values (`‖wo‖_F²` per block, `max_t ‖x t‖₂²` and `Σ_t ‖x t‖₂²` per batch) turn the proved smoothness `S_batch = ‖wo‖_F²·Σ_t‖x t‖₂²` of the W1 layer into a number: log `S_batch`, `gamma_star = 1/S_batch`, `gamma_star_mean = B/S_batch` next to the Adam lr; optional warn if `lr > 2/S_mean` (outside the proved descent zone `γ ≤ 2/L`). |
| 12 | [PROPOSAL-ef21-adaptive-scale.md](PROPOSAL-ef21-adaptive-scale.md) | EF21Scale | Theory implemented in primes; code-side pending in HAGI_v2 | Changed algorithm: YES (one line) — ternary EF21 scale `s = ‖m‖_∞/2` per step instead of frozen `0.2·max|m|`: a frozen scale zeroes the direction when `‖m‖_∞ < s/2` (every step rejected), the adaptive one keeps alignment ≥ `‖m‖_∞‖m‖₁/2 − n‖m‖_∞²/8`. |

Numbering keeps the historical ids: #1 (the weaker e^R majorizer,
replaced coefficient-for-coefficient by #2) is removed, and the
remaining numbers are cited from STATUS.md and DERIVED-CONFIG.md.

Statuses: Proposed = ready for the HAGI_v2 agent, pending its port +
validation (`real ≥ certified` every step) as specified per document;
«Theory implemented in primes» = the Lean side is done, the
code-side port is pending.
| 13 | [PROPOSAL-paired-gain-eb.md](PROPOSAL-paired-gain-eb.md) | PairedGain | **ACCEPTED — HAGI_v2 414ede5**: both `paired_gain` call sites now use `paired_margin_eb(d, n_states, delta = 0.01)` (adapters: `n_states = len(cands)`; certificate = `admit_false_union_le`) | Priority: 2 (two one-line call swaps, strict guarantee) — Changed algorithm: YES (one function) — paired-gain lower bound `mean − 2.4·SE` becomes `mean − r_EB` with `r_EB = √(2σ̂²L/n) + 2bL/n`, clipped `b = 2`: `admit_false_le_shifted` gives `P[false admit] ≤ α` for any n and any null `μ ≤ g₀`; the normal heuristic has no finite-sample guarantee |
| 14 | [PROPOSAL-lazy-second-moment.md](PROPOSAL-lazy-second-moment.md) | LazyAdam | Theory implemented in primes; code-side pending in HAGI_v2 | Priority: 3 (subsumed by 15 for tables; keep if Adam stays) — Changed algorithm: YES (two lines) — dense `v_v.mul_(b2)` decays rare byte rows to `v → 0`; `touchStep_dense_mono`: the touch step grows with staleness up to `lr/ε` (`touchStep_le_eps`); the lazy rule `v_d = v₀` keeps it constant and dominates after bias correction (`vh_lazy_ge_dense`) |
| 15 | [PROPOSAL-snr-table-lr.md](PROPOSAL-snr-table-lr.md) | AdamSNR | Theory implemented in primes; code-side pending in HAGI_v2 | Priority: 1 (largest memory saving; needs per-domain SNR warmup — see applicability boundary, AdaShift/Adam-Rel) — Changed algorithm: YES (table optimizer) — stationary Adam factor = `(μ/σ)/√(1+(μ/σ)²)` (`adamFactor_eq_snr_scale`), saturating (`adamFactor_abs_le_one`); the clipped g-SNR rate `lr·min(SNR,1)` is within `1/√2` of Adam for every SNR and drops `v_m`/`v_v` on byte tables (one third of the optimizer state) |
| 16 | [PROPOSAL-adam-rel-reset.md](PROPOSAL-adam-rel-reset.md) | AdamRel | Theory implemented in primes; already implemented in HAGI_v2 (fresh optimizer per `train_optimal`) | Changed algorithm: NO (certificate + regression guard) — reset `step_count` and Adam moments at the start of each new domain: the global timestep leaves `v̂` at the previous domain's scale and oversizes the step by `s/√v₀` (`rel_vhat_ge_global`); after the reset `v̂ = s²` exactly on the first step (`rel_reset_exact`) |
| 17 | [PROPOSAL-val-windows-step.md](PROPOSAL-val-windows-step.md) | ValWindows | Theory implemented in primes; code-side pending in HAGI_v2 | Priority: 2 (one expression) — Changed algorithm: YES — window step `max(k, n // 256)` instead of `max(1, n // 256)`: adjacent windows share bytes iff `k > step` (`adjacent_disjoint_iff`), so for domains shorter than `256·k` bytes the EB gate runs on dependent differences (`indep_threshold`); the radius then grows honestly with fewer windows (`radius_anti`) |
| 18 | [PROPOSAL-repair-share-minimax.md](PROPOSAL-repair-share-minimax.md) | RepairShare | **REVERTED — HAGI_v2 cc1bdd1** (accepted in 1e707ce, reverted without a stated cause; theory stands, re-approval needs the code agent's measurement) | Priority: 3 (needs calibration `c`) — Changed algorithm: YES — repair byte share `∝ √Δ` is not minimax (`sqrt_share_not_minimax`: Δ = 4, 1 gives unequal residuals); equalise residuals `Δ_i(1 − c√x_i)` by water-filling, matching the worst-domain gate |
| 19 | [PROPOSAL-adaptive-ingest-epochs.md](PROPOSAL-adaptive-ingest-epochs.md) | EpochTradeoff | Theory implemented in primes; code-side pending in HAGI_v2 | Priority: 3 — Changed algorithm: YES — fixed CYCLE_EPOCHS = 4 → per-ingest stop at lam·R₀·ρ·(1−ρ)^E ≤ c₁ (stop_condition); c₁ = 137 s, ρ ≈ 0.27 from ec80163 |
| 20 | [PROPOSAL-gate-precheck-windows.md](PROPOSAL-gate-precheck-windows.md) | PairedGain | Theory implemented in primes; code-side pending in HAGI_v2 | Priority: 2 (compute only) — Changed algorithm: YES (pre-gate) — skip building the EB gate when n_windows < N(ε) = max(⌈8σL/ε²⌉+1, ⌈4bL/ε⌉+1) (radius_eventually_le + n_suffices); acceptance rule untouched |
| 21 | [PROPOSAL-delta-budget.md](PROPOSAL-delta-budget.md) | PairedGain | Theory implemented in primes; code-side pending in HAGI_v2 | Priority: 2 (certificate void after 100 checks as is) — Changed algorithm: YES (delta scaling) — delta = δ₀/M per check on the current holdout gives total ≤ δ₀ (delta_budget_scaled); reset on holdout change |
| 22 | [PROPOSAL-residual-masking.md](PROPOSAL-residual-masking.md) | ResidualMasking, MirrorHedgeMWU | **IN HAGI_v2 WORKING TREE (uncommitted)**: bypass_mask (residual masking) implemented; importance draw q ∝ |ℓ_b| still pending | Priority: 1 — Changed algorithm: YES — zero gradients on ExactBypass-covered positions (identity, gradCE_zero_of_onehot) and draw windows with q ∝ |ℓ_b| (selectedLoss_optimalPropensity_mse); both missing from train_optimal |
| 23 | [PROPOSAL-archiver-mixture.md](PROPOSAL-archiver-mixture.md) | MixtureCoding | Theory implemented in primes; code-side pending in HAGI_v2 | Priority: 2 — Changed algorithm: YES — arithmetic coder on a Hedge mixture (model + PPM-3 + zlib); bpb ≤ best expert + log₂K + regret (mixCE_le_best_regret, hedge_negLogW_le); fixes archiver.py losing 25% to zlib |
| 24 | [PROPOSAL-state-carry.md](PROPOSAL-state-carry.md) | GDNBridge | Certificate implemented in primes; code in HAGI_v2 working tree (uncommitted) | Priority: 1 (commit + regression test) — Changed algorithm: already in working tree — forward exact across chunks (gdnScan_append), wrap must zero the state (carry_without_wrap_leaks); backward truncated (TBPTT, honest boundary) |
| 25 | [PROPOSAL-gauge-balance.md](PROPOSAL-gauge-balance.md) | GaugeBalance | **ACCEPTED BUT UNWIRED — HAGI_v2 0affafb** defines `gauge_balance` (SwiGLU + BigramSkip; MLA not yet) but nothing calls it; 25b asks for the export-time call + test | Priority: 2 — Changed algorithm: YES — exact gauge balance of every rank-1 factor and SwiGLU neuron before quantization (rank1_gauge identity; stock_balance_attained: c = sqrt(|b|/|a|) minimises squared norms); arXiv:2611.27889v1 |
| 26 | [PROPOSAL-worst-domain-gate.md](PROPOSAL-worst-domain-gate.md) | TailGate | **ACCEPTED — HAGI_v2 5a773e6** (`HAGI_WORST_GATE` default on); RareDecay guard test `2a34515` | Priority: 1 — Changed algorithm: YES — worst-domain rollback gate on by default (max_le_imp_mean_le: strictly stronger than the mean gate; mean_le_not_imp_max_le: the mean gate admits single-domain collapse); addendum to 25: MLA factor in gauge_balance |
| 27 | [PROPOSAL-asymmetric-grow-init.md](PROPOSAL-asymmetric-grow-init.md) | GaugeBalance | Theory in primes; code-side pending (grow_depth W_down = zeros) | Priority: 2 — Changed algorithm: YES — W_down = ε·sign-noise, W_up = zeros: identity kept at step 0, ∂L/∂W_up = −ε·x·y ≠ 0 from the first step (pairGrad_u_zero_at_d0 / pairGrad_u_at_eps; Lu–Shin–Su 2020); ready-made test attached |
| 28 | [PROPOSAL-importance-token-loss.md](PROPOSAL-importance-token-loss.md) | ResidualMasking | Theory in primes; code-side pending (optimal_lm.py:637 uniform CE) | Priority: 1 — Changed algorithm: YES — token loss with q ∝ |ℓ_b|, capped at 1 (Bernoulli): unbiased (masked_importance_unbiased), covered positions get ~0 propensity (covered_propensity_le), subsumes the masking path; ~30 % backward saving at equal gradient quality |
| 29 | [PROPOSAL-mixed-precision-rows.md](PROPOSAL-mixed-precision-rows.md) | ResidualVQ | Theory in primes; code-side pending (quant_per_row uniform bits) | Priority: 1 (export-time, trajectory-neutral) — Changed algorithm: YES — per-row bits by 4× water-filling on Fisher contributions (bit_swap_improves_iff; fisher_optimal_scale); synthetic: 0.189× error at equal size (bits 1–4), ready-made test attached |
| 30 | [PROPOSAL-lazy-table-step.md](PROPOSAL-lazy-table-step.md) | LazyAdam | **REVERTED — HAGI_v2 cc1bdd1** (accepted in 9a381f3, removed by the revert of 1e707ce; Muon-branch `act` gate kept at optimal_lm.py:214) | Priority: 1 — Changed algorithm: YES — moments and step gated by `act` for 2-D tables (lazy_momentum_bound: drift ≤ c·β/(1−β) = 9c at β₁=0.9; measured 0.095); untouched row bitwise unchanged |
| 31 | [NOTES-verification.md](NOTES-verification.md) | DepthExitCert | Margin early exit is a heuristic until `L_h·bres₂` is logged (`margin_exit_unbounded_without_bound`) | Priority: 1 — replace fixed `margin > 2.0` by `2·L_h·bres₂` with logged per-block bound; reconcile AdamSNR memory 7680 vs 8192 |
| 33 | [PROPOSAL-hnet2-sparse-train.md](PROPOSAL-hnet2-sparse-train.md) | AdaptiveChunking | Cost model in primes; code-side pending (dense u2_all on training path) | Priority: 3 (changes the trajectory: hard gate at train time) — gather W_l2 rows only on boundary positions during training (≈5× fewer level-2 FLOPs; gradient through p_t intact, verified 0.67) |
| 34 | [PROPOSAL-gate-domain-rotation.md](PROPOSAL-gate-domain-rotation.md) | PairedGain / TailGate | Cost model in primes (`budget_split_radius_bounds`); code-side: `OLD_GATE_DOMAINS` working tree | Priority: 1 (trajectory-neutral) — rotate the capped measured set so every old domain is measured every ⌈n/m⌉ steps; stale growth = unknown, never 0 |

## When the cap becomes necessary (numbers from `radius` with sig2 = 0.05, b = 0.5, α = 0.05, L = ln 40)

| old domains n | windows/domain w = 2048/n | noise term | bias term | radius | × vs n = 4 |
|---|---|---|---|---|---|
| 4 | 512 | 0.027 | 0.007 | 0.034 | 1.00 |
| 8 | 256 | 0.038 | 0.014 | 0.052 | 1.54 |
| 16 | 128 | 0.054 | 0.029 | 0.083 | 2.42 |
| 32 | 64 | 0.076 | 0.058 | 0.134 | 3.92 |

(`budget_split_radius_bounds`: noise × √n, bias × n.) Against `WORST_TOL_ROLLBACK = 0.25`
the radius is fine up to n ≈ 16 and eats half the tolerance at n = 32 — that is
the point where `HAGI_OLD_GATE_DOMAINS` should be turned on *together with* the
rotation above; before that, full coverage (d602812) is strictly better.

## Measured (HAGI_v2 working tree, after d602812)

With n = 138 old domains and the 2048 budget the per-domain share was 16 windows
and the code agent measured a CE-difference error of **0.16 nat — every exceedance
of the 0.25 tolerance was noise**; raising the budget to 32768 (237 windows/domain)
gives **0.044 nat**. Check against `radius`: noise-dominated scaling
`0.16·√(16/237) = 0.042` ≈ 0.044 — the measurement matches the √(W/m) law of
`budget_split_radius_bounds`. Consequence: full coverage (d602812) is affordable
only with the 16× budget; the cap + rotation is the alternative when 32768 windows
per gate are too expensive.
