# PROPOSAL index

Single source of truth for status (the proposal files carry none).
LIVE = wired in HAGI_v2 · UNWIRED = accepted, never called · REVERTED = by the
code agent (re-approval condition in the file) · READY = theory + test +
measurement, waiting for code · PENDING = theory only. Numbers live in the files.

| # | Document | Module | Status | What it changes |
|---|---|---|---|---|
| 2 | [PROPOSAL-tight-kappa.md](PROPOSAL-tight-kappa.md) |  | tight Bennett κ(R) curvature for the CE adaptive step (2.8–6.7× larger certified drops) | Tight Bennett κ(R)=(e^R−1−R)/R² curvature for the CE adaptive step: 2.77×/3.79×/6.73× larger certified drop… |
| 3 | [PROPOSAL-fisher-quant.md](PROPOSAL-fisher-quant.md) | Proposed | PENDING | g\ |
| 4 | [PROPOSAL-joint-step.md](PROPOSAL-joint-step.md) |  | PENDING | Simultaneous trunk+head certified step CE ≤ −2A²/R² + 2·HL·dd with measured trunk displacement; |
| 5 | [PROPOSAL-merge-meas.md](PROPOSAL-merge-meas.md) |  | measured (δ-gated) expert merge on a rational t-grid for MDL-prune | Measured (δ-gated) expert merge for MDL-prune: linResidualGrid on a rational t-grid replaces the δ-free qua… |
| 6 | [PROPOSAL-external-plan.md](PROPOSAL-external-plan.md) |  | external plan top-4: projected weight decay, EB gates, water-filling, window step | The external optimization plan top-4 ported: projected weight decay (leak factor (1−ηλ) exact), Empirical-B… |
| 7 | [PROPOSAL-certified-warmup.md](PROPOSAL-certified-warmup.md) |  | warm-up of a grown block via the certified finite step (COMMIT iff drop > 1e-12) | Warm-up of a grown block via the _certified_finite_step mechanism (COMMIT iff drop > 1e-12, else exact-roll… |
| 8 | [PROPOSAL-holdout-size.md](PROPOSAL-holdout-size.md) |  | PENDING | Holdout slice size for a non-trivial growth-gate certificate: k ≥ ln(2N/δ)/(2(ε/B)²); |
| 9 | [PROPOSAL-muon-guards.md](PROPOSAL-muon-guards.md) |  | Muon guards/telemetry on the growth-block layer: skip if ‖G‖_F ≤ eps, warn on σ_max | guards and telemetry for the Muon step on the growth-block layer W1: skip if ‖G‖_F ≤ eps, warn if σ_max(X₃)… |
| 10 | [DERIVED-CONFIG.md](DERIVED-CONFIG.md) |  | PENDING | Every training parameter is DERIVED (formula + number) or HONEST-GAP; |
| 11 | [PROPOSAL-smoothness-logging.md](PROPOSAL-smoothness-logging.md) |  | telemetry only: ‖w_o‖_F² per block, max/Σ ‖x_t‖² per batch | , guards: NO — two telemetry values (‖wo‖_F² per block, max_t ‖x t‖₂² and Σ_t ‖x t‖₂² per batch) turn the p… |
| 12 | [PROPOSAL-ef21-adaptive-scale.md](PROPOSAL-ef21-adaptive-scale.md) | EF21Scale | PENDING | (one line) — ternary EF21 scale s = ‖m‖_∞/2 per step instead of frozen 0.2·max |
| 13 | [PROPOSAL-paired-gain-eb.md](PROPOSAL-paired-gain-eb.md) | PairedGain | paired-gain lower bound mean − r_EB instead of mean − 2.4·SE at both call sites | (one function) — paired-gain lower bound mean − 2.4·SE becomes mean − r_EB with r_EB = √(2σ̂²L/n) + 2bL/n,… |
| 14 | [PROPOSAL-lazy-second-moment.md](PROPOSAL-lazy-second-moment.md) | LazyAdam | PENDING | (two lines) — dense v_v.mul_(b2) decays rare byte rows to v → 0; |
| 15 | [PROPOSAL-snr-table-lr.md](PROPOSAL-snr-table-lr.md) | AdamSNR | table-optimizer stationary Adam factor (μ/σ)/√(1+(μ/σ)²) from AdamSNR | (table optimizer) — stationary Adam factor = (μ/σ)/√(1+(μ/σ)²) (adamFactor_eq_snr_scale), saturating (adamF… |
| 16 | [PROPOSAL-adam-rel-reset.md](PROPOSAL-adam-rel-reset.md) | AdamRel | reset step_count and Adam moments at the start of each new domain | (certificate + regression guard) — reset step_count and Adam moments at the start of each new domain: the g… |
| 17 | [PROPOSAL-val-windows-step.md](PROPOSAL-val-windows-step.md) | ValWindows | window step max(k, n//256) so adjacent windows never share bytes | window step max(k, n // 256) instead of max(1, n // 256): adjacent windows share bytes iff k > step (adjace… |
| 18 | [PROPOSAL-repair-share-minimax.md](PROPOSAL-repair-share-minimax.md) | RepairShare | repair byte share ∝ √Δ is not minimax; water-filling is (when Δ are calibrated) | repair byte share ∝ √Δ is not minimax (sqrt_share_not_minimax: Δ = 4, 1 gives unequal residuals); |
| 19 | [PROPOSAL-adaptive-ingest-epochs.md](PROPOSAL-adaptive-ingest-epochs.md) | EpochTradeoff | PENDING | fixed CYCLE_EPOCHS = 4 → per-ingest stop at lam·R₀·ρ·(1−ρ)^E ≤ c₁ (stop_condition); |
| 20 | [PROPOSAL-gate-precheck-windows.md](PROPOSAL-gate-precheck-windows.md) | PairedGain | skip building the EB gate when n_windows < N(ε) = max(⌈8σL/ε²⌉+1, ⌈4bL/ε⌉+1) | (pre-gate) — skip building the EB gate when n_windows < N(ε) = max(⌈8σL/ε²⌉+1, ⌈4bL/ε⌉+1) (radius_eventuall… |
| 21 | [PROPOSAL-delta-budget.md](PROPOSAL-delta-budget.md) | PairedGain | PENDING | (delta scaling) — delta = δ₀/M per check on the current holdout gives total ≤ δ₀ (delta_budget_scaled); |
| 22 | [PROPOSAL-residual-masking.md](PROPOSAL-residual-masking.md) | ResidualMasking, MirrorHedgeMWU | PENDING | ℓ_b |
| 23 | [PROPOSAL-archiver-mixture.md](PROPOSAL-archiver-mixture.md) | MixtureCoding | PENDING | arithmetic coder on a Hedge mixture (model + PPM-3 + zlib); |
| 24 | [PROPOSAL-state-carry.md](PROPOSAL-state-carry.md) | GDNBridge | state carry: forward exact across chunks (gdnScan_append); wrap must zero the state | Changed algorithm: already in working tree — forward exact across chunks (gdnScan_append), wrap must zero t… |
| 25 | [PROPOSAL-gauge-balance.md](PROPOSAL-gauge-balance.md) | GaugeBalance | UNWIRED | exact gauge balance of every rank-1 factor and SwiGLU neuron before quantization (rank1_gauge identity; |
| 26 | [PROPOSAL-worst-domain-gate.md](PROPOSAL-worst-domain-gate.md) | TailGate | LIVE | worst-domain rollback gate on by default (max_le_imp_mean_le: strictly stronger than the mean gate; |
| 27 | [PROPOSAL-asymmetric-grow-init.md](PROPOSAL-asymmetric-grow-init.md) | GaugeBalance | grown block init W_down = ε·sign, W_up = 0: identity at step 0, W_up trainable at once | W_down = ε·sign-noise, W_up = zeros: identity kept at step 0, ∂L/∂W_up = −ε·x·y ≠ 0 from the first step (pa… |
| 28 | [PROPOSAL-importance-token-loss.md](PROPOSAL-importance-token-loss.md) | ResidualMasking | PENDING | token loss with q ∝ |
| 29 | [PROPOSAL-mixed-precision-rows.md](PROPOSAL-mixed-precision-rows.md) | ResidualVQ | LIVE (opt-in, HAGI_EMB_ROWS2=0) | per-row bits by 4× water-filling on Fisher contributions (bit_swap_improves_iff; |
| 29c | [PROPOSAL-emb-rows2-fisher.md](PROPOSAL-emb-rows2-fisher.md) | ResidualVQ | READY | emb stage-two rows ranked by p_i·‖res_i‖² (Fisher) instead of ‖res_i‖²: same bytes, −0.26 nat at k = 32 (measured) |

| 30 | [PROPOSAL-lazy-table-step.md](PROPOSAL-lazy-table-step.md) | LazyAdam | REVERTED | moments and step gated by act for 2-D tables (lazy_momentum_bound: drift ≤ c·β/(1−β) = 9c at β₁=0.9; |
| 31 | [NOTES-verification.md](NOTES-verification.md) | DepthExitCert | PENDING | replace fixed margin > 2.0 by 2·L_h·bres₂ with logged per-block bound; |
| 33 | [PROPOSAL-hnet2-sparse-train.md](PROPOSAL-hnet2-sparse-train.md) | AdaptiveChunking | PENDING | gather W_l2 rows only on boundary positions during training (≈5× fewer level-2 FLOPs; |
| 34 | [PROPOSAL-gate-domain-rotation.md](PROPOSAL-gate-domain-rotation.md) | PairedGain / TailGate | LIVE | rotate the capped measured set so every old domain is measured every ⌈n/m⌉ steps; |
| 35 | [PROPOSAL-worst-gate-margin.md](PROPOSAL-worst-gate-margin.md) | PairedGain | LIVE | certified growth grow − radius(α/n) > tol; |
