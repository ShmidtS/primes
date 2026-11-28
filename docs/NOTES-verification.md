# Verification notes — external reports vs primes

Each claim of a user-supplied report is checked against the theorems (Chesterton
first) and recomputed from its formula. "Not reproducible" means the prototype
(`/var/hagi_prime/`) is not on this machine.

## HAGI-Prime reports 1–3

| Claim | Status |
|---|---|
| every cited certificate (HNet-2, GDN, MLA, Polar, GPM, bypass, trit5, Hadamard, ResidualVQ, MirrorHedge, κ-curvature, importance sampling) | exists in primes |
| `residual_masking` | the one gap → `ResidualMasking.lean` (`gradCE_zero_of_onehot`, `masked_saving_frac`) |
| state-carry chunk equivalence | `GDNBridge.gdnScan_append`; `carry_without_wrap_leaks` (why `wrap` must zero the state) |
| AdamSNR `af ≤ min(s,1) ≤ √2·af` | `adam_le_clipped`, `clipped_le_sqrt2_adam_*` |
| `rootT` n* = ⌈1/t*²⌉ | `radius_le_iff_ge_root`; at σ² = 0.25, b = 1.2, ε = 0.15, α = 0.05: n* = 181, r(181) = 0.1499 — exact |
| water-filling, epoch stop | `water_filling_exists`, `stop_condition`; E* = 3 iff 952 < λR₀ ≤ 1304 |
| curvature κ(R') = (e^R'−1−R')/R'², C_bennett = 0.000969, C_range = 0.28125 | reproduce; ratio 290.3 vs 279.2 (4 %, Var differs); **`curv_coarse = 1446.84` not reproducible** — do not cite as measured |
| archiver 0.6625 / 0.9375 / 0.5000 bpb (4.06× / 2.89× / 3.78× zlib), quant 108200 → 28649 B, growth gain 0.1770 | reproduce |

## HagiOptimalV3 report

- L2 fire 19.9 % → 2.51× vs r = 2, 5.03× vs a full layer; AdamSNR −31.4 %;
  EF21 +0.0171; early exit −0.0077 — reproduce. Mean CE rows differ in the
  3rd–4th digit; "4.4×" is 4.64×; the 7.7k-float saving does not add up
  (256·24 + 256·8 = 8192 ≠ 7680) — not an anchor.
- `margin > 2.0` is a heuristic, not a certificate: `DepthExitCert.margin_exit_unbounded_without_bound`.
  Safe iff `2·L_h·bres₂ < margin` (log `L_h·bres₂`, PROPOSAL 31).
- `AdaptiveHNet2Layer` saves 2.5× at inference only; the training branch is dense.
- CortexFiber: early trunk freeze leaves `‖P t‖²` unreachable for any fiber
  (`CortexFiber.frozen_trunk_unreachable`) — hence Hybrid, not Frozen.

## NTK balance vs quantisation (literature)

No paper links the two directly. Cai 2024 (arXiv:2407.17834): normalisation cuts
the max and variance of NTK eigenvalues; Zhang 2022 (arXiv:2206.05916): binary
weights give exponentially decaying NTK spectra. In primes the linear-regime
claim is already covered: `GaugeBalance.balance_key` + `ResidualVQ.frobSq_mul_le`;
the rank-1 term is gauge invariant (`rank1_ntk_gauge_invariant`). The spectral
statement (`log det₊ K̄`) is not formalised.

## HAGI-Prime v4 (OptHagiV4 + CertOpt + HadamardFisherVQ + MirrorHedge), NumPy

Arithmetic reproduces: skip 256·(2+4+2)·2 = 4096 params; head share 46.8 % ≈ 47 %;
nats → bpb (2.2767 → 3.285, 1.8726 → 2.702); Polar-Express 9 vs 15 matmul
= −40 %; archive N = bytes·8/bpb = 13 697 for all rows; 2653/3478 = 23.7 %,
1129/1974 = 42.8 %; trits5 = 5·log₂3/5 = 1.585 bit/weight bound; κ(1.5) = 0.8808.

Theory each claim rests on (all in primes): HNet `hnet_opt_ratio_unique`
(r* = (2bT/a)^{1/3}; the report's 3.2…6.4 for T = 64…512 implies b/a = 0.256 —
not stated there); `mhc_stack_no_growth` (Birkhoff trunk, ρ ≤ 1);
`polar_express_cycle_cert` (covers σ₀ = 0.05, below the NS theorem's 0.5);
`cosine_sched_bounds` 3/20 floor; `clipped_weight_unbiased`,
`gradCE_zero_of_onehot`; `ce_adaptive_curv_le_range_tight`;
`sqrt_share_not_minimax` (water-filling replay, −45 % worst — PROPOSAL 18,
reverted by the code agent without cause: new evidence to re-approve on
worst-domain CE); `wd_compl_annihilates`, `decay_keeps_protected`;
`fisher_optimal_scale`, `bit_swap_improves_iff`, `topk_residual_is_optimal`;
`mixCE_le_best_regret`; `gdn_onehot_is_colUpdate` and the new `gdn_beta_readout`
(β ∈ (0,2) is a sign-flipping generalised Householder write — now proved).

Cross-checks with our own measurements: SemCache self-calibrated λ = 0.35 →
−0.163 nat on structured data, λ = 0 on noise (our PROPOSAL 36: −0.76 / 0.0000);
asymmetric init W_down = 0 keeps the function exactly (`dead_loss_const`: W_up
is frozen until the first step — correct for depth growth); gauge balance as a
*preprocessing for quantisation* — consistent with 25b (no CE gain on its own).

Not reproducible here: the 2×2 matrix and the quantisation table need the
NumPy implementation (not on this machine); the 3.5×–21× Bennett speed-up is
the certified-drop ratio, not wall-clock.

## Measured on HAGI_v2 (the two `ab_*.py` scripts)

| Claim | Recomputed | Verdict |
|---|---|---|
| L2 fire 19.9 % vs r=2 (50 %) → 2.5× | 2.51× | ✓ |
| 19.9 % vs full layer → 5× | 5.03× | ✓ |
| mean CE row 1 | 0.8732 | ✓ |
| mean CE rows 2/3/4/5 | 0.8493 / 0.8485 / 1.7418 / 1.0057 | report says 0.8489 / 0.8482 / 1.7416 / 1.0059 — 3rd–4th digit mismatch (rounding of inputs?) |
| worst forgetting 0.2674 → 0.0576 = 4.4× | 4.64× | report understates |
| AdamSNR memory −31.4 % | 7680/24492 = 0.3136 | ✓ |
| "saving 7.7k floats = v_v on emb + E_bi" | 256·24 + 256·8 = 8192 ≠ 7680 | composition does not add up (7680 = 5·1536) |
| EF21 ΔCE | +0.0171 | ✓ |
| Early-exit ΔCE | −0.0077 | ✓ |
| Top-1 agreement 99.01/99.07 %, coverage 52.5/52.9/61.5 % | empirical | not reproducible here |
- PROPOSAL 31 (new): log `L_h·bres₂` per block at export and replace the fixed
- The AdamSNR memory accounting (7680 vs 8192) must be reconciled before the
