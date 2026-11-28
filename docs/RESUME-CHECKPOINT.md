# Resume checkpoint — cycle 120

Purpose: continue the HAGI research cycle after a context/environment reset
without re-deriving the state. Authoritative facts live in git; this file is a
map, not a source of truth.

## Where things stand

- Repo `C:\primes` (Lean 4.36.0 / Mathlib), CI = `bash scripts/ci.sh`
  (needs `export PATH="/c/Users/shmid/lean-toolchains/lean-4.36.0-windows/bin:$PATH"`
  — without it lake fails on Batteries and CI reports a false BUILD FAIL).
  Every commit of the session passed the full battery (Freeze 9659 declarations,
  DocLint R4/R5, DocAnchorCheck, TrivialLint, LayerLint, ReachLint, NsLint, DupLint).
- Reference implementation `C:\HAGI_v2` is READ-ONLY (another agent).
  HEAD `4f5dc81` (PROPOSAL 35 ACCEPTED: certified worst gate `grow − radius(α/min(n,16)) > tol`, default on; GPM protection default on + bases persist across save/load → `GPMProjection.projOut_idem`, `pythagoras_k`, `Rollback.named_keeps_new`; gate and repair measure *all* old domains; window budget
  32768 because the 2048 budget gave *false rollbacks* at 16 windows/domain, n = 138:
  per-domain radius 0.16 nat × union over 138 domains, `worst_gate_false_rollback_le`;
  measured 0.044 at 237 windows, predicted 0.042 by `budget_split_radius_bounds`).
- 34 proposals in `docs/PROPOSAL-index.md`:
  - accepted and live: 13, 17, 26 (`5a773e6`), 34 in substance (`d602812`),
    35 (`4f5dc81`, theory→measurement→code with default on);
  - accepted but UNWIRED: 25 (`gauge_balance` defined, never called) → 25b;
  - reverted by the code agent without a stated cause: 18 (`cc1bdd1`), 30 (×2);
  - measured on HAGI_v2 with `scripts/ab_export_quant.py` / `scripts/ab_grow_init.py`:
    29 (emb-only 2nd stage: −1.0 of 2.3 nat for +13 % bytes, curve in the proposal),
    25b (no CE gain, no clip reduction — insurance only), 27 (theory exact, CE no-op),
    35 (point gate 5.8 % false trips at w = 16; certified 0; usable from w ≥ 128 with
    Bonferroni cap 16 — accepted as `4f5dc81`);
  - pending with ready-made tests: 29 (P1, export-time), 31, 25b;
  - pending without a test: 19–21, 23, 24, 25-addendum (MLA factor).
- Code-agent accept/revert pattern (notes): changes that move the training CE curve
  *without a protective role* get reverted; export/rollback-time changes and
  protection (GPM default on, 3c19a8c) get accepted. Verify *call sites*, not
  commits, when marking a proposal ACCEPTED.
- Numeric anchors theory ↔ code: gate radius 0.16 → 0.044 nat at 16 → 237
  windows (predicted 0.042); HAGI-Prime reports reproduce from formulas except
  `curv_coarse = 1446.84` (formula not stated).

## Theory map (what is proved, where)

| Topic | Module | Key theorems |
|---|---|---|
| EB admission gate, exact window threshold | `Hagi/Probability/PairedGain.lean` | `radius`, `radius_anti`, `n_suffices`, `max_gain_le`, `short_domain_radius_ge`, `radius_eventually_le`, `radius_le_iff_root`, `rootT`, `radius_le_iff_ge_root`, `admit_false_union_le`, `prodPq_union_le_sum`, `delta_budget_scaled`, `radius_delta_cost_le`, `mean_clip_bias_le` |
| Window grids | `Hagi/Data/ValWindows.lean`, `ValCoverage.lean`, `ValCost.lean` | `adjacent_disjoint_iff`, `indep_threshold`, `grid_covers_tail`, `windows_exist` |
| Importance sampling, residual masking | `Hagi/Theory/ResidualMasking.lean`, `Hagi/Probability/MirrorHedgeMWU.lean` | `gradCE_zero_of_onehot`, `covered_window_propensity_zero`, `combinedCost_lt_one_of_is`, `masked_importance_unbiased`, `masking_residual_boost8`, `covered_propensity_le`; `selectedLoss_optimalPropensity_mse*` |
| Bypass thresholds, hard starts | `Hagi/Theory/BypassMinK.lean`, `HardStart.lean` | `min3_coincidence`, `min6_coincidence`, `coincidence_anti`; `hardStart_eval_biased` |
| GDN state carry / TBPTT | `Hagi/Model/GDNBridge.lean` | `gdn_onehot_is_colUpdate`, `gdnScan_append`, `carry_without_wrap_leaks`, `carry_influence_decays`, `carry_influence_abs_le` |
| Muon guards, Polar Express | `Hagi/Optimization/MuonDual.lean`, `Hagi/Step/PolarExpress.lean` | `MuonGuards`, `guards_sound`, `polar_guards`, `polar_step_attains`, `polar_express_cycle_cert` |
| Protected weight decay / GPM | `Hagi/Step/GPMProjection.lean` | `decay_keeps_protected`, `decay_unprotected`, `projOut_idem`, `pythagoras_k`, `gpm_zero_forgetting` |
| Replay × repair, forgetting | `Hagi/Data/ReplaySchedule.lean`, `Hagi/Unified/RepairLoop.lean`, `Hagi/Learning/ContinualForgetting.lean`, `EpochTradeoff.lean` | `replay_repair_bounded`, `no_tol_guarantee`, `stop_condition`, `oldReg_ratio`, `overhead_from_measurement` |
| Repair cost/share | `Hagi/Unified/RepairCost.lean`, `ReplayCompute.lean`, `RepairShare.lean` | `replay_mem_const`, `block_mem_le`, `replay_steps_le`, `sqrt_share_not_minimax`, `water_filling_exists` |
| Rollback | `Hagi/Unified/Rollback.lean` | `paramsOnly_ne_full`, `honestCE`, `rolled_back_forget_zero`, `positional_misaligns`, `named_keeps_new` |
| Adapters | `Hagi/Learning/AdapterBank.lean` | `adapter_init_identity`, `rank_one_cheap_iff`, `rank_two_cheap`, `warm_start_not_certified` |
| Mixture coding (archiver) | `Hagi/Information/MixtureCoding.lean` | `mixCE_le_best_regret`, `hedge_negLogW_le` |
| Gauge balance (arXiv:2611.27889v1) | `Hagi/Step/GaugeBalance.lean` | `rank1_gauge`, `stock_balance_min`, `stock_balance_attained`, `dead_loss_const` |
| LZP-эксперт archiver | `Hagi/Information/LzpExpert.lean` | `lzp_false_ce` (проигрыш ≤ −log(1−λ·cf) ≤ 0.35 nat), `lzp_true_ce_lower` |
| Rare features × weight decay | `Hagi/Step/RareDecay.lean` | `dense_decay_fixed_point` (∝ f), `coupled_decay_fixed_point` (f-independent; certifies `where(act, 1−lr·wd, 1)`), `dense_over_coupled` |
| Path norm / heat death | `Hagi/Step/PathNorm.lean` | `penalty_eq_path_norm` (balanced decay = 2·path norm), `path_norm_shrinks` ((1−λ)^{2t}), `prox_kills_small`/`prox_threshold` |
| End-to-end composed step | `Hagi/Unified/CertifiedStepCompose.lean` | `gate`, `composedStep`, `composed_never_increases`, `composed_gate_false_le` |
| Growth, H-Net, MLA, depth exit, quant | existing modules | `WidthGrowth`, `hnet_opt_ratio_unique`, `mla_cache_saving`, `kv_work_ratio`, `exitLeak`, `HadamardTernaryBridge`, `ResidualVQ`, `stable_factor_two`, `trit5_roundtrip`, `exists_best_mse_scale`, `BitAlloc` |

## Verification notes

- `docs/NOTES-hagi-prime-verification.md`, `docs/NOTES-hagi-prime-report3.md`:
  every numeric claim of the three HAGI-Prime reports reproduces from the
  formulas (`rootT n* = 181`, bpb ratios 4.06/2.89/3.78, κ(R) curvature),
  except `curv_coarse = 1446.84` in report 1 (formula not stated, prototype
  not on this machine).

## How to continue the cycle

1. `cd /c/HAGI_v2 && git log --oneline | head` — a new commit is a certificate
   target: read the diff, find the exact Lean model, probe in `.tmp/*.lean`, add to
   the sibling module, CI, commit. Then check the call site (`rg "<name>\(" hagi
   | grep -v def`) before writing ACCEPTED.
2. If the code is unchanged, do not add micro-theorems for their own sake
   (YAGNI). Proposals with numbers carry a numpy simulation and a regression test
   before submission (LESSONS, cycle 97). On a revert, log a re-approval condition
   instead of resubmitting.
3. CI hygiene: `scripts/ci.sh` greps the whole build log; DocLint R4 rejects
   backticked non-Lean names in docstrings (write them bare); R5 wants every number
   either a literal of the file or marked «измерено»/«#eval»; docstrings must not
   contain `-/`.

Total commits in primes at checkpoint: 2435.

## Retrospective at cycle 120 (what the theory bought)

* Accepted by code and matched 1:1 by a theorem: 13, 17, 26 (`TailGate`), 34
  (`PairedGain.budget_split_radius_bounds`, confirmed by measurement), guard
  test `2a34515` (→ `RareDecay`).
* Theory that prevented a wrong change: 28 v1 (cap 4 → biased by 1/q,
  `bernoulli_prop_le_one`); the `x < y` mis-statement of the bit swap (true
  threshold 4×, `bit_swap_improves_iff`); the false "only all-negative is dead"
  claim (unequal inputs), restricted to the per-input form.
* Theory ahead of code: 18–21, 23, 24, 25b, 25-addendum, 27, 28 v2, 29, 31, 33.
* TBPTT tail is formalised (`GDNBridge.carry_influence_abs_le`); only the numeric
  plug-in with measured GDN `g` is missing.
* Not formalised, honestly: NTK spectral entropy (`log det₊ K̄`; rank-1 term is
  `rank1_ntk_gauge_invariant`), capillary form `α^{-N/2}` of the dead-set volume
  (sign model: `dead_one_input_fraction`, `sign_assignments_card`).

