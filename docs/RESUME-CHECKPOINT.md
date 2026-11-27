# Resume checkpoint — cycle 84 (HEAD of primes at the time of writing)

Purpose: continue the HAGI research cycle after a context/environment reset
without re-deriving the state. Authoritative facts live in git; this file is a
map, not a source of truth.

## Where things stand

- Repo `C:\primes` (Lean 4.36.0 / Mathlib), CI = `bash scripts/ci.sh`
  (needs `export PATH="/c/Users/shmid/lean-toolchains/lean-4.36.0-windows/bin:$PATH"`
  — without it lake fails on Batteries and CI reports a false BUILD FAIL).
  Every commit in this session passed the full battery (Freeze, DocLint R4/R5,
  DocAnchorCheck, TrivialLint, LayerLint, ReachLint, NsLint, DupLint).
- Reference implementation `C:\HAGI_v2` is READ-ONLY (another agent).
  HEAD `9de7b61` (PROPOSAL 13, 25 accepted; 26dcd09 LZP → LzpExpert, 2aa1242 → ResidualVQ, 9de7b61 → GDNBridge). Working tree carries three
  uncommitted changes in `hagi/models/optimal_lm.py`: `state_carry`,
  `HARD_START`, `bypass_mask` — all three are certified in primes
  (`GDNBridge.gdnScan_append`, `HardStart.*`, `ResidualMasking.*`).
- 24 proposals in `docs/PROPOSAL-index.md`; accepted by the code agent:
  13 (EB adapters), 17 (non-overlapping windows, `fd040a7`), 25 (gauge balance,
  `0affafb`); `2aa1242` adds 2-stage residual quant (`ResidualVQ.residualTwoStage_error_le`). In the working
  tree, uncommitted: 22 (residual masking), 24 (state carry).
  Pending: 18 (repair-share minimax), 19 (adaptive epochs), 20 (gate
  pre-check with `rootT`), 21 (delta budget), 23 (archiver mixture).

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
| End-to-end composed step | `Hagi/Unified/CertifiedStepCompose.lean` | `gate`, `composedStep`, `composed_never_increases`, `composed_gate_false_le` |
| Growth, H-Net, MLA, depth exit, quant | existing modules | `WidthGrowth`, `hnet_opt_ratio_unique`, `mla_cache_saving`, `kv_work_ratio`, `exitLeak`, `HadamardTernaryBridge`, `ResidualVQ`, `stable_factor_two`, `trit5_roundtrip`, `exists_best_mse_scale`, `BitAlloc` |

## Verification notes

- `docs/NOTES-hagi-prime-verification.md`, `docs/NOTES-hagi-prime-report3.md`:
  every numeric claim of the three HAGI-Prime reports reproduces from the
  formulas (`rootT n* = 181`, bpb ratios 4.06/2.89/3.78, κ(R) curvature),
  except `curv_coarse = 1446.84` in report 1 (formula not stated, prototype
  not on this machine).

## How to continue the cycle

1. `cd /c/HAGI_v2 && git log --oneline | head` — any commit past `414ede5`
   (or a commit of `state_carry`/`HARD_START`/`bypass_mask`) is a new
   certificate target: read the diff, find the exact Lean model, probe in
   `.tmp/*.lean`, add to the sibling module, CI, commit.
2. If the code is unchanged, do not add micro-theorems for their own sake
   (YAGNI). Remaining research directions with real content:
   - a quantitative TBPTT bias bound tied to the measured `g` values of the
     GDN layers (needs the code's `a1, b1` statistics);
   - (done, cycle 83) composition theorem: `CertifiedStepCompose` — gate ⇒
     obj non-increasing for every ω; false gate pass ≤ α;
   - `n_eff` model for dependent windows is obsolete since `fd040a7` (step ≥ k).
3. CI hygiene: `scripts/ci.sh` now greps the whole build log (`.tmp/ci_build.txt`);
   DocLint R4 rejects backticked Python names in docstrings — write them bare.
   Docstring text must not contain `-/` or `5-/3` sequences (closes the block).

Total commits in primes at checkpoint: 2435.
