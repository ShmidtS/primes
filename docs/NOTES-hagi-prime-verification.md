# HAGI-Prime synthesis — verification note (cycle 69)

Source: user-supplied synthesis (HAGI-Prime / PrimeCertTrain). Checked
against `primes` (HEAD b8666778) and `HAGI_v2` (HEAD 414ede5).

## Theorems cited — already in primes

All named certificates exist: `hnet_opt_ratio_unique`, `gdn_onehot_is_colUpdate`,
`mla_cache_saving`, `kv_work_ratio`, `config_storage_beats_dense`,
`polar_express_cycle_cert`, `gpm_zero_forgetting`, `total_compute_to_quality`,
`stable_factor_two`, `trit5_roundtrip`, `exists_best_mse_scale`,
`gate_never_increases`, `ce_total_eq_residual`, `bypass_reaches_compression_limit`,
`wt_saving`, `rotary_old_pairs_unchanged`, `exitLeak`, `rowStep_inert_iterate`,
`touchStep_dense_excess_pos`, `HadamardTernaryBridge`, `ResidualVQ`, `BitAlloc`,
`AnytimeHoldoutStop`, `MirrorHedge`, `kappa`, `adaptive_descent`,
`ce_adaptive_curv_le_range_tight` (= the min(Bennett, Range) curvature
`C* = min(R'²/8, κ(R')·Var_p(d))`), `selectedLoss_optimalPropensity_mse`
(importance sampling `q ∝ |ℓ_b|`, `MSE*`).

## Gap found and closed

`residual_masking` was the only unformalised item →
`Hagi/Theory/ResidualMasking.lean` (`gradCE_zero_of_onehot`,
`masked_saving_frac`); PROPOSAL 22 for the two missing code edits.

## Numerical cross-check of the curvature claim

Formulas as stated: κ(R') = (e^R' − 1 − R')/R'², C_bennett = κ·Var,
C_range = R'²/8 at R' = 1.5, Var = 0.0011:

    kappa    = 0.8808
    C_bennett= 0.000969   (document: 0.0010 ✓)
    C_range  = 0.28125   (document: 0.2812 ✓)
    ratio    = 290.30   (document: 279.23 — 4% off; consistent only if
                              the prototype used a slightly different Var)
    C_coarse: document 1446.84 is NOT reproduced by R'²/(8·Var²) (= 232438);
              the prototype's "coarse" formula is not stated and its source
              (/var/hagi_prime/) is not on this machine.

Conclusion: the Lean side is complete; the coarse-curvature number and the
exact ratio must be re-read from the prototype before being cited as measured.
