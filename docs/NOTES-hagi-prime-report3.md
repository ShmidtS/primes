# HAGI-Prime report 3 — verification note (cycle 74)

Checked against `primes` (HEAD after cycle 73) and `HAGI_v2` (HEAD 414ede5;
`state_carry` is present in the working tree of `optimal_lm.py`).

## Formal items

| Claim | Status in primes |
|---|---|
| AdamSNR `af ≤ min(s,1) ≤ √2·af` | `adam_le_clipped`, `clipped_le_sqrt2_adam`, `clipped_le_sqrt2_adam_high` |
| AdamRel `rel_reset_exact` | present |
| ResidualMasking identity, zero propensity, `(1−ρ)·MSE*/MSE_u < 1` | `gradCE_zero_of_onehot`, `covered_window_propensity_zero`, `combinedCost_lt_one_of_is` |
| `rootT` exact window threshold `n* = ⌈1/t*²⌉` | `radius_le_iff_ge_root` |
| `mean_clip_bias_le` | present (`PairedGain`) |
| Water-filling `F(m) ≤ 1 ≤ F(0)`, epoch stop `λR₀ρ(1−ρ)^E ≤ c₁` | `water_filling_exists`, `stop_condition` |
| **State-carry BPTT chunk equivalence** | **new**: `gdnScan_append`; `carry_without_wrap_leaks` (why `wrap` must zero the state) |

## Numeric cross-check (formulas only; the prototype is not on this machine)

- `rootT` at σ² = 0.25, b = 1.2, ε = 0.15, α = 0.05: n* = 181, r(181) = 0.1499,
  r(180) = 0.1504 — matches the report exactly.
- Archiver: Code 53 B → 0.6625 bpb, 4.06× vs zlib; Proto 75 B → 0.9375 bpb,
  2.89×; Algo 16 B → 0.5000 bpb — all reproduce.
- Quant 108,200 → 28,649 B = 3.78×; growth gain 0.1770; Code Δ = −0.0879 — reproduce.
- EpochTradeoff: E* = 3 is consistent iff 952 < λR₀ ≤ 1304 (report gives no λR₀).

Nothing in the report contradicts the theorems; the only unformalised item
(state carry) is now closed.
