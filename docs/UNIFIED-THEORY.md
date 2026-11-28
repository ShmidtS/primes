# HAGI: unified theory map (what is proved, how it connects)

Statement of the goal (Hagi/Unified/IdealModel.lean): an "ideal model under a
budget" is a Pareto point **inside a guarantee class** — not an absolute. The
class is fixed by three things: the per-step risk limit, the quality floor kept
by every step, and the export error δ(bytes). Every certificate below is a
lemma about one component; `IdealModel` is the only place that says what their
conjunction means.

## The one diagram

```
data → windows ──► paired EB gate ──► certified step ──► composed loop ──► export ──► bytes
       ValWindows    PairedGain        CertifiedLoop      CertifiedStepCompose  ResidualVQ  IdealModel
       (step ≥ k)    radius, α/n      StepCert           composed_never_increases  fisher_optimal_scale  Pareto in class
       no overlap    worst gate ≤ m·α risk ≤ n·riskLim   gate ⇒ obj ↓            bit_swap 4×, stages     bytes = last axis
```

## Components and their exact certificates

| Layer | Module | Certificate | Code (HAGI_v2) |
|---|---|---|---|
| Measurement | `PairedGain` | `radius` (EB), `admit_false_le`, `radius_anti`, `budget_split_radius_bounds`, `clamped_budget_radius_le`, `worst_gate_certified_false_rollback` (≤ m·α) | `paired_margin_eb`, `WORST_GATE_MARGIN` (4f5dc81, default on, Bonferroni 16) |
| Windows | `ValWindows`, `ValCoverage`, `ValCost` | `adjacent_disjoint_iff`, `windows_exist`, `inv_sqrt_convex` | `step = max(k, n//w)` (fd040a7) |
| Step | `CertifiedLoop` | `StepCert`, `certified_loop`, `certified_loop_risk` (Σ risk ≤ n·riskLim) | HybridMuonAdamW, GPM (3c19a8c default on) |
| Composition | `CertifiedStepCompose` | `composed_never_increases`, `composed_gate_false_le` | rollback loop |
| Protection | `GPMProjection` | `pythagoras_k`, `decay_keeps_protected`, `truncation_loses_old` | GPM bases persist (test_gpm_persist) |
| Growth | `GaugeBalance` | `dead_loss_const`, `pairGrad_u_at_eps`, `rank1_gauge`, `stock_balance_attained`, `rank1_ntk_gauge_invariant` | `grow_depth` (zero block), `grow_width` |
| Optimiser | `LazyAdam`, `AdamSNR`, `EF21Scale`, `RareDecay`, `PathNorm` | `lazy_moment_drift`, `return_step_underestimates`, `coupled_decay_fixed_point`, `penalty_eq_path_norm` | `act`-gated decay (Muon branch) |
| Export | `ResidualVQ`, `GaugeBalance` | `fisher_optimal_scale`, `bit_swap_improves_iff`, `stage2_swap_stationary`, `residualTwoStage_error_le` | `quant_per_row(stages)`, `gauge_balance` (unwired) |
| Routing | `MirrorHedge`, `MixtureCoding`, `LzpExpert`, `SoftRouterMix` | `hedge_eta_sqrt` (√(2T ln K)), `mixCE_le_best_regret`, `lzp_false_ce` | MirrorHedge archiver |
| State / TBPTT | `GDNBridge` | `carry_influence_abs_le` (g^T tail) | `state_carry` |
| Bypass | `BypassMinK`, `ResidualMasking` | `min3/min6_coincidence`, `masked_importance_unbiased`, `bernoulli_prop_le_one` | `ExactBypass` |
| Target | `IdealModel` | `Pareto`, `ideal_is_bytes_minimization` | — |

## What follows (and what does not)

1. **Within the class, the only improvable axis is bytes.** Risk is bounded by
   the same `n·riskLim` for every program of the class; obj never increases on a
   certified step; export adds δ. Two programs with equal obj and risk differ
   only in bytes → PROPOSAL 29 (same error for fewer bytes) is *the* remaining
   lever. Measured: −1.0 of 2.3 nat for +13 % bytes (emb-only, knee at 128 rows).
2. **Every gate is a measurement statement, not a heuristic.** The worst-domain
   gate as shipped (4f5dc81) is `worst_gate_certified_false_rollback` verbatim;
   the point threshold it replaced trips on noise at 5.8 % per domain (w = 16).
3. **Budget laws are measured, not assumed.** radius(W/m): noise ×√n, bias ×n —
   confirmed by the code agent (0.16 → 0.044 nat, predicted 0.042).
4. **Some "improvements" are provably no-ops at this scale.** Gauge balance
   (25b) and asymmetric grow init (27) are exact identities with no CE effect
   under adaptive per-row scales / 150-step horizons. Keeping them as insurance
   is honest; claiming gains is not.
5. **The bytes axis is learnable.** `CodedSizeQAT.prefixCode_ge_entropy`:
   bytes ≥ H(level histogram) (Kraft + Jensen), so a coded-size loss term
   moves the one improvable axis *during training* — measured 218 → 202 B
   (−7.3 %) with fp32 CE unchanged and quantised CE −0.01 nat (PROPOSAL 37).
   Fisher scores (29c/d, `FisherRowScore`) choose *where* to spend the bytes;
   coded-size QAT shrinks *how many* are needed; `BitsBackPerm` recovers
   log₂(n!) of them for free on every growth block.

6. **Every threshold is one rule.** `DecisionRule.certified_decision`: act iff
   `ĝ − radius(n, α) > λ·ΔB`; the probability of certifying an action whose true
   gain is below its byte price is ≤ α. Gates (ΔB = 0), worst-domain rollback
   (α/16), stage-two rows (ΔB = row bytes), MDL (λ = 8 ln 2 / N) are instances.
   Consequence for the code (DERIVED-CONFIG §3): `ADAPTER_MIN_GAIN = 0.005` and
   `FIBER_MIN_GAIN = 0.01` sit *below* the radius at 4096 windows (0.073), and
   `ANCHOR_MIN_WINDOWS = 32` gives a radius of 1.5–3.0 nat against a tolerance of
   0.25 — they pass empirically, not with a finite-sample guarantee; the
   certified window counts are n*(0.005) = 764 311, n*(0.01) = 193 272,
   n*(0.25) = 463–978.

## What is not proved (and cannot be, from here)

* That the class has no better program — only that the shipped one attains the
  class bound. A real "ideal architecture" theorem needs the class itself to be
  derived (which floor, which riskLim, which δ curve) — a separate programme.
* NTK spectral entropy (`log det₊ K̄`; only the rank-1 term is formalised).
* Numeric TBPTT bias (tail law is proved; measured GDN `g` are not available).
