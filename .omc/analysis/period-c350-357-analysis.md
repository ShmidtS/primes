# Analysis of proved: C350–C357 period (2026-11-17, 8 commits)

All receipts/plan artifacts terminal (`.tmp/C350..C357`); full battery
CI: PASS at every landing beat (per-beat battery.log). HEAD 1f78b6e
(C357), tree clean. This beat (C358) is READ-ONLY analysis + this doc.

## Commit one-liners (C350–C357)

- C350 19d2711 `feat:` freedman bridge — `CertStochasticStep` +
  `stochastic_safe_step_whp` (radius R = 2√(V·L)+4c·L, failure ≤ δ),
  self-built Freedman (Mathlib has none), plan-review caught the
  adaptive-compensator {C>V} union-bound defect pre-landing.
- C351 7ab370b `feat:` global convergence under PL —
  `ce_loglinear_convex` (first convexity theorem for a concrete
  model head), `pl_descent_step`, `ce_global_convergence`:
  (1 − μ/L)^T from PL + smoothness premises only.
- C352 (this precedent pattern) — phase analysis C344–C351; ranked
  the next beats consumed by C353–C357: adapter (#1→C353),
  smoothness discharge (#2→C354), PL-free rate (#3→C355).
- C353 d282f64 `feat:` stochastic certified loop via kernel adapter —
  `Hagi/Unified/StochasticLoop.lean` (425 lines, 10 decls):
  `certStochasticStep_to_bounded` adapter (δ-budget → riskRem,
  literally per ТЗ), `stochastic_loop_certified` (union + kernel
  telescope through C345 capstone), `stochastic_loop_descent_whp`.
- C354 20ea52a `feat:` smoothness discharged — descent lemma for lse
  (L = 1, MVT + softDef-variance ≤ ∑b²), `ceSmoothL X` = row energy,
  `ce_smooth_ident`, `ce_global_convergence_ident` (h_smooth
  DERIVED from data geometry, EuclideanSpace carrier).
- C355 1bbc565 `feat:` PL-free O(1/T) rate — `lse_tangent_lower`
  (first-order convexity), `ce_convex_ident` (h_convex DISCHARGED),
  `gd_progress_convex` δ' ≤ δ − δ²/(2LR²), nonlinear telescope →
  `ce_rate_no_pl`: f(θ_T) − f* ≤ 2LR²/(T+1), every T ≥ 1, no PL.
  Probe caught a soundness hole (attainment needed — fixed pre-prod).
- C356 d1e7374 `feat:` variance-compensator Freedman —
  `history_exp_compensated_le` (E[exp(λS−λ²C)] ≤ 1, C = actual
  cond-var sum), `stochastic_safe_step_variance_whp`:
  1 − exp(−r²/(4Tσ)) in regime c·r ≤ 2Tσ — strictly stronger than
  C350's exp(−r²/(4(Tσ+cr))); {C>V} branch covered constructively
  (capped compensator ≤ σ pointwise, no union bound).
- C357 1f78b6e `feat:` PL via ℓ2-regularization — `ceReg` =
  ceOneHot t (X·θ) + (λ/2)‖θ‖², `strong_convex_pl` (strong convexity
  + attainment ⟹ PL, μ = λ, NO smoothness needed),
  `ceReg_smooth_ident` (L = ceSmoothL X + λ),
  `ce_global_convergence_reg`: (1 − λ/(ceSmoothL X+λ))^T with PL and
  smoothness BOTH discharged. X = 0 admissible (L = λ > 0).

## (a) ДОСТИЖЕНИЕ: полная конвергентная картина для реальной модели

The period closed the loop the C344–C351 bridges opened. What is now
proved END-TO-END (chain, each link a landed theorem):

1. **Safety whp (C350+C356).** A stochastic step with bounded,
   conditionally zero-mean noise, cond-var ≤ σ, realized-cover
   descent and drift floor γ is whp-safe:
   P[T·γ − r ≤ realized] ≥ 1 − exp(−r²/(4Tσ)) (C356 form,
   regime cr ≤ 2Tσ; C350 form exp(−r²/(4(Tσ+cr))) unconditional
   regime). Both coexist, zero rewrites.
2. **Safety → certified loop (C353).** The stochastic certificates
   plug through a consumer-layer adapter into the C345 kernel
   capstone: `stochastic_loop_certified` (union bound + telescope)
   and `stochastic_loop_descent_whp`. δ-budget is channeled into the
   risk channel (riskRem = residual ∑δ_i) — the ТЗ semantics
   literally. First end-to-end STOCHASTIC certified training loop.
3. **Convexity of the real head (C351+C355).** log-linear/softmax
   CE is convex in θ (`ce_loglinear_convex`, from weighted AM-GM →
   Hölder → ConvexOn) and first-order convexity is discharged on
   the EuclideanSpace carrier (`ce_convex_ident`).
4. **Smoothness derived from data (C354).** Descent lemma for
   f θ = ceOneHot t (X·θ) with L = ceSmoothL X = ∑_v ∑_j X v j²
   (row energy) — no smoothness premise, only X.
5. **PL-free rate (C355).** For every T ≥ 1:
   f(θ_T) − f* ≤ 2·L·R²/(T+1) under discharged smoothness +
   discharged convexity; pinned: h_floor, h_attains, R/h_dist.
6. **PL-geometric rate with λ (C357).** For ceReg (weight decay
   λ/2·‖θ‖²): f(θ_T) − fstar ≤ (1 − λ/(ceSmoothL X + λ))^T·
   (f θ₀ − fstar) — PL (μ = λ, from strong convexity + attainment)
   AND smoothness (L = ceSmoothL X + λ) both DISCHARGED.

**What this gives HAGI.** The «best learning algorithm» objective now
has a formal skeleton: a real loss head (softmax CE + weight decay)
with a *derived* Lipschitz constant from the data matrix, a proven
convexity theorem, a geometric rate in the regularized (strongly
convex) regime and an O(1/T) rate in the plain convex regime, plus a
whp-safe stochastic step wired into the certified-loop kernel. Every
constant is explicit (ceSmoothL X, λ, R, T, δ); every remaining
premise is a named binder with honest docs — no hidden empirics.

## (b) Health metrics

- **Freeze declarations:** 7525 (C350 base) → 7531 (C351, +6) →
  7531 flat C352 (analysis-only) → 7541 (C353, +10) → +17 (C354) →
  +6 (C355) → 7571 (C356, +6; base 7565 after interim) →
  **7579 (C357, +8)**. Net +54 proofs, 0 aliased, 0 changed, 0 lost
  at any beat — the period is purely additive-proof.
- **Modules:** ReachLint 606 (C350) → 607 (C351, Model file) →
  608 (C353, StochasticLoop) → 608 flat through C357. Layering
  clean: Probability@2 + Cert kernel consumer at Unified ≥3
  (LayerLint PASS each beat).
- **Premise ledger trend:** ZERO h_emp introduced in the whole
  period. All premises explicit binders (h_noise_*, h_step_descent,
  h_drift_floor, hrc, h_floor, h_attains, hlam, hL, h_rate).
  AssumptionScan lock: 10→11 operational names at C350
  (h_step_descent, intentional); stable since. Axioms: only
  propext/Quot.sound/Classical.choice.
- **STMDUP/DupLint/NsLint/DocLint:** PASS every beat; NsLint 1 vs
  baseline 1; STMDUP 0 duplicate groups. C354 reused (not
  duplicated) `pmfMean_exp_le`; local `softDef_le_one` copy is
  doc-noted.
- **Process wins:** plan-review caught a real defect pre-landing
  (C350 compensator), probe caught a soundness hole pre-production
  (C355 attainment; C357 same lesson — floor-only PL is FALSE).
  Two independent confirmations that the probe/plan-review gates
  are load-bearing.

## (c) Pinned-open list (honest negatives, all documented in-module)

1. **Attainment / minimizer existence** for ceReg (θstar with
   ceReg θstar ≤ fstar is a PREMISE h_attains; coercivity of CE +
   λ‖θ‖² not formalized). Required by C355 and C357 — the last
   un-discharged analytic premise of the family.
2. **Unregularized PL / margin route** — PL for bare CE via
   realizability/margin (C354 pinned; C357 route (a) pinned).
3. **Averaged-iterate** LR²/T rate (C355 proves per-iterate
   2LR²/(T+1); averaging not formalized).
4. **Full Freedman r²/(2(V+cr/3))** — Bennett-chord, adaptive λ
   (C350/C356 negatives; C356 delivered variance-compensator
   r²/(4V) as the accepted intermediate).
5. **Adaptive-λ / adaptive compensator σ process** — heteroscedastic
   noise with pointwise cond-var (stopped process + union bound
   route priced high).
6. Minor: EuclideanSpace transport of `ConvexOn` (Fin d → ℝ form),
   adaptive steps, non-ident-head non-convexity witness, Math
   tranche 2 (FannesPinsker — infeasible-upward verdict stands),
   semantic Freeze (A14 §4.0), challenge v5 pin.

## (d) Ranked next-beats (C359+ candidates, ≥5, Lean-tractable)

Ranked by (impact toward HAGI)/(effort).

1. **Attainment for ceReg via coercivity (Mathlib
   `exists_minimizer_of...` / proper + coercive + continuous).**
   ceReg is continuous + coercive (λ>0 ⟹ ‖θ‖→∞ forces f→∞ once CE
   ≥ 0 is shown) ⟹ minimizer exists ⟹ closes h_attains in BOTH
   C355 and C357. Impact: removes the LAST analytic premise of the
   convergence family — after this, `ce_global_convergence_reg` and
   `ce_rate_no_pl_ident` are fully premise-light model theorems.
   Effort: LOW-MEDIUM (Mathlib has the minimizer-existence API;
   coercivity of the sum is the only real work). Best ratio in list.
2. **Joint composition: stochastic gradient + PL model (C350/C356
   bridge × C357 model).** Instantiate `stochastic_loop_certified`
   with the regularized head: stochastic gradients of ceReg whose
   conditional mean is the true gradient, noise bounded — gives the
   FIRST end-to-end learning theorem: whp certified descent of GD
   on the actual softmax+weight-decay objective. Impact: the HAGI
   flagship (safety layer + convergence layer in one statement).
   Effort: MEDIUM (all ingredients landed; plumbing = noise model
   for CE gradients + cert instantiation). Requires nothing from #1.
3. **Margin PL route (unregularized).** PL for bare log-linear CE
   under realizability + margin (sep condition on X, t) — replaces
   the λ-regularization crutch with a data-geometry condition;
   tightens μ from λ to a margin-dependent constant. Impact: high
   (removes the "PL only via weight decay" caveat); effort: MEDIUM-
   HIGH (margin geometry not in Mathlib). Do after #2.
4. **Averaged-iterate LR²/T.** Fejér + telescoping over
   `ce_convex_ident`; upgrades the worst-case R² constant and gives
   the classical optimal rate shape. Impact: medium (constant-
   factor + textbook completeness); effort: LOW-MEDIUM. Cheap fill-
   in beat, composable with #1.
5. **Math tranche 2 (FannesPinsker → Math@0).** Requires extracting
   entropy-core downward first; payoff architectural only. Defer
   until a Math-layer consumer exists (YAGNI) — but keep on the
   list as the A14 QW8 closer.
6. **Semantic Freeze (A14 §4.0) / challenge v5 pin.** Infrastructure
   beats (statement-hash dedup gate; kernel-form challenge refresh
   after the stochastic-loop landing). Effort: high/medium; schedule
   as dedicated tooling beats, not mixed with math.

Top-3: **(1) attainment via coercivity** — closes the last pinned
premise with a ready Mathlib API; **(2) stochastic×PL joint
composition** — the first true end-to-end learning theorem, every
ingredient already landed; **(3) margin PL** — the honest strong-μ
route for the unregularized head.
