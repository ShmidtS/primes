# Analysis of proved: C344–C351 period (2026-11-16..17, 8 commits)

All receipts/plan artifacts terminal (`.tmp/C344..C351`); full battery
CI: PASS at every landing beat (per-beat battery.log). HEAD 7ab370b
(C351), tree clean. This beat (C352) is READ-ONLY analysis + this doc.

## Commit one-liners (C344–C351)

- C344 401e3ff `feat:` cert step gen bounded constructor —
  `CertStepGenBounded` (≤-law additive kernel constructor, ~13 new
  decls in Cert/StepGen + CertifiedLoop adapter) + premise-FREE
  bounded→exact bridge (`toExact`: spend := state-difference, no
  circularity — challenge-pinned) and hbudeq-discharging StepCert
  corollary. A14 QW3.
- C345 b42ba6f `feat:` certified loop on kernel —
  `Hagi/Unified/CertifiedLoopKernel.lean` (496 lines): 6-fold
  capstone (`certified_loop_kernel`) over generic
  CertStepGenBounded chains, TaskId-generic, + premise-FREE legacy
  bridge (`certified_loop_eq_kernel`, strictly STRONGER than legacy
  `certified_loop`: 5th conjunct risk ledger recovered as kernel
  instance). Challenge pin v4 kernel-form
  (Challenge/MasterChallengeV4Kernel). A14 QW4+QW5 — the central
  S3 kernel-absorption debt from the grand audit, CLOSED.
- C346 78bab6c `feat:` generic telescope + first migrations — 2 new
  generic forms in Foundations/Telescope (`telescope_le_sub`,
  `telescope_sum_floor_le`) + `Unified/TelescopeInstances.lean` with
  9 one-line migration instances (strictly stronger bounded-hyp
  forms, STMDUP-safe); full 40-telescope ledger (`.tmp/C346/ledger.md`:
  9 generic-instance, 5 already-generic, 17 domain-justified, 9
  to-migrate). A14 QW6 batch 1.
- C347 e4cf8e5 `refactor:` growth quarantine — 12 speculative
  modules (11 Growth + Dynamics.GrowthBridge) out of root closure;
  FQNs unchanged, Freeze-tracked via inventory.lean, ReachLint
  explicit exempt; 9 measurement-admission Growth modules kept in
  root. A14 QW7 — root h_emp exposure shrunk (lock now: 116 h_emp
  identifiers over 36 files, 5 proven; GrowthBridge/takeoff chain
  out of the default import closure).
- C348 6ac7787 + aebffa3 `feat:` math layer activation —
  Hagi/Prelude/InfoCore → Hagi/Math/Info/InfoCore (1510 lines, 31
  importers re-pointed, LayerLint "Math": 0 enforced, lakefile lib
  swap, superseded Prelude file dropped in fix-up commit). Freeze
  verify-only PASS, name-delta 0. FannesPinsker move INFEASIBLE
  (upward imports to Probability@2) — verdict pinned, deferred. A14
  QW8 tranche 1.
- C349 1ae742f `refactor:` remaining 9 telescopes migrated —
  batch 2 of QW6: 9/9 migrated, 0 deferred, all statements
  byte-identical, +55/−78 net deletion. QW6 now COMPLETE (18/40
  domain telescopes deduped; 17 domain-justified remain by ledger).
- C350 19d2711 `feat:` freedman bridge for stochastic safe steps —
  `Hagi/Probability/FreedmanStep.lean` (388 lines, 10 decls):
  adaptive-history Freedman (own `history_additive_freedman`) →
  `CertStochasticStep` structure + `stochastic_safe_step_whp`
  ( Prop-form: P[drop ≥ r] controlled, radius R = 2√(V·L)+4c·L,
  failure ≤ δ) + `stochastic_safe_step` CertStepGen-form wrapper.
  A14 research bridge #1 LANDED. Honest negatives pinned: constant-σ
  compensator only (adaptive needs union bound over {C>V}); no
  adaptive-λ; CertStepGen adaptation is consumer-layer (LayerLint
  forbids Probability@2→Cert import).
- C351 7ab370b `feat:` global convergence for log-linear CE under
  PL — `Hagi/Model/CEGlobalConvergence.lean` (287 lines, 6 decls):
  `convexOn_lse`, `ce_loglinear_convex` (log-linear/softmax CE head
  convex in θ — FIRST convexity theorem for a concrete model head),
  `pl_descent_step` one-step contraction, and
  `ce_global_convergence`: geometric rate
  f(iterates) − fstar ≤ (1 − μ/L)^T (f θ₀ − fstar) from PL +
  smoothness premises only (no convexity premise). A14 research
  bridge #6 LANDED.

## (a) What is now PROVEN — capability delta

The period delivered the two research bridges the C338/A14 ranking
put at #1 and #6, and they compose into the project's FIRST
training-convergence story:

1. **Deterministic global convergence (C351).** For any f with
   descent-lemma smoothness (L) and PL (μ), gradient descent with
   fixed step 1/L converges geometrically: (1−μ/L)^T. Applied shape:
   log-linear CE head is CONVEX in θ (proven from weighted AM-GM →
   Hölder → ConvexOn; generalizes lse_midpoint_le), so the
   PL-based rate is backed by a convexity theorem for the actual
   softmax head — not an abstract carrier.
2. **Stochastic safety (C350).** One stochastic step with bounded
   conditionally-zero-mean noise, conditional variance ≤ σ, and
   realized-cover descent premise is WHp-safe: certified drop
   r > 0 with failure probability ≤ δ at explicit radius
   2√(V·L)+4c·L. This is the first probability-side step
   certificate in the repo (Mathlib has NO Freedman — bridge is
   self-built, plan-review caught the adaptive-compensator defect
   pre-landing).
3. **Jointly they enable (not yet proven, now tractable):** a
   *stochastic certified training loop* — C350's
   `stochastic_safe_step` is already a CertStepGen-form def, and
   C345's `certified_loop_kernel` consumes any
   CertStepGenBounded chain. The missing link is a consumer-layer
   adapter (Cert instance from CertStochasticStep, layer ≥3) plus a
   Whp-lifted descent law. Every ingredient exists; no new math
   family is needed.
4. **Architecture delta (invisible to math, decisive for pace):**
   kernel capstone + bounded constructor + 18 migrated telescopes
   mean new step certificates plug into a 6-fold capstone with ZERO
   legacy-premise bundles (C344 removed hbudeq; C345 bridge is
   premise-free), and the Growth speculation is fenced out of the
   default closure.

## (b) Health metrics

- **Freeze declarations:** 7504 (C345) → 7515 (C346, +11: 2 generic
  + 9 instances) → 7515 flat through C347/C348/C349 (quarantine and
  moves are decl-neutral; C349 is net −23 lines) → 7525 (C350 +10)
  → **7531 (C351 +6)**. Nothing aliased/lost/changed at any point;
  period is almost perfectly additive-proof (net +27 proofs, 0
  statement edits).
- **Modules/coverage:** 607 ReachLint modules (605 at C349, 606 at
  C350, 607 at C351 — Model file added); root closure SHRANK by 12
  at C347. STMDUP PASS 0 duplicate groups (C351 battery). DupLint,
  NsLint (1 vs baseline 1), DocLint, LayerLint (Math:0, Model:4)
  all PASS.
- **h_emp trend:** lock header `h_emp files: 36, identifiers: 116,
  proven theorems: 5`. The A14 complaint "365 h_emp in root" is
  addressed structurally: the speculative cone/takeoff chain
  (h_emp-heavy GrowthBridge, Takeoff, LinearCone, …) is quarantined
  out of the default import closure; remaining h_emp are
  measurement-admission ledgers + Legacy freeze-tracked.
- **Premise ledger:** C350/C351 introduced ZERO h_emp; all new
  premises explicit binders (hL, h_rate, h_smooth, h_pl, h_floor,
  h_noise_*, h_step_descent, h_drift_floor). AssumptionScan lock
  grew 10→11 operational names (h_step_descent, intentional,
  reviewed). Axioms: only propext/Quot.sound/Classical.choice.
- **Duplication:** last STMDUP = 0 groups; C349 removed ~78 lines
  of duplicated induction via the generic core; the 17
  domain-justified telescopes are ledgered with reasons
  (multiplicative/vector/product forms — honest non-duplication).
- **Reproducibility:** unchanged env-blocked items (lean-toolchain
  absolute path, local mathlib path override — documented in
  lakefile comment, C338).

## (c) A14 scorecard

| Item | Status after C344–C351 |
|---|---|
| QW1 canonical toolchain | env-blocked, unchanged (A13 verdict) |
| QW2 tracked receipts | stays untracked (user directive) |
| QW3 bounded constructor | **DONE (C344)** |
| QW4 kernel view w/o premises | **DONE (C344/C345)** |
| QW5 capstone on kernel | **DONE (C345)**, challenge pin v4 |
| QW6 generic telescope | **DONE (C346+C349)**: 18 migrated, ledger closed |
| QW7 growth quarantine | **DONE (C347)**: 12 modules out of root |
| QW8 Math layer | **tranche 1 DONE (C348)**; FannesPinsker deferred-infeasible |
| QW9 KV mirror | deferred (conflicts QW2) |
| QW10 generated docs | later phase |
| Bridge #1 stochastic safe step (Freedman) | **LANDED (C350)** |
| Bridge #6 PL→global rate log-linear | **LANDED (C351)** (convexity bonus) |

8 of 10 QW items resolved or on-record; both top research bridges
landed. Phases 2–8 of A14: kernel/capstone phase COMPLETE, Math
layer phase tranche-1 complete, research-bridges phase 2/… landed
(rect EY #2 retry-bounded, Muon SVD #3, e-process #4 remain).

## (d) Ranked next-research list (C353+ candidates)

Ranked by (impact on HAGI goal)/(effort); every candidate has a
concrete Lean-tractable statement.

1. **CertStochasticStep → kernel adapter (consumer-layer
   integration).** New file layer ≥3 (e.g.
   Hagi/Unified/StochasticLoop.lean, imports Probability@2 +
   Cert@2 + kernel@6 legally): instance
   `CertStochasticStep.toCertStepGenBounded` reading the Whp-drop
   as the bounded ≤-law, then
   `stochastic_certified_loop_whp : ∀ᵐ ω, kernel conclusions hold
   along stochastic_safe_step chain`. Impact: turns C350+C345 into
   the first END-TO-END stochastic certified training loop — the
   flagship theorem family for HAGI. Effort: medium (all math
   exists; measurability plumbing only). RATIO: best in list.
2. **Discharge h_pl/h_smooth for the concrete log-linear head.**
   In CEGlobalConvergence: derive h_smooth from ‖X‖op ≤ L bound
   (premise: op-norm bound, one-liner once CE gradient identity
   `CEGradient.fderiv_ceOneHot_mulVec` is used) and h_pl at
   optima-neighborhood or under a strong-convexity-of-X premise
   (min singular value). Yields `ce_global_convergence_X`: first
   PREMISE-LIGHT convergence theorem for an actual model. Impact:
   high (C351 stops being a scheme, becomes a model theorem);
   effort: low-medium. Very high ratio.
3. **O(1/T) rate without PL (averaged iterate).** Convexity is now
   available in-repo (`ce_loglinear_convex`). Statement:
   `f (avg T) − fstar ≤ (L·D²)/(2T)` under h_smooth + convexity +
   bounded diameter (Fejér monotonicity + telescoping; the C351
   receipt already sketches the route and prices it "not cheap").
   Impact: covers the non-PL regime (real heads are often non-PL);
   effort: medium.
4. **Adaptive compensator Freedman (removes constant σ).** Route:
   stopped variance process V_τ + union bound over {C > V} (the
   defect plan-review caught), or e-process/self-normalization.
   Statement: same `stochastic_safe_step_whp` with
   h_noise_cond_var pointwise (V_k adaptive). Impact: high (all
   realistic noise is heteroscedastic); effort: high. Do AFTER #1
   (independent upgrade, doesn't block the flagship).
5. **Convexity of parametric non-ident heads — honest negative
   hunt.** `LogitMap` non-ident (e.g. tanh) heads: prove
   NON-convexity witness (two points + midpoint counterexample on a
   concrete instance) — turns the C351 docstring negative into a
   theorem, fencing where PL-without-convexity is the only route.
   Impact: medium (scope honesty for the convergence family);
   effort: low.
6. **Joint analytic-convergence pinned-open items:** EuclideanSpace
   transport of `ConvexOn` (Fin d → ℝ ↔ EuclideanSpace), adaptive
   step sizes (backtracking line search certified), C204
   stationarity probe follow-up. Each small; bundle as one
   cleanup-beat. Impact: low-medium; effort: low each.
7. **Math tranche 2 (FannesPinsker → Math):** requires first
   extracting entropy-core (EntropyConvexity/GibbsCore/GibbsCooling)
   downward or duplicating primitives at Math@0. Effort: high,
   payoff architectural only — defer until a Math-layer consumer
   other than InfoCore exists (YAGNI).
8. **Semantic Freeze (A14 §4.0):** statement-hash/alpha-equivalence
  dedup gate to unlock semantic (not just lexical) Freeze policy.
   Infrastructure beat, high effort, unblocks future dedup quota —
   schedule as a dedicated tooling beat, not mixed with math.

Top-3 recommendation: **(1) stochastic kernel adapter, (2) PL/smooth
discharge for log-linear CE, (3) O(1/T) averaged-iterate rate** —
together they convert the period's two bridges into a complete
certified-training-convergence stack (stochastic + deterministic,
PL and non-PL regimes).
