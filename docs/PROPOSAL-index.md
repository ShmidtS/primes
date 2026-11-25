# PROPOSAL index — HAGI_v2 port packages from primes

Nine self-contained proposals for the HAGI_v2 implementation
agent. Each cites Lean anchors proved and frozen in primes
(anchors to re-verify before port), a minimal Python diff, sanity numbers, a validation
criterion, and honest limits. Proposals are mutually independent —
apply in any order.

| # | Document | Primes theory | Status | One-liner |
|---|----------|---------------|--------|-----------|
| 1 | [PROPOSAL-adaptive-majorizer.md](PROPOSAL-adaptive-majorizer.md) (C466) | C462 | **SUPERSEDED by #2** (C471) | Variance-adaptive CE majorizer, WEAK e^R multiplier — replaced coefficient-for-coefficient by the tight κ below; the η≤1 cap, branch structure and validation loop carry over unchanged. |
| 2 | [PROPOSAL-tight-kappa.md](PROPOSAL-tight-kappa.md) | C471 | Proposed | Tight Bennett κ(R)=(e^R−1−R)/R² curvature for the CE adaptive step: 2.77×/3.79×/6.73× larger certified drops at R=0.5/1/2, weaker dominance premise. |
| 3 | [PROPOSAL-fisher-quant.md](PROPOSAL-fisher-quant.md) | C472 | Proposed | Curvature (Fisher/Gershgorin) per-coordinate quantization budgets for the ternary jump and self-edit weight prune: quadratic ΔL ≤ Σ\|g\|ε + ½Σcε², allocation monotone in curvature. |
| 4 | [PROPOSAL-joint-step.md](PROPOSAL-joint-step.md) | C475 | Proposed | Simultaneous trunk+head certified step CE ≤ −2A²/R² + 2·HL·dd with measured trunk displacement; strict-commit criterion and the joint-vs-alternating window. |
| 5 | [PROPOSAL-merge-meas.md](PROPOSAL-merge-meas.md) | C476 | Proposed | Measured (δ-gated) expert merge for MDL-prune: linResidualGrid on a rational t-grid replaces the δ-free quadratic gate; negative theorem pins why measurement is mandatory. |
| 6 | [PROPOSAL-external-plan.md](PROPOSAL-external-plan.md) | C538–C541 | Proposed | The external optimization plan top-4 ported: projected weight decay (leak factor (1−ηλ) exact), Empirical-Bernstein validation radius (27.49× samples), OE hash-consing prune completeness (relative to probes), PROVEN_EXACT bypass with CE = 0 on covered positions (gate rejects p = 0). |
| 7 | [PROPOSAL-certified-warmup.md](PROPOSAL-certified-warmup.md) (C644) | C642, C644 | Theory implemented in primes (C657/C660/C663/C665); code-side pending in HAGI_v2 | Warm-up of a grown block via the `_certified_finite_step` mechanism (COMMIT iff drop > 1e-12, else exact-rollback HOLD) on ONE fixed objective instead of plain Adam: closes the h1 premise of C642, so train-objective ≤ fOld becomes certified for any holdout-gate verdict; cost = one forward per trial; per-batch drops still do not telescope (negative theorem). |
| 8 | [PROPOSAL-holdout-size.md](PROPOSAL-holdout-size.md) (C662) | C660, C662 | Theory implemented in primes; code-side pending in HAGI_v2 | Holdout slice size for a non-trivial growth-gate certificate: k ≥ ln(2N/δ)/(2(ε/B)²); at ε=0.05B, δ=0.05 → k ≥ 1199 (N=10) / 877 (N=2) vs ≤512 in code (2ε ≈ 0.13–0.15B); holdout ≥ 1200 windows or fewer checkpoint peeks. |
| 9 | [PROPOSAL-muon-guards.md](PROPOSAL-muon-guards.md) (C677, rev. C682) | C668–C676, C678, C680–C682 | Theory implemented in primes; code-side pending in HAGI_v2 | Changed algorithm: NO — guards and telemetry for the Muon step on the growth-block layer W1: skip if ‖G‖_F ≤ eps, warn if σ_max(X₃) > 1+1e-6, accept the step only if the loss decreases on a small batch (operational ∃η), log ⟨G,X₃⟩/‖X₃‖_F and ‖G‖₁/√(mn). |

Statuses: SUPERSEDED = replaced by a strictly stronger version
(kept for history); Proposed = ready for the HAGI_v2 agent,
pending its port + loop-5 validation (`real ≥ certified` every
step) as specified per document.