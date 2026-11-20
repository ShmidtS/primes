# PROPOSAL index — HAGI_v2 port packages from primes

Five self-contained proposals for the HAGI_v2 implementation
agent. Each cites Lean anchors proved and frozen in primes
(Freeze 8462), a minimal Python diff, sanity numbers, a validation
criterion, and honest limits. Proposals are mutually independent —
apply in any order.

| # | Document | Primes theory | Status | One-liner |
|---|----------|---------------|--------|-----------|
| 1 | [PROPOSAL-adaptive-majorizer.md](PROPOSAL-adaptive-majorizer.md) (C466) | C462 | **SUPERSEDED by #2** (C471) | Variance-adaptive CE majorizer, WEAK e^R multiplier — replaced coefficient-for-coefficient by the tight κ below; the η≤1 cap, branch structure and validation loop carry over unchanged. |
| 2 | [PROPOSAL-tight-kappa.md](PROPOSAL-tight-kappa.md) | C471 | Proposed | Tight Bennett κ(R)=(e^R−1−R)/R² curvature for the CE adaptive step: 2.77×/3.79×/6.73× larger certified drops at R=0.5/1/2, weaker dominance premise. |
| 3 | [PROPOSAL-fisher-quant.md](PROPOSAL-fisher-quant.md) | C472 | Proposed | Curvature (Fisher/Gershgorin) per-coordinate quantization budgets for the ternary jump and self-edit weight prune: quadratic ΔL ≤ Σ\|g\|ε + ½Σcε², allocation monotone in curvature. |
| 4 | [PROPOSAL-joint-step.md](PROPOSAL-joint-step.md) | C475 | Proposed | Simultaneous trunk+head certified step CE ≤ −2A²/R² + 2·HL·dd with measured trunk displacement; strict-commit criterion and the joint-vs-alternating window. |
| 5 | [PROPOSAL-merge-meas.md](PROPOSAL-merge-meas.md) | C476 | Proposed | Measured (δ-gated) expert merge for MDL-prune: linResidualGrid on a rational t-grid replaces the δ-free quadratic gate; negative theorem pins why measurement is mandatory. |

Statuses: SUPERSEDED = replaced by a strictly stronger version
(kept for history); Proposed = ready for the HAGI_v2 agent,
pending its port + loop-5 validation (`real ≥ certified` every
step) as specified per document.
