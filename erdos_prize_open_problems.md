# Open Erdős Prize Problems — Lean 4 Formalization

Source: [erdosproblems.com](https://www.erdosproblems.com/) (1217 problems, 55 with monetary prize)
DeepMind formal-conjectures: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)

## Files

| File | Content |
|------|---------|
| `Primes/ErdosProblems.lean` | 13 open Erdős prize problems, grouped by theme |
| `Primes/VonMangoldtChain.lean` | Von Mangoldt chain infrastructure for #1196 |

## Problems by group

### A: Primitive sets
- **#1196** (Solved 2026) — Primitive set sum ≤ 1 + o(1). Tao et al. via von Mangoldt chains.
- **#143** ($500) — Well-separated set convergence. Partial: KLL25 ∑ 1/x = o(log n).

### B: Weird numbers
- **#470** ($10) — Odd weird numbers? Infinitely many primitive weird? Melfi conditional result.

### C: Unitary perfect numbers
- **#1052** ($10) — Finitely many? All even (AlphaProof). Known: 6, 60, 90, 87360, 5th.

### D: Covering & Jacobsthal — ALL ORIGINAL FORMALIZATION
- **#687** ($1000) — Jacobsthal function Y(x). Iwaniec Y(x)≪x², Maier-Pomerance Y(x)≪x(log x)².
  - **Proven**: `jacobsthal_lower_from_primorial` — covering argument Y(p_m) ≥ p_m-1.
- **#710** (₹2000) — Placement of multiples in intervals. Erdős-Pomerance bounds.
- **#711** (₹1000) — Generalized placement. van Doorn [vD26] answered 2nd question.
- **#708** ($100) — Divisibility covering. Erdős-Suranyi: g(n) ≥ (2-o(1))n.

### E: Additive combinatorics
- **#3** ($5000) — APs from divergent reciprocal sum. Bloom-Sisask: k=3.
- **#126** ($250) — Prime factors of sums. Erdős-Turán: log n ≪ f(n) ≪ n/log n.
- **#142** ($10000) — Asymptotic for r_k(N). Erdős: "enormously difficult".

### F: Other
- **#123** ($250) — d-completeness of {a^k b^l c^m}.
- **#50** ($250) — Totient distribution singularity.

## Infrastructure (VonMangoldtChain.lean)

- `IsPrimitiveSet` — Finset antichain under divisibility
- `erdosWeight`, `erdosSum` — Erdős weight 1/(n log n) and sum
- `vonMangoldtTransition` — Markov chain transition Λ(q)/log n
- `DivisibilityChain` — totally ordered subset of (N, |)
- `entranceMass` — entrance mass b_x(n) from Tao et al. proof
- Uses Mathlib's `ArithmeticFunction.vonMangoldt_sum` (∑_{q|n} Λ(q) = log n)

## Proven results (non-trivial)

| Theorem | Statement |
|---------|-----------|
| `jacobsthal_lower_from_primorial` | Y(p_m) ≥ p_m - 1 via explicit covering construction |

## Build

```
lake build
```

0 errors. 37 `sorry` warnings (open conjectures awaiting proof).
