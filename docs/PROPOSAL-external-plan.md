# PROPOSAL: external plan port — C538–C541 theory packages for HAGI_v2

For: the HAGI_v2 implementation agent. Written by the primes
agent (C543; theory landed in primes C538–C541, Freeze 8666).
This is the answer to the external optimization plan mapped in
`.omc/analysis/external-plan-c537-mapping.md` (top-4 items
P4/P1/P6/P8; the mapping file was removed in c442e69 — history:
`git show c442e69^:.omc/analysis/external-plan-c537-mapping.md`):
every gap identified there is now proved and
frozen in primes. This document is the bridge theory →
implementation: per plan item — the exact theorem, what the code
must do so the theorem applies, the fix in meaning (not code),
and the plan's confirmed numbers. Proposals are mutually
independent — apply in any order. Same format family as
`PROPOSAL-adaptive-majorizer.md` … `PROPOSAL-merge-meas.md`.

## (a) Overview table

| Plan item | HAGI_v2 target | primes theorem (FQN, Freeze 8666) | Code fix (meaning) | Expected effect (plan numbers, confirmed) |
|---|---|---|---|---|
| P4 weight-decay leak (GPM) | hagi/gpu.py — GPM continual step | `Hagi.Theory.WeightDecayLeak.wd_proj_preserves`, `Hagi.Theory.WeightDecayLeak.naive_decay_leak`, `Hagi.Theory.WeightDecayLeak.wd_gpm_step_sound` | Apply decay PROJECTED into the complement of the protected span: `W ← W − ηλ·(W − W·P)` (i.e. `W·P⊥`), never naive `(1−ηλ)·W` | Projected SubspaceLeak 5.68e-15 (machine zero = exact zero) vs naive 1.945; naive leak factor exactly (1−ηλ) |
| P1 Empirical-Bernstein validation | hagi/core.py — AuditLedger sample sizing | `Hagi.Probability.empirical_bernstein_bound`, `Hagi.Probability.empirical_bernstein_mean_bound` | Replace Hoeffding radius R-based n with EB radius ε_EB = √(2σ̂²L/n) + 2bL/n, L = ln(2/α); σ̂² = measured empirical variance of increments | 27.49× validation-sample saving vs Hoeffding at the plan point (ΔCE=0.04, R≈11.09, σ̂=0.25, α=0.01); our constants give 41.5× |
| P6 OE completeness (synthesize) | hagi/loop.py — synthesize, OE hash-consing prune | `Hagi.Theory.OEComplete.oe_classes_partition`, `Hagi.Theory.OEComplete.oe_search_complete`, `Hagi.Theory.OEComplete.oe_search_terminates` | Keep the OE prune keyed on the vector of values on the FIXED probe set (first representative per OE-class); dedup budget ≤ naive enumeration | Witness bench: 343 → 4 visited nodes (~86×); HAGI_v2 analog 6478 → 896 nodes |
| P8 exact bypass PROVEN_EXACT | hagi/unified.py — Exact-First Residual Coupling | `Hagi.Theory.ExactBypass.ce_pointwise_of_prob_one`, `Hagi.Theory.ExactBypass.ce_split`, `Hagi.Theory.ExactBypass.exact_gate_sound`, `Hagi.Theory.ExactBypass.exact_gate_rejects_zero` | Certify coverage ONLY under the gate `p = 1` on the true byte at every covered position; reject the certificate at p = 0; accumulate CE additively over the covered/residual split | CE contribution of the covered share exactly 0; CE_total = CE_residual; the −33% FLOP on covered positions is correctness, not approximation |

## (b) P4 — Weight-decay leak (C538, module Hagi/Theory/WeightDecayLeak.lean)

Exact statements (verbatim signatures, namespace
`Hagi.Theory.WeightDecayLeak`):

```
theorem wd_proj_preserves (W : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P * P = P) (c : ℝ) :
    (W - c • (W - W * P)) * P = W * P

theorem naive_decay_leak (W : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (i : Fin m)
    (hne : nrm ((W * P) i) ≠ 0) :
    nrm ((((1 - c) • W) * P) i) < nrm ((W * P) i)

theorem wd_gpm_step_sound (W ΔC : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) (hC : ΔC * P = 0) (c : ℝ) :
    (W - ΔC - c • (W - W * P)) * P = W * P
```

Hypotheses the code must satisfy:

- Projector: only IDEMPOTENCE `P * P = P` (orthogonality/symmetry
  of P is NOT needed — rows are projected from the right);
- Decay: apply as `W − c • (W − W * P)` with `c = ηλ` — decay
  only in the complement `W − W * P = W·P⊥`;
- Complement update ΔC (momentum projection / polar-NS operator /
  projected EF21): black box, only `ΔC * P = 0` (its rows lie in
  the complement);
- For the leak to bite: `0 < c < 1` and a non-trivial protected
  row (`nrm ((W * P) i) ≠ 0`).

Exact intermediate law: `naive_decay_norm` gives the leak factor
EXACTLY (1 − c) per row norm — the plan's (1−ηλ), not a bound.
Witness: .tmp/C538 receipt (projected SubspaceLeak 5.68e-15 —
numerical zero standing for the exact zero above; naive
SubspaceLeak 1.945 — the strict inequality live).

## (c) P1 — Empirical-Bernstein validation radius (C539, module Hagi/Probability/EmpiricalBernstein.lean)

Exact statement (main, verbatim conclusion; full signature in
the module):

```
theorem empirical_bernstein_bound (q : V → ℝ)
    (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (X : ∀ t, (Fin t → V) → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hbnd : ∀ t pref, |X t pref| ≤ b)
    (sig : ℝ) (hsig : 0 < sig)
    (hmean : ∀ t pref,
      ∑ v, q v * X (t + 1) (Fin.snoc (α := fun _ => V) pref v) = 0)
    (hvar : ∀ t pref,
      ∑ v, q v * (X (t + 1) (Fin.snoc (α := fun _ => V) pref v)) ^ 2
        ≤ sig)
    (n : ℕ) (hn : 0 < n)
    (alpha : ℝ) (halpha1 : 0 < alpha) (halpha2 : alpha < 1) :
    1 - alpha ≤ prodPq (fun _ => q)
      (fun ω => |azumaSum X n ω| <
        Real.sqrt (2 * (n : ℝ) * sig * Real.log (2 / alpha))
          + 2 * b * Real.log (2 / alpha))

theorem empirical_bernstein_mean_bound … :
    1 - alpha ≤ prodPq (fun _ => q)
      (fun ω => |azumaSum X n ω / (n : ℝ)| <
        Real.sqrt (2 * sig * Real.log (2 / alpha) / (n : ℝ))
          + 2 * b * Real.log (2 / alpha) / (n : ℝ))
```

Hypotheses the code must satisfy (AuditLedger):

- Increments conditionally centered (`hmean`: per-prefix mean 0)
  and bounded `|X| ≤ b` (constructor range);
- `sig` is the MEASURED empirical variance (runtime premise,
  h_emp-style: a running bound Σq·X² ≤ σ̂² must actually be
  tracked at each prefix — this is the price of EB vs Hoeffding);
- `0 < σ̂` (a zero-variance tracker needs an ε- Floor or the
  Hoeffding fallback).

Validation numbers (plan point ΔCE = 0.04, R = 2·ln 256 ≈ 11.09,
σ̂ = 0.25, α = 0.01): Hoeffding n ≈ 177k; plan (Maurer–Pontil
3R·ln(3/α)/(n−1) form) n = 6439 → 27.49×; our constants
(√(2σ̂²L/n) + 2bL/n, L = ln(2/α)) n = 4267 → 41.5×.
Witness: .tmp/C539 receipt.

## (d) P6 — OE search completeness (C540, module Hagi/Theory/OEComplete.lean)

Exact statements:

```
theorem oe_classes_partition : Equivalence (fun p q : Prog => obsV p = obsV q)

theorem oe_search_complete {p : Prog} {space : List Prog} (hp : p ∈ space) :
    ∃ q ∈ oeFirsts obsV space, obsV q = obsV p

theorem oe_search_terminates (space : List Prog) :
    (oeFirsts obsV space).length ≤ space.length
```

Hypotheses the code must satisfy (synthesize):

- The OE key is the vector of program values on the FIXED probe
  set (`obsV`); the dedup keeps the FIRST representative per
  OE-class (any other policy voids `oe_search_complete`);
- Search space is depth-bounded (finite enumeration `space`).

Effect: the prune is CORRECTNESS-CERTIFIED — no solution visible
on the probes is lost, and the dedup visit budget never exceeds
the naive enumeration budget. Witness bench: 343 → 4 visited
programs (~86×) on the witness instance; HAGI_v2 analog plan
number: naive 6478 nodes without a solution vs Levin+OE+MITM 896
nodes to a solution. Witness: .tmp/C540 receipt.

## (e) P8 — Exact bypass, zero CE (C541, module Hagi/Theory/ExactBypass.lean)

Exact statements:

```
theorem ce_pointwise_of_prob_one (p : ℝ) (h : p = 1) :
    cePoint p = 0

theorem ce_split (p : ι → ℝ) (xs ys : List ι) :
    ceSum p (xs ++ ys) = ceSum p xs + ceSum p ys

theorem exact_gate_sound (p : ι → ℝ) (xs : List ι)
    (h : ExactGate p xs) : ceSum p xs = 0

theorem exact_gate_rejects_zero (p : ι → ℝ) (xs : List ι) (x₀ : ι)
    (hx₀ : x₀ ∈ xs) (hz : p x₀ = 0) : ¬ ExactGate p xs
```

(`ExactGate p xs := ∀ x ∈ xs, p x = 1`; `cePoint p = -Real.log p`;
bridge to the canonical logit CE SSOT:
`ceOneHot_eq_zero_of_softmaxP_eq_one`.)

Hypotheses the code must satisfy (unified.py):

- The symbolic certificate must place probability EXACTLY 1 on
  the true byte at every covered position (that is the
  PROVEN_EXACT gate — nothing weaker has a zero-CE guarantee);
- The gate must REJECT on p = 0: an erroneous coverage is a
  rejected certificate, never a computed `−ln 0`;
- CE accumulates additively over the covered/residual split
  (positions independent), so CE_total = CE_residual exactly.

Effect: covered positions contribute exactly CE = 0 — the −33%
FLOP saving on the covered share is exactness, not approximation.
Witness: .tmp/C541 receipt.

## (f) Honest warnings (scope limits — all four packages)

- P6 completeness is RELATIVE TO THE PROBES: the theorem equates
  observation vectors on the fixed probe set (`obsV q = obsV p`),
  NOT semantic equivalence of programs. Probe-set quality is an
  external, unproved premise.
- P1 EB: σ̂ is a runtime premise (measured conditional variance
  per prefix). The theorem does NOT assert stochastic validity
  of substituting a random σ̂ (the Maurer–Pontil λ-trick is an
  open form, not claimed). b is the constructor's increment
  range.
- P8: the gate is exact and REJECTS p = 0 (and everything
  ≠ 1); no calibration claim, no execution-speed claim, no
  aggregation-within-position claim (that is the canonical
  ceOneHot SSOT's job, reached via the bridge theorem).
- P4: projector hypothesis is idempotence only; the leak factor
  (1−ηλ) is exact per row norm, and `wd_gpm_step_sound` treats
  the complement update ΔC as a black box (`ΔC * P = 0`) — the
  internals of momentum/NS/EF21 mechanisms are NOT re-verified
  here, only their complement property.
- The bench numbers (27.49×, 41.5×, 343→4, 6478→896,
  5.68e-15 vs 1.945, −33% FLOP) are witness/plan measurements
  calibrating the theorems, not their conclusions.
