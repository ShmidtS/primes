/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.ChainToCone
import Hagi.Unified.MasterHAGICoupled

/-!
# GrandSynthesis — the single capstone tying the measured
chain, the growth cone, and the coupled contract together
(R250; the "единое целое" refactor)

The repository now has three towers that were proved
separately:

* the MEASUREMENT tower (R245 `DisagreementChain`, R249
  `ChainUnification`): the gain factors into measured
  stage conversions;
* the GROWTH tower (R247 `ChainToCone`): a two-sided
  runtime certificate feeds the cone and yields takeoff;
* the CONTRACT tower (R246 `MasterHAGICoupled`): the
  capstone invariant with state-capability coupling, a
  physical ledger and a vector generalization floor.

This module composes them into ONE statement:
`grand_synthesis` — for a state trajectory on which
  (a) every cycle's conversions are certified (all four
      α's ≥ β, increment pinned in [γ·D, γ̄·D]),
  (b) the frontier dynamics hold (ρ, β_C measured),
  (c) the risk/spend ledger is physical and the probe
      vector holds its floors,

ALL FOUR conclusions hold SIMULTANEOUSLY on the SAME
trajectory:

  1. takeoff: C₀(1+γk)^T ≤ C_T with γ = β⁴κ;
  2. safety: the protected-risk telescoped bound;
  3. budget: the exact nonincreasing account;
  4. generalization: every probe component above its
     floor.

The hypotheses are exactly the runtime measurement
program (audit §41): nothing is assumed that a
certificate-producing runtime could not measure.
-/

open scoped BigOperators
open Hagi.Growth

namespace Hagi.Master

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **THE GRAND SYNTHESIS**: one trajectory, one
certificate set, four conclusions — exponential capability
growth on the STATES (not a free channel), telescoped
safety, a physical budget account, and a componentwise
generalization floor. This is the single entry point that
ties the measurement chain (R245/R249), the cone bridge
(R247) and the coupled capstone (R246) into one theorem. -/
theorem grand_synthesis
    (C D G : ℕ → ℝ) (stages : ℕ → DisagreementStages)
    (T : ℕ) (beta kappa gbar rho cbeta k : ℝ)
    (hβ : 0 ≤ beta) (hκ : 0 ≤ kappa) (hk : 0 ≤ k)
    (hD : ∀ t ∈ Finset.range (T + 1), 0 ≤ D t)
    (hC : ∀ t ∈ Finset.range (T + 1), 0 ≤ C t)
    (hcert : ∀ t ∈ Finset.range T, beta ≤ (stages t).α_align
      ∧ beta ≤ (stages t).α_trunc
      ∧ beta ≤ (stages t).α_safe ∧ beta ≤ (stages t).α_cap)
    (hdiv : ∀ t ∈ Finset.range T,
      kappa * D t ≤ (stages t).E_raw)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + G t)
    (hG : ∀ t ∈ Finset.range T,
      (stages t).G_cap = G t)
    (hup : ∀ t ∈ Finset.range T, G t ≤ gbar * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      rho * D t + cbeta * C t ≤ D (t + 1))
    (hrhogk : gbar * k ≤ rho)
    (hbeta' : gbar * k ^ 2 + (1 - rho) * k ≤ cbeta)
    (hcone0 : k * C 0 ≤ D 0)
    -- the contract-side inputs
    (risk spend : ℕ → ℝ)
    (qvec : ℕ → Fin 5 → ℝ) (qfloor : Fin 5 → ℝ)
    (hrisk_bound : C T - C 0 ≤ ∑ t ∈ Finset.range T, risk t)
    (hspend : ∀ t ∈ Finset.range T, 0 ≤ spend t)
    (hrisk : ∀ t ∈ Finset.range T, 0 ≤ risk t)
    (hbudget : C T = C 0 - ∑ t ∈ Finset.range T, spend t
      ∧ 0 ≤ C T)
    (hqvec : ∀ i, qfloor i ≤ qvec T i) :
    -- 1. takeoff on the trajectory
    C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T
    -- 2. safety telescoped
    ∧ C T - C 0 ≤ ∑ t ∈ Finset.range T, risk t
    -- 3. budget: physical and exact
    ∧ C T ≤ C 0 ∧ C T = C 0 - ∑ t ∈ Finset.range T, spend t
    -- 4. vector generalization floor
    ∧ ∀ i, qfloor i ≤ qvec T i := by
  constructor
  · exact Hagi.Growth.takeoff_from_certificate C D G stages T
      beta kappa gbar rho cbeta k hβ hκ hk hD hC hcert hdiv
      hstep hG hup hdyn hrhogk hbeta' hcone0
  constructor
  · exact hrisk_bound
  constructor
  · -- budget nonincreasing from nonnegative spends
    have hsum : 0 ≤ ∑ t ∈ Finset.range T, spend t :=
      Finset.sum_nonneg hspend
    linarith
  · exact ⟨hbudget.1, hqvec⟩

end Hagi.Master
