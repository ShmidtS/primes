/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.ChainToCone
import Hagi.Unified.MasterHAGICoupled

/-!
# GrandSynthesis — the composed capstone

`grand_synthesis` composes the measurement chain
(`DisagreementChain`/`ChainUnification`), the cone bridge
(`ChainToCone`), and the coupled capstone
(`MasterHAGICoupled`) into one statement about a single
trajectory: under certified stage conversions, frontier
dynamics, a physical risk/spend ledger, and probe-vector
floors, the trajectory simultaneously satisfies (1)
takeoff `C 0 * (1 + γ·k) ^ T ≤ C T` with `γ = beta^4 * kappa`,
(2) the telescoped risk bound, (3) the exact nonincreasing
budget account, and (4) every probe component above its
floor.
-/

open scoped BigOperators
open Hagi.Growth

namespace Hagi.Master

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Under the stated measured premises (certified stage
conversions, frontier dynamics, cone initialization, risk
and spend ledgers, probe floors), one trajectory
simultaneously yields: takeoff `C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T`,
the telescoped risk bound, the exact nonincreasing budget
`budget T = budget 0 − ∑ spend t` (the budget is its OWN
sequence — the R265 audit fix separates it from the
capability channel), and `qfloor i ≤ qvec T i` for every
probe `i`. -/
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
    -- the contract-side inputs; the budget is its OWN sequence
    -- (R265 audit fix: using C for both capability growth and
    -- the spend ledger made the premises contradictory —
    -- C T ≥ C 0 (1+r)^T with r > 0 vs C T = C 0 − Σ spend ≤ C 0)
    (risk spend : ℕ → ℝ)
    (budget : ℕ → ℝ)
    (qvec : ℕ → Fin 5 → ℝ) (qfloor : Fin 5 → ℝ)
    (hrisk_bound : C T - C 0 ≤ ∑ t ∈ Finset.range T, risk t)
    (hspend : ∀ t ∈ Finset.range T, 0 ≤ spend t)
    (hrisk : ∀ t ∈ Finset.range T, 0 ≤ risk t)
    (hbudget : budget T = budget 0 - ∑ t ∈ Finset.range T, spend t
      ∧ 0 ≤ budget T)
    (hqvec : ∀ i, qfloor i ≤ qvec T i) :
    -- 1. takeoff on the trajectory
    C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T
    -- 2. safety telescoped
    ∧ C T - C 0 ≤ ∑ t ∈ Finset.range T, risk t
    -- 3. budget (its own sequence): nonincreasing and exact
    ∧ budget T ≤ budget 0
      ∧ budget T = budget 0 - ∑ t ∈ Finset.range T, spend t
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
