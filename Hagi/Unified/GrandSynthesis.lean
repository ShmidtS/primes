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

namespace Hagi.Unified

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


/-! ## Слабые посылки для пунктов 2/4 (R540) -/

/-- **Риск-телескоп из покомпонентного покрытия (R540, пункт
2 из слабых посылок)**: если каждый единичный прирост
capability покрыт риском (G t ≤ risk t), то полный прирост
ограничен телескопом риска: C T − C 0 ≤ Σ risk. Вместо
глобальной посылки hrisk_bound — локальная пошаговая. -/
theorem risk_telescope_of_growth_covered (C G risk : ℕ → ℝ)
    (T : ℕ)
    (hstep : ∀ t ∈ Finset.range T, C (t + 1) = C t + G t)
    (hcover : ∀ t ∈ Finset.range T, G t ≤ risk t) :
    C T - C 0 ≤ ∑ t ∈ Finset.range T, risk t := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ,
        hstep T (Finset.mem_range.mpr (Nat.lt_succ_self T))]
      have hle : C T - C 0
          ≤ ∑ t ∈ Finset.range T, risk t :=
        ih (fun t ht => hstep t (Finset.mem_range.mpr
          (lt_trans (Finset.mem_range.mp ht) (Nat.lt_succ_self T))))
          (fun t ht => hcover t (Finset.mem_range.mpr
            (lt_trans (Finset.mem_range.mp ht) (Nat.lt_succ_self T))))
      have hpt := hcover T (Finset.mem_range.mpr (Nat.lt_succ_self T))
      have h1 : C T + G T - C 0 ≤ C T + risk T - C 0 := by linarith
      have h2 : C T + risk T - C 0
          ≤ ∑ t ∈ Finset.range T, risk t + risk T := by linarith
      linarith

/-- **Полы из монотонности (R540, пункт 4 из слабых посылок)**:
если floors выполняются в нуле и каждый компонент векторного
описания монотонно не убывает, то полы выполнены на всём
горизонте — вместо плоской передачи qvec-гипотезы. -/
theorem qfloor_le_of_monotone {n : Type*} [Fintype n]
    (qvec : ℕ → n → ℝ) (qfloor : n → ℝ) (T : ℕ)
    (h0 : ∀ i, qfloor i ≤ qvec 0 i)
    (hmono : ∀ i t, qvec t i ≤ qvec (t + 1) i) :
    ∀ i, qfloor i ≤ qvec T i := by
  intro i
  induction T with
  | zero => exact h0 i
  | succ T ih => exact le_trans ih (hmono i T)


/-- **Слабая форма капстоуна (R540)**: та же траекторная
конъюнкция, что `grand_synthesis`, но пункты 2/4 выведены из
локальных пошаговых посылок: вместо глобального риск-телескопа
— покомпонентное покрытие роста риском (`risk_telescope_of_
growth_covered`), вместо плоской передачи qvec-гипотезы —
полы в нуле + монотонность (`qfloor_le_of_monotone`). -/
theorem grand_synthesis_weak
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
    (risk spend : ℕ → ℝ)
    (budget : ℕ → ℝ)
    (qvec : ℕ → Fin 5 → ℝ) (qfloor : Fin 5 → ℝ)
    -- СЛАБЫЕ посылки для пунктов 2/4:
    (hcover : ∀ t ∈ Finset.range T, G t ≤ risk t)
    (hspend : ∀ t ∈ Finset.range T, 0 ≤ spend t)
    (hrisk : ∀ t ∈ Finset.range T, 0 ≤ risk t)
    (hbudget : budget T = budget 0 - ∑ t ∈ Finset.range T, spend t
      ∧ 0 ≤ budget T)
    (hq0 : ∀ i, qfloor i ≤ qvec 0 i)
    (hqmono : ∀ i t, qvec t i ≤ qvec (t + 1) i) :
    C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T
    ∧ C T - C 0 ≤ ∑ t ∈ Finset.range T, risk t
    ∧ budget T ≤ budget 0
      ∧ budget T = budget 0 - ∑ t ∈ Finset.range T, spend t
    ∧ ∀ i, qfloor i ≤ qvec T i := by
  exact grand_synthesis C D G stages T beta kappa gbar rho cbeta k
    hβ hκ hk hD hC hcert hdiv hstep hG hup hdyn hrhogk hbeta'
    hcone0 risk spend budget qvec qfloor
    (risk_telescope_of_growth_covered C G risk T hstep hcover)
    hspend hrisk hbudget
    (qfloor_le_of_monotone qvec qfloor T hq0 hqmono)

end Hagi.Unified
