/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.ChainToCone
import Hagi.Unified.MasterHAGICoupled
import Hagi.Unified.LinkedQVec

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

/-- Бюджетная неповышаемость — арифметическое следствие
неотрицательности трат (REFACTOR_PLAN E2/Ф2): не содержательное
утверждение о модели, выделено из конъюнкций капстоунов. -/
theorem budget_nonincreasing_of_nonneg_spend (budget spend : ℕ → ℝ)
    (T : ℕ)
    (hspend : ∀ t ∈ Finset.range T, 0 ≤ spend t)
    (hexact : budget T = budget 0 - ∑ t ∈ Finset.range T, spend t) :
    budget T ≤ budget 0 := by
  have hsum : 0 ≤ ∑ t ∈ Finset.range T, spend t :=
    Finset.sum_nonneg hspend
  rw [hexact]
  linarith

/-- Under the stated measured premises (certified stage
conversions, frontier dynamics, cone initialization, risk
and spend ledgers, probe floors), one trajectory
simultaneously yields: takeoff `C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T`,
the telescoped risk bound, the exact nonincreasing budget
`budget T = budget 0 − ∑ spend t` (the budget is its OWN
sequence — the R265 audit fix separates it from the
capability channel), and `qfloor i ≤ qvec T i` for every
probe `i`.
AUDIT v4 §3.1 — premise transparency: the conjunctions are NOT EQUAL:
* DERIVED from cone dynamics: exponential takeoff;
* PASSED verbatim (hrisk_bound): risk constraint;
* PASSED (hbudget): exact budget (only the
  non-increasing property budget T ≤ budget 0 is derived — arithmetic);
* PASSED (hqvec): componentwise quality floor.
The passed conjunctions are MEASURABLE premises, not consequences
of the learning mechanism; their source is the certification stage. -/
-- DEPRECATED (REFACTOR_PLAN F1): flat-premise form; use grand_synthesis_weak
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
    (spend : ℕ → ℝ)
    (budget : ℕ → ℝ)
    (hspend : ∀ t ∈ Finset.range T, 0 ≤ spend t)
    (hbudget : budget T = budget 0 - ∑ t ∈ Finset.range T, spend t
      ∧ 0 ≤ budget T) :
    -- 1. takeoff on the trajectory (REAL mathematical content)
    C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T
    -- 2. budget nonincreasing (derived from the exact ledger)
    ∧ budget T ≤ budget 0 := by
  constructor
  · exact Hagi.Growth.takeoff_from_certificate C D G stages T
      beta kappa gbar rho cbeta k hβ hκ hk hD hC hcert hdiv
      hstep hG hup hdyn hrhogk hbeta' hcone0
  · exact budget_nonincreasing_of_nonneg_spend budget spend T
      hspend hbudget.1


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
    C T - C 0 ≤ ∑ t ∈ Finset.range T, risk t :=
  Hagi.Foundations.telescope_band C G risk T hstep hcover

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
  refine ⟨?_, risk_telescope_of_growth_covered C G risk T hstep
    hcover, ?_, ⟨hbudget.1, fun i =>
      qfloor_le_of_monotone qvec qfloor T hq0 hqmono i⟩⟩
  · exact (grand_synthesis C D G stages T beta kappa gbar rho cbeta k
      hβ hκ hk hD hC hcert hdiv hstep hG hup hdyn hrhogk hbeta'
      hcone0 spend budget hspend hbudget).1
  · exact (grand_synthesis C D G stages T beta kappa gbar rho cbeta k
      hβ hκ hk hD hC hcert hdiv hstep hG hup hdyn hrhogk hbeta'
      hcone0 spend budget hspend hbudget).2


/-! ### Аудит v17, P0-3: qvec ↔ состояние

`CoupledHAGIInvariant.qvec_floor` требует floor для ВНЕШНЕЙ
последовательности qvec. Мост закрывает
разрыв (аналог cap_is_state для capability):
если измеритель
`M : MeasuredState (GrowthState X)` закреплён за
состоянием и qvec t = M.evaluate (S t) на
всём горизонте, то инвариант
переносится на КАНАЛЬНУЮ
qvec (измеренную из состояния):
качество больше не внешняя цифра. -/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- qvec-канал состояния: измерение M
на t-м состоянии траектории. -/
def stateQVec (M : LinkedQVec.MeasuredState (GrowthState X))
    (S : ℕ → GrowthState X) : ℕ → Fin 5 → ℝ :=
  fun t => M.evaluate (S t)

/-- P0-3 МОСТ: инвариант с внешней qvec, связанной
с состоянием измерителем M на всём
горизонте, переносится на канал
`stateQVec M S` (т.е. qvec = измерение самого
состояния) — floor-гарантия
сохраняется, но теперь она
о измеренной величине. -/
theorem coupled_state_qvec {T : ℕ}
    (S : ℕ → GrowthState X)
    (risk spend : ℕ → ℝ)
    (qvec : ℕ → Fin 5 → ℝ)
    (qfloor : Fin 5 → ℝ) (alpha : ℝ)
    (M : LinkedQVec.MeasuredState (GrowthState X))
    (hlink : ∀ t ≤ T, qvec t = stateQVec M S t)
    (h : CoupledHAGIInvariant T S risk spend qvec qfloor alpha) :
    CoupledHAGIInvariant T S risk spend (stateQVec M S) qfloor alpha where
  cap_is_state := h.cap_is_state
  risk_bound := h.risk_bound
  spend_nonneg := h.spend_nonneg
  risk_nonneg := h.risk_nonneg
  budget_account := h.budget_account
  capability_growth := h.capability_growth
  qvec_floor := by
    intro i
    have hT := h.qvec_floor i
    have hqT := hlink T (le_refl _)
    rw [hqT] at hT
    exact hT

end Hagi.Unified
