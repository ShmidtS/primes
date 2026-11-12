/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# Canonical certification kernel (master plan v3, Track S1+S2)

Thin, dependency-free interface for certified trajectory steps.

`SystemMetrics` bundles the system readouts (objective, risk, budget,
task tag) as functions of an abstract state.  `StepObligations` is a
separate structure carrying the certified lower obligations for the
objective.  A `CertStep` is a certified progress step: a positive
certified drop, real descent from execution, exact budget/risk
consumption laws with nonnegative remainders, and floors kept at the
post-state.  A `HoldStep` makes no progress claim and is always
available at a floor-keeping state (`HoldStep.id`).  A
`TransitionStep` is either certified progress or a hold.

Composition: `CertStep.trans` composes two steps against the SAME
obligations; `CertStep.trans'` is the two-obligation strengthening
where the second step is certified against pointwise stronger
floors.  The telescope laws bound the terminal objective by the
initial objective minus the sum of certified drops.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Cert

/-! ## S1: metrics + obligations -/

variable (S : Type*) (TaskId : Type*)

/-- Canonical system readouts: objective, risk and budget levels as
functions of the state, plus the task tag. -/
structure SystemMetrics where
  objective : S → ℝ
  risk : S → ℝ
  budget : S → ℝ
  task : S → TaskId

/-- Per-step obligations: a separate structure.  `floor t` is the
certified lower obligation for the objective at task tag `t`. -/
structure StepObligations (T : Type*) where
  floor : T → ℝ

variable {S TaskId}

/-- Floor contract: the objective at `s` meets every obligation. -/
def FloorsKept (M : SystemMetrics S TaskId) (obl : StepObligations TaskId)
    (s : S) : Prop :=
  ∀ t, obl.floor t ≤ M.objective s

/-! ## S2: cert kernel -/

variable (M : SystemMetrics S TaskId) (obl : StepObligations TaskId)

/-- Certified progress step: positive drop, real descent from
execution, budget/risk spend deducted from the running levels with
nonnegative remainders, floors kept at the post-state. -/
structure CertStep (s s' : S) where
  drop : ℝ
  drop_pos : 0 < drop
  descent : M.objective s' ≤ M.objective s - drop
  budgetSpend : ℝ
  budget_next : M.budget s' = M.budget s - budgetSpend
  budget_nonneg : 0 ≤ M.budget s'
  riskSpend : ℝ
  risk_next : M.risk s' = M.risk s - riskSpend
  risk_nonneg : 0 ≤ M.risk s'
  floorsKept : FloorsKept M obl s'

/-- Derived pointwise bound: budget spend is bounded by the
available budget. -/
theorem CertStep.budgetBound {s s' : S} (h : CertStep M obl s s') :
    h.budgetSpend ≤ M.budget s :=
  sub_nonneg.mp (by rw [← h.budget_next]; exact h.budget_nonneg)

/-- Derived pointwise bound: risk spend is bounded by the available
risk level. -/
theorem CertStep.riskBound {s s' : S} (h : CertStep M obl s s') :
    h.riskSpend ≤ M.risk s :=
  sub_nonneg.mp (by rw [← h.risk_next]; exact h.risk_nonneg)

/-- Hold step: no progress claim, state unchanged, floors kept. -/
structure HoldStep (s s' : S) where
  hold : s' = s
  floorsKept : FloorsKept M obl s'

/-- A hold step is always available at a floor-keeping state. -/
theorem HoldStep.id (s : S) (h : FloorsKept M obl s) : HoldStep M obl s s where
  hold := rfl
  floorsKept := h

/-- One trajectory step: certified progress or a hold (a hold makes
no progress claim and spends nothing). -/
inductive TransitionStep (M : SystemMetrics S TaskId) (obl : StepObligations TaskId)
    (s s' : S) where
  | progress : CertStep M obl s s' → TransitionStep M obl s s'
  | hold : HoldStep M obl s s' → TransitionStep M obl s s'

/-! ## Composition -/

/-- Composition of two certified steps against the same obligations:
drops add, spends add, floors are carried by the second step. -/
def CertStep.trans {S : Type*} {TaskId : Type*}
    {M : SystemMetrics S TaskId} {obl : StepObligations TaskId}
    {s₁ s₂ s₃ : S}
    (h₁ : CertStep M obl s₁ s₂)
    (h₂ : CertStep M obl s₂ s₃) :
    CertStep M obl s₁ s₃ where
  drop := h₁.drop + h₂.drop
  drop_pos := add_pos h₁.drop_pos h₂.drop_pos
  descent := by
    have e₁ := h₁.descent
    have e₂ := h₂.descent
    linarith
  budgetSpend := h₁.budgetSpend + h₂.budgetSpend
  budget_next := by
    rw [h₂.budget_next, h₁.budget_next]
    ring
  budget_nonneg := h₂.budget_nonneg
  riskSpend := h₁.riskSpend + h₂.riskSpend
  risk_next := by
    rw [h₂.risk_next, h₁.risk_next]
    ring
  risk_nonneg := h₂.risk_nonneg
  floorsKept := h₂.floorsKept

/-- Two-obligation strengthening of `CertStep.trans`: the second
step may be certified against pointwise stronger obligations `obl₂`
while the composite is certified against `obl₁`. -/
def CertStep.trans' {S : Type*} {TaskId : Type*}
    {M : SystemMetrics S TaskId} {obl₁ obl₂ : StepObligations TaskId}
    {s₁ s₂ s₃ : S}
    (h₁ : CertStep M obl₁ s₁ s₂)
    (h₂ : CertStep M obl₂ s₂ s₃)
    (h_floor : ∀ t, obl₁.floor t ≤ obl₂.floor t) :
    CertStep M obl₁ s₁ s₃ where
  drop := h₁.drop + h₂.drop
  drop_pos := add_pos h₁.drop_pos h₂.drop_pos
  descent := by
    have e₁ := h₁.descent
    have e₂ := h₂.descent
    linarith
  budgetSpend := h₁.budgetSpend + h₂.budgetSpend
  budget_next := by
    rw [h₂.budget_next, h₁.budget_next]
    ring
  budget_nonneg := h₂.budget_nonneg
  riskSpend := h₁.riskSpend + h₂.riskSpend
  risk_next := by
    rw [h₂.risk_next, h₁.risk_next]
    ring
  risk_nonneg := h₂.risk_nonneg
  floorsKept := fun t => le_trans (h_floor t) (h₂.floorsKept t)

/-! ## Telescope -/

/-- Trajectory telescope over `n` certified steps: the objective at
the terminal state is bounded by the initial objective minus the
sum of all certified drops. -/
theorem trajectory_telescope {S : Type*} {TaskId : Type*}
    {M : SystemMetrics S TaskId} {obl : StepObligations TaskId}
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, CertStep M obl (t j) (t (j + 1))) :
    M.objective (t n) ≤ M.objective (t 0)
      - ∑ j ∈ Finset.range n, (steps j).drop := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e := (steps n).descent
    simp only [Finset.sum_range_succ]
    linarith

/-- `Fin n`-indexed corollary of `trajectory_telescope`: the same
bound for a step supply indexed by `Fin n`. -/
theorem trajectory_telescope_fin {S : Type*} {TaskId : Type*}
    {M : SystemMetrics S TaskId} {obl : StepObligations TaskId}
    {n : ℕ} (t : ℕ → S)
    (steps : ∀ j : Fin n, CertStep M obl (t j) (t (j + 1))) :
    M.objective (t n) ≤ M.objective (t 0) - ∑ j : Fin n, (steps j).drop := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e2 : M.objective (t (n + 1)) ≤ M.objective (t n)
        - (steps (Fin.last n)).drop := (steps (Fin.last n)).descent
    have ihr := ih (fun j => steps j.castSucc)
    rw [Fin.sum_univ_castSucc]
    linarith

end Hagi.Cert
