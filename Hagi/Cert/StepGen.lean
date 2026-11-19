/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Cert.Core
import Hagi.Cert.Telescope
import Hagi.Math.Foundations.Telescope

/-!
# General certification kernel (master plan v3 addendum A10, item 2)

Target canonical kernel per A10: ONE certified-step structure with the
remaining step-carriers as views/adapters.  `CertStepGen` generalizes
the frozen `CertStep` (which stays untouched, Freeze-locked) in the two
directions the audit demanded:

* general index type: `TaskId` stays an arbitrary type parameter —
  the hard `Fin 5` floor index of the loop carriers (StepCert,
  NCStepCert) is a CONSUMER instantiation, not a kernel constraint;
* risk-remainder as a FIELD: `riskRem` is explicit data with the split
  law `M.risk s = riskSpend + riskRem`, so adapters no longer pin the
  remainder to zero (the C254 `toKernelCertStep` defect: only the last
  step of a trajectory could spend risk);
* folded delta budget: the fourth resource of `CertStepDelta` (C245,
  A7 — false-commit probability budget) is a kernel field, with the
  same exact telescoping law.

Bridges: `certStep_to_gen` embeds every frozen `CertStep` (at the zero
delta level); `CertStepGen.toCertStep` projects back (dropping the
delta channel); `certStepDelta_to_gen` folds the C245 add-on in.
Composition `CertStepGen.trans` and the drop/delta telescopes mirror
the kernel laws.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Cert

variable {S TaskId : Type*}
variable (M : SystemMetrics S TaskId) (obl : StepObligations TaskId)

/-- General certified progress step (A10 target kernel): positive
drop, real descent, exact budget law, risk law SPLIT into an explicit
spend and an explicit nonzero-allowed REMAINDER field (not pinned to
zero), the folded delta (false-commit probability) budget against an
explicit carrier `deltaLevel`, and floors kept at the post-state. -/
structure CertStepGen (deltaLevel : S → ℝ) (s s' : S) where
  /-- Certified lower bound on the objective drop. -/
  drop : ℝ
  drop_pos : 0 < drop
  descent : M.objective s' ≤ M.objective s - drop
  /-- Compute budget spent by the step. -/
  budgetSpend : ℝ
  budget_next : M.budget s' = M.budget s - budgetSpend
  budget_nonneg : 0 ≤ M.budget s'
  /-- Risk budget spent by the step. -/
  riskSpend : ℝ
  /-- The risk REMAINDER as explicit data (the audit field: adapters
  may keep a nonzero remainder; pinning to zero was the C254 defect). -/
  riskRem : ℝ
  /-- The post-risk level IS the remainder. -/
  risk_next : M.risk s' = riskRem
  /-- The pre-risk level splits exactly into spend plus remainder. -/
  risk_split : M.risk s = riskSpend + riskRem
  risk_nonneg : 0 ≤ riskRem
  /-- Delta budget (false-commit probability) spent by the step. -/
  delta : ℝ
  /-- Exact delta law against the explicit carrier (C245 form). -/
  delta_next : deltaLevel s' = deltaLevel s - delta
  delta_nonneg : 0 ≤ deltaLevel s'
  floorsKept : FloorsKept M obl s'

/-- Derived pointwise bound: the risk spend is bounded by the
available risk level (from the split law and the nonnegative
remainder). -/
theorem CertStepGen.riskBound {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepGen M obl deltaLevel s s') :
    h.riskSpend ≤ M.risk s := by
  have e1 := h.risk_split
  have e2 := h.risk_nonneg
  linarith

/-- Derived pointwise bound: the budget spend is bounded by the
available budget. -/
theorem CertStepGen.budgetBound {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepGen M obl deltaLevel s s') :
    h.budgetSpend ≤ M.budget s :=
  sub_nonneg.mp (by rw [← h.budget_next]; exact h.budget_nonneg)

/-! ## Bridges to the frozen kernel -/

/-- Embedding: every frozen `CertStep` is a `CertStepGen` at the zero
delta level, with the risk remainder read off the post-state (the
frozen kernel's implicit remainder made explicit).  The frozen
`CertStep` itself is untouched (Freeze). -/
def certStep_to_gen {s s' : S} (h : CertStep M obl s s') :
    CertStepGen M obl (fun _ => 0) s s' where
  drop := h.drop
  drop_pos := h.drop_pos
  descent := h.descent
  budgetSpend := h.budgetSpend
  budget_next := h.budget_next
  budget_nonneg := h.budget_nonneg
  riskSpend := h.riskSpend
  riskRem := M.risk s'
  risk_next := rfl
  risk_split := by
    have e := h.risk_next
    linarith
  risk_nonneg := h.risk_nonneg
  delta := 0
  delta_next := by simp
  delta_nonneg := by norm_num
  floorsKept := h.floorsKept

/-- Projection: a `CertStepGen` is a frozen `CertStep` — the risk law
collapses to the one-equation form by the split law, and the delta
channel is dropped. -/
def CertStepGen.toCertStep {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepGen M obl deltaLevel s s') :
    CertStep M obl s s' where
  drop := h.drop
  drop_pos := h.drop_pos
  descent := h.descent
  budgetSpend := h.budgetSpend
  budget_next := h.budget_next
  budget_nonneg := h.budget_nonneg
  riskSpend := h.riskSpend
  risk_next := by
    have e1 := h.risk_next
    have e2 := h.risk_split
    linarith
  risk_nonneg := by rw [h.risk_next]; exact h.risk_nonneg
  floorsKept := h.floorsKept

/-- Fold-in of the C245 fourth-resource add-on: every `CertStepDelta`
is a `CertStepGen` at the same delta level (risk remainder read off
the post-state).  `CertStepDelta` stays verbatim (Freeze). -/
def certStepDelta_to_gen {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepDelta M obl deltaLevel s s') :
    CertStepGen M obl deltaLevel s s' where
  drop := h.step.drop
  drop_pos := h.step.drop_pos
  descent := h.step.descent
  budgetSpend := h.step.budgetSpend
  budget_next := h.step.budget_next
  budget_nonneg := h.step.budget_nonneg
  riskSpend := h.step.riskSpend
  riskRem := M.risk s'
  risk_next := rfl
  risk_split := by
    have e := h.step.risk_next
    linarith
  risk_nonneg := h.step.risk_nonneg
  delta := h.delta
  delta_next := h.delta_next
  delta_nonneg := h.delta_nonneg
  floorsKept := h.step.floorsKept

/-! ## Composition -/

/-- Composition of two general steps against the same metrics,
obligations and delta level: drops, spends and deltas add; the risk
split of the composite has the SECOND step's remainder (the first
step's remainder is exactly the second step's pre-risk level). -/
def CertStepGen.trans {deltaLevel : S → ℝ} {s₁ s₂ s₃ : S}
    (h₁ : CertStepGen M obl deltaLevel s₁ s₂)
    (h₂ : CertStepGen M obl deltaLevel s₂ s₃) :
    CertStepGen M obl deltaLevel s₁ s₃ where
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
  riskRem := h₂.riskRem
  risk_next := h₂.risk_next
  risk_split := by
    have e₁ := h₁.risk_split
    have e₂ := h₂.risk_split
    have e₁' := h₁.risk_next
    linarith
  risk_nonneg := h₂.risk_nonneg
  delta := h₁.delta + h₂.delta
  delta_next := by
    rw [h₂.delta_next, h₁.delta_next]
    ring
  delta_nonneg := h₂.delta_nonneg
  floorsKept := h₂.floorsKept

/-! ## Telescopes -/

/-! ### AdditiveLedger инстансы (A18.3): CertStepGen-каналы -/

/-- `CertStepGen`: objective-канал (declared drop, ≤-закон). -/
instance certStepGen_objective {deltaLevel : S → ℝ} :
    AdditiveLedger S M.objective (CertStepGen M obl deltaLevel) where
  spend c := c.drop
  step_descend c := c.descent

/-- `CertStepGen`: δ-канал (точный закон `delta_next`). -/
instance certStepGen_delta {deltaLevel : S → ℝ} :
    ExactAdditiveLedger S deltaLevel (CertStepGen M obl deltaLevel) where
  spend c := c.delta
  step_exact c := c.delta_next

/-- `CertStepGen`: budget-канал (точный закон `budget_next`). -/
instance certStepGen_budget {deltaLevel : S → ℝ} :
    ExactAdditiveLedger S M.budget (CertStepGen M obl deltaLevel) where
  spend c := c.budgetSpend
  step_exact c := c.budget_next

/-- `CertStepGen`: risk-канал (точный закон из split: post-risk =
remainder, pre-risk = spend + remainder). -/
instance certStepGen_risk {deltaLevel : S → ℝ} :
    ExactAdditiveLedger S M.risk (CertStepGen M obl deltaLevel) where
  spend c := c.riskSpend
  step_exact c := by rw [c.risk_next, c.risk_split]; ring

/-- Drop telescope for the general kernel: the terminal objective is
bounded by the initial objective minus the sum of certified drops. -/
theorem trajectory_telescope_gen (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, CertStepGen M obl deltaLevel (t j) (t (j + 1))) :
    M.objective (t n) ≤ M.objective (t 0)
      - ∑ j ∈ Finset.range n, (steps j).drop :=
  Hagi.Cert.additive_ledger_telescope (level := M.objective) n t steps

/-- Delta telescope for the general kernel
sum of per-step false-commit budgets is bounded by the initial delta
level, provided the initial level is nonnegative (honest explicit
premise). -/
theorem delta_telescope_gen (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S)
    (h0 : 0 ≤ deltaLevel (t 0))
    (steps : ∀ j : ℕ, CertStepGen M obl deltaLevel (t j) (t (j + 1))) :
    ∑ j ∈ Finset.range n, (steps j).delta ≤ deltaLevel (t 0) := by
  have hnn : 0 ≤ deltaLevel (t n) := by
    match n with
    | 0 => exact h0
    | m + 1 => exact (steps m).delta_nonneg
  exact Hagi.Cert.additive_ledger_telescope_floor
    (level := deltaLevel) n t hnn steps

/-- Risk telescope for the general kernel: the sum of per-step risk
spends is bounded by the initial risk level (remainder field makes
the accounting explicit; no zero-pinning anywhere).  The initial
level's nonnegativity is an honest explicit premise (per-step spends
are unconstrained in sign, so it is not derivable). -/
theorem risk_telescope_gen (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S)
    (h0 : 0 ≤ M.risk (t 0))
    (steps : ∀ j : ℕ, CertStepGen M obl deltaLevel (t j) (t (j + 1))) :
    ∑ j ∈ Finset.range n, (steps j).riskSpend ≤ M.risk (t 0) := by
  have hnn : 0 ≤ M.risk (t n) := by
    match n with
    | 0 => exact h0
    | m + 1 =>
      have h := (steps m).risk_nonneg
      rw [(steps m).risk_next]
      exact h
  exact Hagi.Cert.additive_ledger_telescope_floor
    (level := M.risk) n t hnn steps

/-! ## Bounded variant (A14 QW3, C344): ≤-law constructor

The exact kernel demands EQUALITY consumption laws; legacy loop
carriers (e.g. `StepCert`) only certify the ≤ law (hdec).  The
bounded variant mirrors the carrier fields with ≤ laws, and the
bridge `CertStepGenBounded.toExact` upgrades it to the exact
kernel PREMISE-FREE: the exact spends are DEFINED as the actual
state differences, so the equality holds by construction. -/

/-- Bounded certified progress step (≤-law lens on the gen
kernel): positive drop, ≤ descent, ≤ budget/risk/delta
consumption laws with nonnegative post-levels, floors kept.  The
remainders are the post-state readouts themselves (no separate
fields). -/
structure CertStepGenBounded (deltaLevel : S → ℝ) (s s' : S) where
  /-- Certified lower bound on the objective drop. -/
  drop : ℝ
  drop_pos : 0 < drop
  descent : M.objective s' ≤ M.objective s - drop
  /-- Declared compute-budget spend (a lower commitment). -/
  budgetSpend : ℝ
  budget_next_le : M.budget s' ≤ M.budget s - budgetSpend
  budget_nonneg : 0 ≤ M.budget s'
  /-- Declared risk-budget spend. -/
  riskSpend : ℝ
  risk_next_le : M.risk s' ≤ M.risk s - riskSpend
  risk_nonneg : 0 ≤ M.risk s'
  /-- Declared delta (false-commit probability) spend. -/
  delta : ℝ
  delta_next_le : deltaLevel s' ≤ deltaLevel s - delta
  delta_nonneg : 0 ≤ deltaLevel s'
  floorsKept : FloorsKept M obl s'

/-- The declared budget spend is bounded by the DEFINITIONAL spend
(the actual state difference) — honesty: upgrading to the exact
kernel may spend MORE than the declared lower commitment. -/
theorem CertStepGenBounded.budgetSpend_le_actual
    {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepGenBounded M obl deltaLevel s s') :
    h.budgetSpend ≤ M.budget s - M.budget s' := by
  have e := h.budget_next_le
  have e' := h.budget_nonneg
  linarith

/-- The declared risk spend is bounded by the definitional spend. -/
theorem CertStepGenBounded.riskSpend_le_actual
    {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepGenBounded M obl deltaLevel s s') :
    h.riskSpend ≤ M.risk s - M.risk s' := by
  have e := h.risk_next_le
  have e' := h.risk_nonneg
  linarith

/-- The declared delta spend is bounded by the definitional spend. -/
theorem CertStepGenBounded.delta_le_actual
    {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepGenBounded M obl deltaLevel s s') :
    h.delta ≤ deltaLevel s - deltaLevel s' := by
  have e := h.delta_next_le
  have e' := h.delta_nonneg
  linarith

/-- PREMISE-FREE bounded→exact bridge (the QW3 key): from a bounded
certificate one GETS an exact `CertStepGen` with NO extra
witnesses — the exact spends are DEFINED as the actual state
differences (`budgetSpend := M.budget s - M.budget s'` etc.), so
the equalities hold by construction (the hbudeq problem of the
premise-form adapters dissolves). -/
def CertStepGenBounded.toExact {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepGenBounded M obl deltaLevel s s') :
    CertStepGen M obl deltaLevel s s' where
  drop := h.drop
  drop_pos := h.drop_pos
  descent := h.descent
  budgetSpend := M.budget s - M.budget s'
  budget_next := by
    show M.budget s' = M.budget s - (M.budget s - M.budget s')
    rw [sub_sub_cancel]
  budget_nonneg := h.budget_nonneg
  riskSpend := M.risk s - M.risk s'
  riskRem := M.risk s'
  risk_next := rfl
  risk_split := by
    show M.risk s = (M.risk s - M.risk s') + M.risk s'
    rw [sub_add_cancel]
  risk_nonneg := h.risk_nonneg
  delta := deltaLevel s - deltaLevel s'
  delta_next := by
    show deltaLevel s'
      = deltaLevel s - (deltaLevel s - deltaLevel s')
    rw [sub_sub_cancel]
  delta_nonneg := h.delta_nonneg
  floorsKept := h.floorsKept

/-! ### Bounded telescopes (≤, level form) -/

/-- Drop telescope, bounded form: the terminal objective is ≤ the
initial objective minus the sum of declared drops. -/
theorem trajectory_telescope_gen_bounded (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, CertStepGenBounded M obl deltaLevel (t j) (t (j + 1))) :
    M.objective (t n) ≤ M.objective (t 0)
      - ∑ j ∈ Finset.range n, (steps j).drop := by
  exact Hagi.Foundations.telescope_le_sub
    (f := fun k => M.objective (t k))
    (c := fun j => (steps j).drop)
    (fun j _ => (steps j).descent)

/-- Budget telescope, bounded form: the terminal budget level is ≤
the initial level minus the sum of declared spends. -/
theorem budget_telescope_gen_bounded (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, CertStepGenBounded M obl deltaLevel (t j) (t (j + 1))) :
    M.budget (t n) ≤ M.budget (t 0)
      - ∑ j ∈ Finset.range n, (steps j).budgetSpend := by
  exact Hagi.Foundations.telescope_le_sub
    (f := fun k => M.budget (t k))
    (c := fun j => (steps j).budgetSpend)
    (fun j _ => (steps j).budget_next_le)

/-- Risk telescope, bounded form: the terminal risk level is ≤ the
initial level minus the sum of declared risk spends. -/
theorem risk_telescope_gen_bounded (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, CertStepGenBounded M obl deltaLevel (t j) (t (j + 1))) :
    M.risk (t n) ≤ M.risk (t 0)
      - ∑ j ∈ Finset.range n, (steps j).riskSpend := by
  exact Hagi.Foundations.telescope_le_sub
    (f := fun k => M.risk (t k))
    (c := fun j => (steps j).riskSpend)
    (fun j _ => (steps j).risk_next_le)

/-- Delta telescope, bounded form: the terminal delta level is ≤
the initial level minus the sum of declared deltas. -/
theorem delta_telescope_gen_bounded (deltaLevel : S → ℝ)
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, CertStepGenBounded M obl deltaLevel (t j) (t (j + 1))) :
    deltaLevel (t n) ≤ deltaLevel (t 0)
      - ∑ j ∈ Finset.range n, (steps j).delta := by
  exact Hagi.Foundations.telescope_le_sub
    (f := fun k => deltaLevel (t k))
    (c := fun j => (steps j).delta)
    (fun j _ => (steps j).delta_next_le)

/-! ## TransitionStep lift (C290, kernel-unification closeout)

The frozen `TransitionStep` (progress | hold) is lifted to the gen
kernel through the C278 embedding `certStep_to_gen`.  A hold is
honestly `none`: the kernel demands a POSITIVE certified drop and a
hold makes no progress claim — faking a zero-drop certificate would
be a defect, so the bridge is Option-valued (the C280 StepProvider
precedent: Option = "no certified step from here").  The trajectory
composition lemma links OLD progress trajectories to the EXISTING
gen telescope (C278 already provides `trajectory_telescope_gen`;
nothing is re-proved here). -/

/-- Bridge embedding the frozen `TransitionStep` into the gen
kernel at the zero delta level: progress lands on the C278
`certStep_to_gen` embedding, hold honestly yields `none`. -/
def transitionStep_to_gen {s s' : S}
    (h : TransitionStep M obl s s') :
    Option (CertStepGen M obl (fun _ => 0) s s') :=
  match h with
  | .progress c => some (certStep_to_gen M obl c)
  | .hold _ => none

/-- The progress case of the bridge lands EXACTLY on the C278
embedding (the bridge composes with `certStep_to_gen`; no third
adapter is introduced). -/
theorem transitionStep_to_gen_progress {s s' : S}
    (c : CertStep M obl s s') :
    transitionStep_to_gen M obl (TransitionStep.progress c)
      = some (certStep_to_gen M obl c) := rfl

/-- Extract form for consumers (premise-form, the C278 bridge
pattern): a `TransitionStep` witnessed as progress carries the gen
certificate obtained through the existing embedding. -/
theorem transitionStep_progress_to_gen {s s' : S}
    (h : TransitionStep M obl s s') (c : CertStep M obl s s')
    (hc : h = TransitionStep.progress c) :
    transitionStep_to_gen M obl h = some (certStep_to_gen M obl c) := by
  rw [hc]
  exact transitionStep_to_gen_progress M obl c

/-- Composition lemma linking old trajectories through the bridge to
the EXISTING gen-kernel telescope (C278 `trajectory_telescope_gen`):
a trajectory of `TransitionStep`s in which every step is witnessed
progress satisfies the gen telescope bound.  The all-progress premise
is honest — a hold makes no drop claim and cannot appear in a
progress telescope.  No new telescope is proved; this is transport
through the bridge. -/
theorem trajectory_telescope_progress_bridge
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, TransitionStep M obl (t j) (t (j + 1)))
    (hprog : ∀ j : ℕ, ∃ c : CertStep M obl (t j) (t (j + 1)),
      steps j = TransitionStep.progress c) :
    M.objective (t n) ≤ M.objective (t 0)
      - ∑ j ∈ Finset.range n,
        (certStep_to_gen M obl (Classical.choose (hprog j))).drop := by
  exact trajectory_telescope_gen M obl (fun _ => 0) n t
    (fun j => certStep_to_gen M obl (Classical.choose (hprog j)))

/-! ### Journal bridge (C449, A19.2): gen kernel → StepRecord -/

/-- Журнальная запись gen-шага (C449): drop-ядро + траты бюджет/риск
и δ-канал как телеметрия. Законы потребления остаются в `CertStepGen`. -/
def CertStepGen.toRecord {deltaLevel : S → ℝ} {s s' : S}
    (c : CertStepGen M obl deltaLevel s s') :
    StepRecord M.objective s s' where
  drop := c.drop
  drop_pos := c.drop_pos
  descent := c.descent
  budgetSpend := c.budgetSpend
  riskSpend := c.riskSpend
  delta := c.delta

end Hagi.Cert
