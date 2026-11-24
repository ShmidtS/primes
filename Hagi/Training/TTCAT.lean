/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Training.AlternatingJoint
import Hagi.Training.MacroStatCert
import Hagi.Theory.MasterTheorem
import Hagi.Theory.MasterEF

/-!
# TT-CAT — the joint controller theorem (A16 two-level training)

The FINAL composition of the TT-CAT controller: the alternating
micro level (phases + gate-protected boundaries
derived damages), the admission events, and the macro
Commit/Hold/Rollback checkpoints (adaptivity route) in
ONE record, and ONE joint theorem `ttcat_complete`: with high
probability — the union over ALL failure events (micro δ's +
admission α's + macro α's, one explicit Σ) — EITHER every level ran
correctly and the trajectory satisfies the master bound with the
DERIVED damages plus the budget plus the EF
endpoint, OR a rollback occurred and the last committed
checkpoint of the SAME trajectory is restored. This is
the project's ultimate certified-or-safe statement.

## Mapping to the A16 TT-CAT spec sequence (line by line)

Micro loop (runs T steps, extractor frozen within phases):
1. forward pass on the frozen CR-MSM block — `alt.headCerts`
   (`CRMSMStep`);
2. certified head step at the frozen extractor — the universal
   step inside `HeadPhase` (`head_phase_certified`);
3. error-feedback quantized update with residual carry — the EF
   channel, whose endpoint bound is `master_trajectory_bound_ef_closed`
carried as the EF conjunct of `ttcat_complete`;
4. compression penalty accounting (form `2·L_lip·ε_q`) —
   `alt.stepPenalty'` (master certificates);
5. resource ledger spend of each step — `master.stepCost`,
   summed against B by the budget conjunct (route:
   `MasterBudgetCert` premise, `masterBudgetCert_of_resource_ledger`
   construction);
6. rare extractor boundary every K steps through the admission
   gate with the DERIVED damage `2·headLip·D` — `alt.boundaries`
   (`DerivedExtractorBoundary`).

Macro loop (every K steps, checkpoint windows `cp m → cp m + 1`):
1. the window closes at a scheduled checkpoint index — `cp`/`cp_lt`;
2. quality estimate ΔQ̂_K with the TYPED confidence radius —
   `macros m`.deltaQ / r_conf;
3. the LCB/UCB three-way decision commit/hold/rollback —
   `macros m`.decision pinned `decide_ok`;
4. checkpoint bookkeeping: the rollback target is a PREVIOUSLY
   EXECUTED window boundary of the same trajectory (or the initial
   state) — `checkpoint_ok`;
5. budget accounting against B — the budget conjunct;
6. anytime-valid α accounting, adaptive route included — the macro
   α family of the union bound (discharge route `commit_sound` /
 `adaptive_commit_bridge`).

## What the joint theorem adds beyond the conjunction of parts

The conjunction ∧ ∧ permits cross-level
inconsistency: a macro COMMIT recorded on states the micro
trajectory never visited, or a ROLLBACK to a "checkpoint" outside
the executed trajectory. The controller's hversion equations
(`macro_before`/`macro_after`, the mechanism) pin every macro
certificate onto the SAME states the alternating trajectory
certified, and `checkpoint_ok` pins the rollback target to the same
trajectory — mixing is not expressible in the type.
`ttcat_commit_installs` and `ttcat_rollback_preserves` extract this
as theorems: a macro commit installs EXACTLY the micro trajectory's
window-end state; a rollback restores EXACTLY a previously executed
window boundary (total-state restore).

## Honesty pins

- **Measure premises are PREMISE-form** (the repo convention): the per-event
  level bounds `hMicro`/`hAdm`/`hMacro`
  are the consumer's to discharge. Discharge routes, CITED not
  restated (statement-duplication discipline): macro α's
  `commit_sound` (single window) `adaptive_commit_bridge`
  (adaptive family, Σ α, covers any selection schedule); admission
  α's `admit_sound`. The e-process premises of those
  routes are conditional (fresh-draw) — full reuse is NOT covered
  (the negative pin inherits).
- **The decision fields are ω-INDEPENDENT** (the convention):
  the controller records ONE decision sequence; only the
  goodGain/micro-realization predicates are ω-dependent.
- **`master` is the BUDGET-carrying view** of the same states
  (`masterStates`); drop-channel coherence between the master view
  and the alternating view is NOT claimed (the two views share
  states and cost channel only).
- **The EF conjunct is a PACKAGED endpoint bound** over an
  explicit `EFTrajectory` binder on an arbitrary normed space W;
  the carrier bridge (head iterate ↔ canonical states) remains the
 pin — no fabricated link premise.
- **microBad is the whp channel, premise-form**: microBad j ω
  is the consumer's "the realized descent of micro step j failed
  its certificate" predicate (the `master_union_bound` δ_t
  convention).
- **Derived damages keep the pin**: the fullObjective channel
  of a boundary remains premise-form with the DERIVED constant
  `2·headLip·D`.

Layer decision: Training (8), same as AlternatingJoint/MacroStatCert
— the module must see the alternating trajectory (8), the macro
certificates (8) and the theory (7); only layer 8 can.
-/

set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open Hagi.State Hagi.Theory Hagi.Training Hagi.Step.ErrorFeedback

namespace Hagi.Training.TTCAT

/-! ## The controller record -/

variable {Θ X V F : Type} [NormedAddCommGroup X] [NormedAddCommGroup F]
variable [Fintype V] [Nonempty V] {mE rE dE n a e q r c k : ℕ}

/-- THE TT-CAT controller (A16 two-level loop, one record): the
alternating micro trajectory (`alt`, derived variant — head
phases at a frozen extractor, admission-gated boundaries with
derived damages, holds), the budget-carrying master view of the
SAME states (`master` + `masterStates`), the budget premise B
(`MasterBudgetCert`; construction route), the macro
checkpoint windows (`cp`), and the macro certificates —
pinned by hversion equations onto the alternating trajectory's
states (the mechanism), with the rollback target pinned to a
previously executed window boundary of the SAME trajectory. -/
structure TTCATController (T M : ℕ) where
  /-- The alternating micro trajectory (derived). -/
  alt : Hagi.Training.AlternatingJoint.DerivedAlternatingTrajectory
    (n := n) (a := a) (e := e) (q := q) (r := r) (c := c) (k := k)
    (Θ := Θ) (X := X) (V := V) (F := F) (mE := mE) (rE := rE) (dE := dE) T
  /-- The budget-carrying master view. -/
  master : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
    (r := r) (c := c) (k := k) T
  /-- The master view runs on the SAME states as the alternating
  trajectory (version coherence of the budget channel). -/
  masterStates : master.states = alt.states
  /-- The budget level B. -/
  B : ℝ
  /-- The budget premise certificate (construction route
  `masterBudgetCert_of_resource_ledger`). -/
  budget : MasterBudgetCert T master B
  /-- The macro checkpoint window starts. -/
  cp : Fin M → ℕ
  /-- Every window is inside the trajectory. -/
  cp_lt : ∀ m : Fin M, cp m + 1 ≤ T
  /-- The macro certificates, one per checkpoint window. -/
  macros : Fin M → MacroStatCert (CanonicalTrainState n a e q r c k)
    fullObjective
  /-- hversion: macro window m starts at the alternating
  trajectory's `cp m` state (the mechanism — no cross-level
  state mixing). -/
  macro_before : ∀ m : Fin M, (macros m).sBefore = alt.states (cp m)
  /-- hversion: macro window m ends at the alternating
  trajectory's `cp m + 1` state. -/
  macro_after : ∀ m : Fin M, (macros m).sAfter = alt.states (cp m + 1)
  /-- The rollback target coherence: on a rollback the restored
  checkpoint is either a PREVIOUSLY EXECUTED macro-window boundary
  of the SAME trajectory, or the initial state — the last committed
  checkpoint is always a state the micro level actually visited. -/
  checkpoint_ok : ∀ m : Fin M,
    (macros m).decision = MacroDecision.rollback →
    (∃ m' : Fin M, (m' : ℕ) < (m : ℕ) ∧
      (macros m).sCheckpoint = alt.states (cp m'))
    ∨ (macros m).sCheckpoint = alt.states 0

/-! ## Cross-level coherence (what the composition adds) -/

/-- A macro COMMIT installs EXACTLY the micro trajectory's
window-end state — through the hversion equation `macro_after`, the
macro decision and the micro trajectory provably act on the SAME
states, not on two separately-versioned copies (
mechanism, extracted as a theorem). -/
theorem ttcat_commit_installs (T M : ℕ)
    (ctl : TTCATController (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T M)
    (m : Fin M) (h : (ctl.macros m).decision = MacroDecision.commit) :
    applyDecision (objective := fullObjective) (ctl.macros m)
      = ctl.alt.states (ctl.cp m + 1) := by
  simp only [applyDecision, h]
  rw [ctl.macro_after m]
  rfl

/-- A macro ROLLBACK restores the last committed checkpoint
(total-state restore `rollback_sound` /) AND the restored
state is a previously executed window boundary of the SAME
trajectory (or the initial state) — the cross-level rollback
coherence: the controller can never land on a state the micro level
never certified. -/
theorem ttcat_rollback_preserves (T M : ℕ)
    (ctl : TTCATController (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T M)
    (m : Fin M) (h : (ctl.macros m).decision = MacroDecision.rollback) :
    applyDecision (objective := fullObjective) (ctl.macros m)
      = (ctl.macros m).sCheckpoint
    ∧ ((∃ m' : Fin M, (m' : ℕ) < (m : ℕ) ∧
        (ctl.macros m).sCheckpoint = ctl.alt.states (ctl.cp m'))
      ∨ (ctl.macros m).sCheckpoint = ctl.alt.states 0) :=
  ⟨rollback_sound _ h, ctl.checkpoint_ok m h⟩

/-! ## The failure events and the good outcome -/

/-- The TT-CAT failure events on ONE probability space Ω
(heterogeneous levels normalized to Ω-predicates; decisions are
ω-independent record fields, the convention): the micro
realization failures (`microBad` — the whp channel,
premise-form), the false admissions (`admBad`), the false
commits (`macroBad`), with their explicit levels δ,
α_adm, α_macro. -/
structure TTCATEvents (T M : ℕ) (Ω : Type*) where
  /-- Micro step j's realized descent failed its certificate (the
 whp δ-channel, premise-form consumer predicate). -/
  microBad : ℕ → Ω → Prop
  /-- Boundary i was a false admission (route: `admit_sound`). -/
  admBad : ℕ → Ω → Prop
  /-- Macro window m was a false commit (route:
  `commit_sound` / `adaptive_commit_bridge`). -/
  macroBad : ℕ → Ω → Prop
  /-- The micro failure levels δ_j. -/
  δ : ℕ → ℝ
  /-- The admission failure levels α_adm,i. -/
  α_adm : ℕ → ℝ
  /-- The macro failure levels α_macro,m. -/
  α_macro : ℕ → ℝ

/-- The good outcome of the TT-CAT controller at ω: EITHER no
rollback was ever decided and every level ran correctly (no false
commit, no false admission, no micro realization failure), OR a
rollback occurred and the last committed checkpoint is preserved
(the deterministic + `checkpoint_ok` coherence). The
trajectory/budget/EF payload is deterministic and carried by
`ttcat_complete` as separate conjuncts. -/
def TTCATGood (T M : ℕ)
    (ctl : TTCATController (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T M)
    (ev : TTCATEvents T M Ω) (ω : Ω) : Prop :=
  ((∀ m : Fin M, (ctl.macros m).decision ≠ MacroDecision.rollback
      ∧ ¬ ev.macroBad m ω)
    ∧ (∀ i : Fin T, ¬ ev.admBad i ω)
    ∧ ∀ j : Fin T, ¬ ev.microBad j ω)
  ∨ ∃ m : Fin M, (ctl.macros m).decision = MacroDecision.rollback
    ∧ ((∃ m' : Fin M, (m' : ℕ) < (m : ℕ) ∧
        (ctl.macros m).sCheckpoint = ctl.alt.states (ctl.cp m'))
      ∨ (ctl.macros m).sCheckpoint = ctl.alt.states 0)

/-- The heterogeneous failure-event family over ONE index type
`Fin T ⊕ (Fin T ⊕ Fin M)` — the union-bound normalization of the
micro/admission/macro levels to one probability-space statement. -/
def ttcatFailSet {T M : ℕ} {Ω : Type*} (ev : TTCATEvents T M Ω)
    (i : Fin T ⊕ (Fin T ⊕ Fin M)) : Set Ω :=
  {ω | Sum.elim (fun j : Fin T => ev.microBad j)
    (Sum.elim (fun i : Fin T => ev.admBad i)
      (fun m : Fin M => ev.macroBad m)) i ω}

/-- The bad outcome is covered by the heterogeneous union: if the
good outcome fails, either a rollback occurred (then the good
rollback disjunct would hold — contradiction), or some micro /
admission / macro failure event fired. -/
theorem ttcat_bad_subset_fail (T M : ℕ)
    (ctl : TTCATController (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T M)
    {Ω : Type*} (ev : TTCATEvents T M Ω) (ω : Ω)
    (hng : ¬ TTCATGood T M ctl ev ω) :
    ω ∈ ⋃ i : Fin T ⊕ (Fin T ⊕ Fin M), ttcatFailSet ev i := by
  by_cases hr : ∃ m : Fin M,
      (ctl.macros m).decision = MacroDecision.rollback
  · exact absurd (Or.inr (let ⟨m, hm⟩ := hr; ⟨m, hm, ctl.checkpoint_ok m hm⟩)) hng
  · by_contra hno
    have hma : ∀ m : Fin M, ¬ ev.macroBad m ω :=
      fun m h => hno (Set.mem_iUnion.2 ⟨Sum.inr (Sum.inr m), h⟩)
    have had : ∀ i : Fin T, ¬ ev.admBad i ω :=
      fun i h => hno (Set.mem_iUnion.2 ⟨Sum.inr (Sum.inl i), h⟩)
    have hmi : ∀ j : Fin T, ¬ ev.microBad j ω :=
      fun j h => hno (Set.mem_iUnion.2 ⟨Sum.inl j, h⟩)
    refine hng (Or.inl ⟨fun m => ⟨fun hdec => hr ⟨m, hdec⟩, hma m⟩, had, hmi⟩)

/-! ## THE JOINT THEOREM -/

/-- **ttcat_complete (the project's ultimate
certified-or-safe statement)**: for any execution of the TT-CAT
controller, under the per-family measure premises (premise-form,
repo convention; discharge routes CITED: macro α's
`commit_sound` / `adaptive_commit_bridge`, admission α's via
 `admit_sound`, micro δ's via the whp channel):
1. the trajectory satisfies the master bound with the DERIVED
   boundary damages (`2·headLip·D`, no opaque δ);
2. the total master-view cost stays within the budget B (
   premise channel, construction route);
3. the EF endpoint satisfies the closed bound (packaged over
   an explicit `EFTrajectory` binder; the carrier bridge stays the
 pin);
4. with high probability the outcome is GOOD: EITHER every level
   ran correctly (no false commit, no false admission, no micro
   realization failure, and no rollback was needed), OR a rollback
   occurred and the last committed checkpoint of the SAME
   trajectory is restored — the failure probability is bounded by
   the ONE explicit union sum Σδ + Σα_adm + Σα_macro over the
   heterogeneous three-level event family. -/
theorem ttcat_complete (T M : ℕ)
    (ctl : TTCATController (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T M)
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ev : TTCATEvents T M Ω)
    (hMicro : ∀ j : Fin T, μ.real {ω | ev.microBad j ω} ≤ ev.δ j)
    (hAdm : ∀ i : Fin T, μ.real {ω | ev.admBad i ω} ≤ ev.α_adm i)
    (hMacro : ∀ m : Fin M, μ.real {ω | ev.macroBad m ω} ≤ ev.α_macro m)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (eftr : EFTrajectory (V := W) T) (L ε : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ (u v : W), |eftr.f u - eftr.f v| ≤ L * ‖u - v‖)
    (hQ : boundedErrorCompressor eftr.Q ε) (he0 : ‖eftr.e 0‖ ≤ ε) :
    Hagi.State.fullObjective (ctl.alt.states T)
      ≤ Hagi.State.fullObjective (ctl.alt.states 0)
        - ∑ j ∈ Finset.range T, ctl.alt.stepDrop' T j
        + ∑ j ∈ Finset.range T, ctl.alt.stepPenalty' T j
        + ∑ j ∈ Finset.range T, ctl.alt.derivedStepDamage T j
    ∧ ∑ j ∈ Finset.range T, ctl.master.stepCost T j ≤ ctl.B
    ∧ eftr.f (eftr.xef T) ≤ eftr.f (eftr.xef 0)
        - ∑ t ∈ Finset.range T, eftr.drop t + 2 * L * ε
    ∧ μ.real {ω | ¬ TTCATGood T M ctl ev ω}
      ≤ ((∑ j : Fin T, ev.δ j) + ∑ i : Fin T, ev.α_adm i)
        + ∑ m : Fin M, ev.α_macro m := by
  refine ⟨?_, ctl.budget.budget_ok,
    master_trajectory_bound_ef_closed T eftr L ε hL hlip hQ he0, ?_⟩
  · exact Hagi.Training.AlternatingJoint.alternating_trajectory_bound_derived
      T ctl.alt
  · have h1 := measureReal_iUnion_fintype_le (μ := μ)
      (f := fun i : Fin T ⊕ (Fin T ⊕ Fin M) => ttcatFailSet ev i)
    rw [Fintype.sum_sum_type] at h1
    rw [Fintype.sum_sum_type] at h1
    calc μ.real {ω | ¬ TTCATGood T M ctl ev ω}
        ≤ μ.real (⋃ i : Fin T ⊕ (Fin T ⊕ Fin M), ttcatFailSet ev i) :=
          measureReal_mono
            (fun ω h => by
              obtain ⟨i, hi⟩ := ttcat_bad_subset_fail T M ctl ev ω h
              exact ⟨i, hi⟩)
            (by finiteness)
      _ ≤ (∑ j : Fin T, μ.real {ω | ev.microBad j ω})
        + ((∑ i : Fin T, μ.real {ω | ev.admBad i ω})
          + ∑ m : Fin M, μ.real {ω | ev.macroBad m ω}) := h1
      _ ≤ (∑ j : Fin T, ev.δ j)
        + ((∑ i : Fin T, ev.α_adm i) + ∑ m : Fin M, ev.α_macro m) := by
          refine add_le_add (Finset.sum_le_sum fun j _ => hMicro j) ?_
          exact add_le_add (Finset.sum_le_sum fun i _ => hAdm i)
            (Finset.sum_le_sum fun m _ => hMacro m)
      _ = ((∑ j : Fin T, ev.δ j) + ∑ i : Fin T, ev.α_adm i)
        + ∑ m : Fin M, ev.α_macro m := by ring

/-! ## Corollary: quality-optimality accounting -/

/-- **Quality-optimality form (corollary)**: the accepted
trajectory's total quality change — the full-objective decrease —
is at least the sum of certified drops MINUS the compression
penalties MINUS the derived boundary damages: the optimality gap is
EXACTLY the accounted penalties and damages, nothing unaccounted
(direct accounting from the derived bound). -/
theorem ttcat_quality_optimality (T M : ℕ)
    (ctl : TTCATController (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T M) :
    Hagi.State.fullObjective (ctl.alt.states 0)
      - Hagi.State.fullObjective (ctl.alt.states T)
      ≥ (∑ j ∈ Finset.range T, ctl.alt.stepDrop' T j)
        - (∑ j ∈ Finset.range T, ctl.alt.stepPenalty' T j)
        - ∑ j ∈ Finset.range T, ctl.alt.derivedStepDamage T j := by
  have h := Hagi.Training.AlternatingJoint.alternating_trajectory_bound_derived
    T ctl.alt
  linarith

end Hagi.Training.TTCAT
