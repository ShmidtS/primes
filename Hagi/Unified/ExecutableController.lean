/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.ExecutableSelection
import Hagi.Unified.QualityResourceMin
set_option linter.style.header false

/-!
# Executable discrete finite resource selection (cycle 77)

A supplied action list is filtered by a concrete Bool guard, then the
existing `List.argmin` chooses minimum memory-first resource cost among
quality-eligible actions **in that list**. No `Classical.choose`, default
action, physical-safety claim, or arbitrary real-valued search is added.

The point-model adapter casts integer quality into the old real-valued
controller interface. Its guard equivalence and equality with the old
minimum cost use that cast model; they do not execute arbitrary real CE.
Completeness of the input list is a separate explicit premise whenever
whole-Fintype minimality is claimed. Instrumented counts are logical
guard and pair-relation calls, not hardware instructions or latency.
-/

namespace Hagi.Unified.ExecutableController

open Hagi.Unified.ExecutableSelection
open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin

/-- A supplied discrete point model with the old controller's `A : Type`
action carrier. `safetyGuard` is only the model's Boolean admission
guard, not evidence of physical safety. -/
structure DiscreteProgram (A : Type) (S : Type*) where
  actions : List A
  state : S
  step : A → S → S
  quality : S → ℤ
  safetyGuard : A → S → Bool
  memory : A → ℕ
  operations : A → ℕ
  memoryCap : ℕ
  operationsCap : ℕ
  qualityFloor : ℤ

/-- Total executable admission at the supplied state. Quality is checked
at the actual successor. Boolean short-circuiting means that a rejected
prefix need not evaluate every later field or successor. -/
def admissionGuard {A : Type} {S : Type*} (p : DiscreteProgram A S) (a : A) : Bool :=
  p.safetyGuard a p.state && decide (p.memory a ≤ p.memoryCap) &&
    decide (p.operations a ≤ p.operationsCap) &&
    decide (p.qualityFloor ≤ p.quality (p.step a p.state))

theorem admissionGuard_eq_true {A : Type} {S : Type*} (p : DiscreteProgram A S) (a : A) :
    admissionGuard p a = true ↔
      p.safetyGuard a p.state = true ∧
        p.memory a ≤ p.memoryCap ∧ p.operations a ≤ p.operationsCap ∧
        p.qualityFloor ≤ p.quality (p.step a p.state) := by
  simp [admissionGuard, and_assoc]

/-- Adapter of the supplied point model into the old real-valued
controller. Only the quality value is cast; `step` and resources are
unchanged. `safe` captures the guard at the fixed supplied state. -/
@[reducible] def toController {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    ControllerProblem A S where
  value s := (p.quality s : ℝ)
  step := p.step
  memory := p.memory
  operations := p.operations
  safe a := p.safetyGuard a p.state = true

instance {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    DecidablePred (toController p).safe :=
  fun a => inferInstanceAs (Decidable (p.safetyGuard a p.state = true))

/-- The executable guard is exactly old eligibility in the integer-cast
controller. Both directions cover arbitrary signs of integer quality. -/
theorem admissionGuard_iff_qualityEligible {A : Type} {S : Type*} [Fintype A]
    (p : DiscreteProgram A S) (a : A) :
    admissionGuard p a = true ↔
      qualityEligible (p := toController p) p.state p.memoryCap p.operationsCap
        (p.qualityFloor : ℝ) a := by
  rw [admissionGuard_eq_true, qualityEligible, mem_feasible (p := toController p)]
  constructor
  · rintro ⟨hsafe, hmemory, hoperations, hquality⟩
    refine ⟨⟨hsafe, hmemory, hoperations⟩, ?_⟩
    change (p.qualityFloor : ℝ) ≤ (p.quality (p.step a p.state) : ℝ)
    exact_mod_cast hquality
  · rintro ⟨⟨hsafe, hmemory, hoperations⟩, hquality⟩
    refine ⟨hsafe, hmemory, hoperations, ?_⟩
    change (p.qualityFloor : ℝ) ≤ (p.quality (p.step a p.state) : ℝ) at hquality
    exact_mod_cast hquality

/-- Selection result together with its explicit logical work counters.
These are model counts, not an automatically generated native profile. -/
structure SelectionReport (A : Type) where
  selected : Option A
  guardCalls : ℕ
  comparisons : ℕ

/-- One guarded filter and one existing argmin fold. Both are inspected
only through the audited kernel; no second minimum algorithm is used. -/
def selectionReport {A : Type} {S : Type*} (p : DiscreteProgram A S) : SelectionReport A :=
  let admitted := auditedFilter (admissionGuard p) p.actions
  let best := auditedArgmin (fun a => resourceCost (toController p) a) admitted.1
  { selected := best.1
    guardCalls := admitted.2
    comparisons := best.2 }

/-- The executable selection as an option; no artificial default action. -/
def finiteSelection {A : Type} {S : Type*} (p : DiscreteProgram A S) : Option A :=
  (selectionReport p).selected

/-- Actual successor of the returned action at the supplied state. -/
def selectedNext {A : Type} {S : Type*} (p : DiscreteProgram A S) : Option S :=
  (finiteSelection p).map (fun a => p.step a p.state)

private theorem finiteSelection_eq_argmin {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    finiteSelection p =
      List.argmin (fun a => resourceCost (toController p) a)
        (p.actions.filter (admissionGuard p)) := by
  unfold finiteSelection selectionReport
  simp only [auditedArgmin_fst, auditedFilter_fst]

private theorem finiteSelection_mem_argmin {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) :
    a ∈ List.argmin (fun a => resourceCost (toController p) a)
      (p.actions.filter (admissionGuard p)) := by
  rw [← finiteSelection_eq_argmin]
  simp [ha]

/-- A returned action really occurs in the supplied list and passed the
complete composite guard. -/
theorem finiteSelection_mem {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) :
    a ∈ p.actions ∧ admissionGuard p a = true := by
  exact List.mem_filter.mp (List.argmin_mem (finiteSelection_mem_argmin p ha))

/-- Minimum memory-first resource cost over all eligible input-list
members. Nothing is claimed about unlisted candidates. -/
theorem finiteSelection_minimum {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) (b : A)
    (hb : b ∈ p.actions) (hguard : admissionGuard p b = true) :
    resourceCost (toController p) a ≤ resourceCost (toController p) b := by
  exact List.le_of_mem_argmin (List.mem_filter.mpr ⟨hb, hguard⟩)
    (finiteSelection_mem_argmin p ha)

/-- No returned action precisely when every input action fails the guard.
There is no fallback witness, and no physical state unchanged theorem. -/
theorem finiteSelection_none_iff {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    finiteSelection p = none ↔
      ∀ a ∈ p.actions, admissionGuard p a = false := by
  rw [finiteSelection_eq_argmin, List.argmin_eq_none, List.filter_eq_nil_iff]
  constructor
  · intro h a ha
    have hg := h a ha
    cases hb : admissionGuard p a <;> simp_all
  · intro h a ha
    have hb := h a ha
    simp [hb]

/-- The optional successor is the actual `step`, not an effects record. -/
theorem selectedNext_eq_some {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) :
    selectedNext p = some (p.step a p.state) := by
  simp [selectedNext, ha]

/-- Guard counter is exactly the number of supplied actions, including
when the filtered candidate list is empty. -/
theorem selectionReport_guardCalls {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    (selectionReport p).guardCalls = p.actions.length := by
  simpa [selectionReport] using auditedFilter_snd (admissionGuard p) p.actions

/-- Pair-relation comparisons are one fewer than admitted candidates,
or zero if there is no admitted candidate. -/
theorem selectionReport_comparisons {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    (selectionReport p).comparisons =
      (p.actions.filter (admissionGuard p)).length - 1 := by
  simpa [selectionReport, auditedFilter_fst] using
    auditedArgmin_snd (fun a => resourceCost (toController p) a)
      (auditedFilter (admissionGuard p) p.actions).1

/-- Model relation-call count is bounded by total inputs, but this is
not minimum CPU, FLOPs, wall time, or a universal search lower bound. -/
theorem selectionReport_comparisons_le {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    (selectionReport p).comparisons ≤ p.actions.length := by
  rw [selectionReport_comparisons]
  exact (Nat.sub_le _ _).trans (List.length_filter_le _ _)

/-- Equality with the old mathematical minimum cost in the cast model,
provided the input list covers every action. The concrete selected
actions may differ under cost ties; only their resource costs are equal. -/
theorem finiteSelection_cost_eq_minimumResource {A : Type} {S : Type*} [Fintype A]
    (p : DiscreteProgram A S) {a : A} (ha : finiteSelection p = some a)
    (hcomplete : ∀ b, b ∈ p.actions) :
    resourceCost (toController p) a = resourceCost (toController p)
      (minimumResource (toController p) p.state p.memoryCap p.operationsCap
        (p.qualityFloor : ℝ) a
        ((admissionGuard_iff_qualityEligible p a).mp (finiteSelection_mem p ha).2)) := by
  let hquality : qualityEligible (toController p) p.state p.memoryCap p.operationsCap
      (p.qualityFloor : ℝ) a :=
    (admissionGuard_iff_qualityEligible p a).mp (finiteSelection_mem p ha).2
  change resourceCost (toController p) a = resourceCost (toController p)
    (minimumResource (toController p) p.state p.memoryCap p.operationsCap
      (p.qualityFloor : ℝ) a hquality)
  have hmin := minimumResource_spec (toController p) p.state p.memoryCap
    p.operationsCap (p.qualityFloor : ℝ) a hquality
  exact le_antisymm
    (finiteSelection_minimum p ha _ (hcomplete _)
      ((admissionGuard_iff_qualityEligible p _).mpr hmin.1))
    (hmin.2 a hquality)

end Hagi.Unified.ExecutableController
