/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Cert.Core
import Mathlib.Tactic

set_option linter.style.header false
set_option relaxedAutoImplicit false

/-!
# Executable certificate step checker

The certified loop lives on `noncomputable ℝ`, so the
certified layer has no executable counterpart — a trainer cannot
hand a certificate to any decidable validator. This module is the
executable checker: step data as RATIONAL readouts (`ℚ` — decidable
order, decision-complete, no floats), a computable `checkStep`, a
computable trajectory fold `checkTrajectory`, and soundness bridges
to the certified kernel. The bridge constructs `Hagi.Cert.CertStep`
from checked data (`mkCertStep`), so the ONE additive-ledger
telescope (`Hagi.Cert.trajectory_telescope`, i.e. the
`certStep_objective` instance of `Hagi.Cert.AdditiveLedger`) proves
`checkTrajectory_sound` — this module adds NO new telescoping
induction over ℝ, only Bool/list plumbing.
-/

namespace Hagi.Runtime

open Hagi.Cert (SystemMetrics StepObligations FloorsKept CertStep)

/-! ## Step data and the executable check -/

/-- One step of trainer-supplied certificate data: objective,
declared drop, budget and risk levels before/after the step, all as
rationals. The trainer reports; `checkStep` decides. -/
structure CertStepData where
  /-- Objective readout at the pre-state. -/
  obj : ℚ
  /-- Objective readout at the post-state. -/
  obj' : ℚ
  /-- Declared certified drop. -/
  drop : ℚ
  /-- Budget readout at the pre-state. -/
  budget : ℚ
  /-- Budget readout at the post-state. -/
  budget' : ℚ
  /-- Risk readout at the pre-state. -/
  risk : ℚ
  /-- Risk readout at the post-state. -/
  risk' : ℚ
deriving Repr

instance : Inhabited CertStepData := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩

/-- The executable step check: positive drop, real descent
(`drop ≤ obj − obj'`), nonnegative budget and risk remainders.
Every conjunct is a decidable rational comparison — the checker is
exact, not floating-point. -/
def checkStep (d : CertStepData) : Bool :=
  decide (0 < d.drop) && decide (d.drop ≤ d.obj - d.obj')
    && decide (0 ≤ d.budget') && decide (0 ≤ d.risk')

/-- Decision content of a passing step check, as rational facts. -/
theorem checkStep_spec {d : CertStepData} (h : checkStep d = true) :
    0 < d.drop ∧ d.drop ≤ d.obj - d.obj'
      ∧ 0 ≤ d.budget' ∧ 0 ≤ d.risk' := by
  simp only [checkStep, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

/-- Soundness of the step check: a passing check gives the
certified drop positivity and the descent inequality over ℝ. -/
theorem checkStep_sound {d : CertStepData} (h : checkStep d = true) :
    0 < (d.drop : ℝ) ∧ (d.obj' : ℝ) ≤ (d.obj : ℝ) - (d.drop : ℝ) := by
  obtain ⟨h1, h2, _, _⟩ := checkStep_spec h
  refine ⟨?_, ?_⟩
  · exact_mod_cast h1
  · have h2' : ((d.drop : ℚ) : ℝ) ≤ ((d.obj - d.obj' : ℚ) : ℝ) := by
      exact_mod_cast h2
    push_cast at h2'
    linarith

/-! ## Bridge to the certified kernel -/

/-- Accuracy contract: the data `d` DESCRIBES the real transition
`s → s'` of a system with metrics `M` — each rational readout casts
to the true real-valued level. This is the (unchecked, proof-side)
interface between the trainer's report and the certified layer. -/
def Describes {S TaskId : Type*} (M : SystemMetrics S TaskId)
    (s s' : S) (d : CertStepData) : Prop :=
  (d.obj : ℝ) = M.objective s ∧ (d.obj' : ℝ) = M.objective s'
    ∧ (d.budget : ℝ) = M.budget s ∧ (d.budget' : ℝ) = M.budget s'
    ∧ (d.risk : ℝ) = M.risk s ∧ (d.risk' : ℝ) = M.risk s'

/-- The bridge: checked data that describes a real transition (plus
floors kept at the post-state) yields a `CertStep` — entry into the
certified kernel and its `Hagi.Cert.AdditiveLedger` instance. The budget/risk
spends are the readout differences `budget − budget'`, `risk − risk'`. -/
def mkCertStep {S TaskId : Type*} {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId} {s s' : S} (d : CertStepData)
    (h : checkStep d = true) (hacc : Describes M s s' d)
    (hfl : FloorsKept M obl s') : CertStep M obl s s' where
  drop := (d.drop : ℝ)
  drop_pos := (checkStep_sound h).1
  descent := by
    have h2 := (checkStep_sound h).2
    rw [← hacc.2.1, ← hacc.1]
    exact h2
  budgetSpend := (d.budget : ℝ) - (d.budget' : ℝ)
  budget_next := by rw [hacc.2.2.1, hacc.2.2.2.1]; ring
  budget_nonneg := by
    rw [← hacc.2.2.2.1]
    have := (checkStep_spec h).2.2.1
    exact_mod_cast this
  riskSpend := (d.risk : ℝ) - (d.risk' : ℝ)
  risk_next := by rw [hacc.2.2.2.2.1, hacc.2.2.2.2.2]; ring
  risk_nonneg := by
    rw [← hacc.2.2.2.2.2]
    have := (checkStep_spec h).2.2.2
    exact_mod_cast this
  floorsKept := hfl

/-! ## Trajectory fold -/

/-- The executable trajectory check: the reported objectives must
chain (`obj` of each step equals `start` for the first and the
previous `obj'` afterwards — internal consistency, the trainer
cannot contradict itself between steps) and every step must pass
`checkStep`. A computable left fold over the certificate list. -/
def checkTrajectory (start : ℚ) : List CertStepData → Bool
  | [] => true
  | d :: ds => decide (d.obj = start) && checkStep d
    && checkTrajectory d.obj' ds

/-- Extraction plumbing: a passing trajectory check checks every
step of the list (indexed by `getD`, matching the soundness
statement). Bool-level induction only, no real arithmetic. -/
theorem checkStep_of_checkTrajectory (start : ℚ) (ds : List CertStepData)
    (h : checkTrajectory start ds = true) :
    ∀ j, j < ds.length → checkStep (ds.getD j default) = true := by
  induction ds generalizing start with
  | nil => intro j hj; simp at hj
  | cons d rest ih =>
    rw [checkTrajectory] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using h.1.2
    · have hl : (d :: rest).length = rest.length + 1 := rfl
      have hstep : (d :: rest).getD j default = rest.getD (j - 1) default := by
        rw [← Nat.succ_pred_eq_of_pos hj0]; simp [List.getD]
      rw [hstep]
      exact ih (d.obj') h.2 (j - 1) (by omega)

/-- Soundness of the trajectory fold: if every element of a passing
certificate list describes the real transitions `t j → t (j+1)` of a
system (and floors are kept along the way), then the ONE certified
telelescope applies — the terminal objective is bounded by the initial
objective minus the sum of declared drops. The proof constructs the
`CertStep` supply with `mkCertStep` and delegates to
`Hagi.Cert.trajectory_telescope_fin` (the `Fin`-indexed form of the
`certStep_objective` instance telescope); no new telescoping
induction over ℝ is introduced. -/
theorem checkTrajectory_sound {S TaskId : Type*}
    {M : SystemMetrics S TaskId} {obl : StepObligations TaskId}
    (t : ℕ → S) (start : ℚ) (ds : List CertStepData)
    (hacc : ∀ j, Describes M (t j) (t (j + 1)) (ds.getD j default))
    (hfl : ∀ j : ℕ, FloorsKept M obl (t (j + 1)))
    (h : checkTrajectory start ds = true) :
    M.objective (t ds.length) ≤ M.objective (t 0)
      - ∑ j : Fin ds.length, ((ds.getD ↑j default).drop : ℝ) := by
  have key := Hagi.Cert.trajectory_telescope_fin (t := t)
    (fun j : Fin ds.length => mkCertStep (ds.getD ↑j default)
      (checkStep_of_checkTrajectory start ds h ↑j j.2) (hacc ↑j) (hfl ↑j))
  calc M.objective (t ds.length)
      ≤ M.objective (t 0) - ∑ j : Fin ds.length,
          (mkCertStep (ds.getD ↑j default)
            (checkStep_of_checkTrajectory start ds h ↑j j.2) (hacc ↑j) (hfl ↑j)).drop :=
        key
    _ = M.objective (t 0)
          - ∑ j : Fin ds.length, ((ds.getD ↑j default).drop : ℝ) := by
        congr 1

end Hagi.Runtime
