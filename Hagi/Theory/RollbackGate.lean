/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# RollbackGate — the exact pre-step rollback gate

Lean bridge for the HAGI_v2 wave199 rollback gate: a validation-
gated optimizer step with EXACT rollback. The controller state is
a three-component snapshot (parameters, optimizer state, RNG); a
step COMMITS only when the weighted validation gain strictly
exceeds the error budget, otherwise the FULL pre-step state is
restored — exactly, with no partial borrowing from the candidate.

## Source anchors (READ-ONLY HAGI_v2)

- snapshots of the three components:
  source: hagi/selfmodel.py:62-76 (params / optimizer / RNG);
- taken at step entry, before any measurement:
  source: hagi/selfmodel.py:88-91;
- commit condition `wb - wa > total_bound` (total_bound = e_gen +
  e_quant + e_route + m_safety):
  source: hagi/selfmodel.py:127 and :145;
- the exact pre-step restore on HOLD (params, optimizer, RNG):
  source: hagi/selfmodel.py:151-156;
- the self-test contract `torch.equal(p, snap)` on HOLD — the
  code-level twin of `rollback_obj_exact`:
  source: hagi/selfmodel.py:175-183.

## Honesty pins

- The state model is the three-component snapshot of the source;
  backtracking (half-stepping the scale) is search INSIDE the
  step and is intentionally not modeled — it only affects WHICH
  candidate reaches the gate, not the gate/rollback semantics.
- The early HOLD branches (missing tasks, backward failure,
  non-finite gradient, gradient conflict, degenerate direction —
  source: hagi/selfmodel.py:95-124) leave the state untouched in
  the same way; the gate theorem covers them all as `gate = false`.
- Neighbor coverage: `Hagi.Unified.CommitGate.holdSafe` pins only
  the scalar potential; the state-unification `hold_rollback_total`
 is a different setting without the gate condition; TTCAT
 restores the last COMMITTED checkpoint, not the
  pre-step state. None of them covers the wave199 bundle
  (gate condition + full state + budget + telemetry chain).
-/

namespace Hagi.Theory.RollbackGate

/-- Controller verdict of a guarded step.
source: hagi/selfmodel.py:17 (`StepResult.action` ∈ {COMMIT, HOLD}). -/
inductive Action : Type
  | COMMIT : Action
  | HOLD : Action
deriving Repr

/-- The three-component controller state snapshot: trainable
parameters, optimizer state, RNG counter. The rollback restores
ALL THREE exactly.
source: hagi/selfmodel.py:62-76 (_snapshot_trainable,
_snapshot_optim, _snapshot_rng). -/
structure CtrlState (P O : Type*) where
  /-- Trainable parameters (snapshot by index). -/
  params : P
  /-- Optimizer state (deep-copied state dict). -/
  optim : O
  /-- RNG state (py/numpy/torch, modeled as one counter). -/
  rng : ℕ
deriving Repr

/-- Commit gate: the weighted validation gain strictly exceeds
the error budget (`wb`/`wa` = weighted losses before/after,
`errBound` = e_gen + e_quant + e_route + m_safety).
source: hagi/selfmodel.py:127 and :145 (`gain > total_bound`). -/
def commitGate (wb wa errBound : ℝ) : Prop := wb - wa > errBound

/-- The guarded step: the candidate state is installed only when
the gate passes; otherwise the step IS the identity on the
snapshot (the exact pre-step restore).
source: hagi/selfmodel.py:139-156 (COMMIT installs the candidate,
final HOLD restores params + optimizer + RNG). -/
def guardedStep (gate : Bool) (s cand : CtrlState P O) :
    CtrlState P O :=
  if gate then cand else s

/-- The action of a guarded step. -/
def stepAction (gate : Bool) : Action :=
  if gate then Action.COMMIT else Action.HOLD

/-! ## The gate theorem: rollback is exact -/

/-- ROLLBACK GATE SOUND: a failed gate leaves the FULL controller
state (params, optimizer, RNG) EXACTLY at the pre-step snapshot.
source: hagi/selfmodel.py:151-156 (final restore on HOLD). -/
theorem rollback_gate_sound (gate : Bool) (s cand : CtrlState P O)
    (h : gate = false) : guardedStep gate s cand = s := by
  simp [guardedStep, h]

/-- Component leg: parameters are unchanged on rollback. -/
theorem rollback_state_params (gate : Bool) (s cand : CtrlState P O)
    (h : gate = false) :
    (guardedStep gate s cand).params = s.params := by
  rw [rollback_gate_sound gate s cand h]

/-- Component leg: optimizer state is unchanged on rollback. -/
theorem rollback_state_optim (gate : Bool) (s cand : CtrlState P O)
    (h : gate = false) :
    (guardedStep gate s cand).optim = s.optim := by
  rw [rollback_gate_sound gate s cand h]

/-- Component leg: RNG state is unchanged on rollback. -/
theorem rollback_state_rng (gate : Bool) (s cand : CtrlState P O)
    (h : gate = false) :
    (guardedStep gate s cand).rng = s.rng := by
  rw [rollback_gate_sound gate s cand h]

/-- OBJ-CHAIN EXACTNESS: for ANY deterministic objective observer
on the state, the objective after a rollback equals the objective
before the step — EXACT equality, not a bound. This is the
functional twin of the source self-test `torch.equal` on every
parameter.
source: hagi/selfmodel.py:175-183 (case2 HOLD+rollback asserts
exact parameter equality). -/
theorem rollback_obj_exact (gate : Bool) (s cand : CtrlState P O)
    (obj : CtrlState P O → ℝ) (h : gate = false) :
    obj (guardedStep gate s cand) = obj s := by
  rw [rollback_gate_sound gate s cand h]

/-! ## Budget: a rollback spends nothing -/

/-- The validation-budget spend of a guarded step: the budget is
charged on COMMIT only; a HOLD/rollback step spends nothing. -/
def budgetSpend (gate : Bool) (δ : ℝ) : ℝ :=
  if gate then δ else 0

/-- A failed gate consumes NO validation budget — the δ-budget is
spent only by committed rounds. -/
theorem rollback_budget_unspent (gate : Bool) (δ : ℝ)
    (h : gate = false) : budgetSpend gate δ = 0 := by
  simp [budgetSpend, h]

/-- The total budget of a step list: spends are summed over
committed steps only. -/
def budgetOf (gates : List Bool) (δ : ℝ) : ℝ :=
  (gates.map (fun g => budgetSpend g δ)).sum

/-- The budget of a step list is bounded by the number of
committed steps times the per-commit δ. -/
theorem budgetOf_le (gates : List Bool) (δ : ℝ) (_hδ : 0 ≤ δ) :
    budgetOf gates δ ≤ gates.count true * δ := by
  induction gates with
  | nil => simp [budgetOf]
  | cons g gs ih =>
    have hcount : (g :: gs).count true
        = gs.count true + (if g then 1 else 0) := by
      cases g <;> simp
    simp only [budgetOf, List.map_cons, List.sum_cons]
    simp only [budgetOf, budgetSpend] at ih
    rw [hcount]
    cases g
    · simp only [budgetSpend, Bool.false_eq_true, ite_false, Nat.add_zero]
      linarith
    · simp only [budgetSpend, ite_true]
      push_cast
      linarith

/-! ## Commit: the gate certifies a real gain -/

/-- COMMIT CERTIFIED GAIN: a passing gate means the post-step
weighted loss is strictly below the pre-step loss minus the error
budget — the certified gain is at least the budget.
source: hagi/selfmodel.py:145 (`gain > total_bound`,
certified_gain). -/
theorem commit_certified_gain (wb wa errBound : ℝ)
    (herr : 0 ≤ errBound) (h : commitGate wb wa errBound) :
    wa < wb - errBound ∧ 0 < wb - wa := by
  unfold commitGate at h
  constructor <;> linarith

/-! ## Telemetry: a mixed chain has no phantom holds -/

/-- One chain step: a gate decision together with the candidate
state it was evaluated against. -/
abbrev ChainStep (P O : Type*) := Bool × CtrlState P O

/-- Fold a mixed commit/hold chain over an initial snapshot: each
step is a `guardedStep`. -/
def runChain (s : CtrlState P O) :
    List (ChainStep P O) → CtrlState P O
  | [] => s
  | (g, cand) :: rest => runChain (guardedStep g s cand) rest

/-- The last COMMITTED state of a chain: the most recent state
installed by a passing gate (`s` if none). -/
def lastCommitted (s : CtrlState P O) :
    List (ChainStep P O) → CtrlState P O
  | [] => s
  | (g, cand) :: rest =>
      if g = true then lastCommitted cand rest
      else lastCommitted s rest

/-- TELEMETRY: after a mixed chain, the final state IS the last
committed state — every trailing/interior rollback contributes
exactly nothing, so the telemetry chain has no phantom states. -/
theorem rollback_chain_telemetry (s : CtrlState P O)
    (chain : List (ChainStep P O)) :
    runChain s chain = lastCommitted s chain := by
  induction chain generalizing s with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨g, cand⟩ := step
    cases hg : g with
    | false =>
      subst hg
      simpa [runChain, lastCommitted, guardedStep] using ih s
    | true =>
      subst hg
      simpa [runChain, lastCommitted, guardedStep] using ih cand

/-! ## Negative: a weak gate can lose -/

/-- WEAK GATE LOSES: committing without the gate condition can
strictly WORSEN the objective — the motivating counterexample for
the gate. Concretely: a one-parameter state where the candidate
has a worse objective, forced through with `gate = true` while
the gate condition fails. -/
theorem weak_gate_loses :
    ∃ (obj : CtrlState ℕ ℕ → ℝ) (s cand : CtrlState ℕ ℕ)
      (errBound : ℝ),
        ¬ commitGate (obj s) (obj cand) errBound ∧
        obj (guardedStep true s cand) > obj s := by
  refine ⟨fun st => st.params, ⟨0, 0, 0⟩, ⟨1, 0, 0⟩, 0, ?_, ?_⟩
  · unfold commitGate; norm_num
  · unfold guardedStep; norm_num

end Hagi.Theory.RollbackGate
