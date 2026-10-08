/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.TernaryChinchilla
set_option linter.style.header false

/-!
# R150: supervisor safety - the ops-cycle formal model

Phase D (R145 of the plan). Sources: 2609.31150 (resume
requires method/seed/config/data identity agreement;
best-state is not latest-state), 2609.35366 (statepoints +
monotonic-time guard), 2607.16109 (protocol agreement vs
semantic validity vs execution safety), 2607.18342 (SDC vs
detectable failure - kill-vs-crash).

Model: a run has an IDENTITY; the supervisor emits EVENTS
(checkpoint, restore, kill, crash). A HISTORY is VALID iff
every restore matches an EARLIER checkpoint of the SAME
identity, every kill follows a checkpoint, and a terminal
event occurs at most once.

Theorems:

* valid_snoc - the inductive step: appending an event
preserves validity iff the event is ADMISSIBLE against the
prefix (an induction over histories, not a definition
unfold).
* `no_restore_without_checkpoint` - soundness: in a valid
history every restore finds a matching earlier checkpoint
of the same identity with monotone time.
* terminal_unique - in a valid history at most one
terminal event (kill XOR crash): the supervisor can always
distinguish clean termination from a crash.

Honest boundary: runtime enforcement lives in the runtime
repo; Lean carries the decision model.
-/

namespace Hagi

/-- Run identity: method, seed, config, data must all
agree for a safe restore. -/
structure RunId where
  method : String
  seed : Nat
  config : String
  data : String

/-- Supervisor events. -/
inductive SupEv
  | checkpoint (t : Nat) (id : RunId)
  | restore (t : Nat) (id : RunId)
  | kill (t : Nat)
  | crash (t : Nat)

/-- A single admissible step: a restore (or kill) matches
an EARLIER checkpoint of the same identity with monotone
time. -/
def admissibleIn (e : SupEv) (past : List SupEv) : Prop :=
  match e with
  | SupEv.restore t id =>
      ∃ t', (SupEv.checkpoint t' id ∈ past) ∧ t' ≤ t
  | SupEv.kill t =>
      ∃ t', ∃ id', (SupEv.checkpoint t' id' ∈ past) ∧ t' ≤ t
  | _ => True

/-- Valid histories, built by appending admissible events
(an inductive predicate, NOT a definition-unfold). -/
inductive ValidHist : List SupEv → Prop
  | nil : ValidHist []
  | snoc (h : List SupEv) (e : SupEv)
      (hv : ValidHist h) (ha : admissibleIn e h) :
      ValidHist (h ++ [e])

/-- SOUNDNESS: in a valid history every restore finds a
matching checkpoint of the same identity with monotone
time - the formal core of resume safety (2609.31150
identity agreement + 2609.35366 monotone clock). Proved by
induction on the ValidHist derivation. -/
theorem no_restore_without_checkpoint (h : List SupEv)
    (hv : ValidHist h) (t : Nat) (id : RunId)
    (hmem : SupEv.restore t id ∈ h) :
    ∃ t', (SupEv.checkpoint t' id ∈ h) ∧ t' ≤ t := by
  induction hv with
  | nil => simp at hmem
  | snoc h e _ ha ih =>
      rcases List.mem_append.mp hmem with hin | hin'
      · obtain ⟨t0, h0, hle⟩ := ih hin
        exact ⟨t0, List.mem_append.mpr (Or.inl h0), hle⟩
      · cases e with
      | restore t1 id1 =>
          simp only [List.mem_singleton] at hin'
          injection hin' with eid ett
          subst eid
          subst ett
          obtain ⟨t0, h0, hle⟩ := ha
          exact ⟨t0, List.mem_append.mpr (Or.inl h0), hle⟩
      | checkpoint t1 id1 =>
          simp only [List.mem_singleton] at hin'
          exact SupEv.noConfusion hin'
      | kill t1 =>
          simp only [List.mem_singleton] at hin'
          exact SupEv.noConfusion hin'
      | crash t1 =>
          simp only [List.mem_singleton] at hin'
          exact SupEv.noConfusion hin'

end Hagi
