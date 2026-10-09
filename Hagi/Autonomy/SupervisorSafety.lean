/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.TernaryChinchilla
set_option linter.style.header false

/-!
# Supervisor safety — the ops-cycle decision model

A run has an identity (`RunId`); the supervisor emits events
(`SupEv`). A history is valid (`ValidHist`) iff every restore
matches an earlier checkpoint of the same identity with
monotone time, and every kill follows a checkpoint.

`no_restore_without_checkpoint`: in a valid history every
restore has a matching earlier checkpoint of the same
identity with `t' <= t`.
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

/-- In a valid history, every restore event `restore t id`
has a matching earlier `checkpoint t' id` with `t' <= t`. -/
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
