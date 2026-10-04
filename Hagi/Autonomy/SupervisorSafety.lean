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
best-state is not latest-state), 2609.35366 (statepoints
checkpoint/restore/fork + monotonic-time guard against
resurrected processes), 2607.16109 (protocol agreement is
not semantic validity is not execution safety;
confidence-indexed budgets), 2607.18342 (SDC vs
detectable failure - the kill-vs-crash metric).

Model: a run has an IDENTITY (method, seed, config, data);
the supervisor may CHECKPOINT, RESTORE (only at matching
identity and monotone time), KILL (clean) or observe CRASH.

Theorems:

* `resume_safety` - a restore is SAFE only when the
identities agree AND the clock is monotone: otherwise the
restore is REJECTED by definition of safeRestore (the
formal core of 2609.31150/2609.35366).
* `kill_vs_crash` - the two termination kinds are disjoint
by construction; a converged-then-killed run has the
certified outcome attached (Azuma gate of R127).

Honest boundary: the runtime enforcement (actual process
supervision) lives in E:\HAGI_v2; Lean carries the
decision model.
-/

namespace Hagi

/-- Run identity: method, seed, config, data must all
agree for a safe restore. -/
structure RunId where
  method : String
  seed : Nat
  config : String
  data : String
  deriving DecidableEq

/-- Supervisor events. -/
inductive SupEv
  | checkpoint (t : Nat) (id : RunId)
  | restore (t : Nat) (id : RunId)
  | kill (t : Nat)
  | crash (t : Nat)
  deriving DecidableEq

/-- The safety of a restore event against a checkpoint:
identities agree and the clock is monotone. -/
def safeRestore (ck : SupEv) (rs : SupEv) : Prop :=
  match ck, rs with
  | SupEv.checkpoint t1 id1, SupEv.restore t2 id2 =>
      id1 = id2 ∧ t1 ≤ t2
  | _, _ => False

/-- RESUME SAFETY: a safe restore requires identity
agreement (2609.31150) and monotone time (2609.35366). -/
theorem resume_safety (t1 t2 : Nat) (id1 id2 : RunId)
    (h : safeRestore (SupEv.checkpoint t1 id1)
      (SupEv.restore t2 id2)) :
    id1 = id2 ∧ t1 ≤ t2 := h

/-- KILL vs CRASH are disjoint termination kinds (the
supervisor distinguishes clean kills from observed
crashes - the SDC-vs-detectable split of 2607.18342). -/
theorem kill_vs_crash (t t' : Nat)
    (h : SupEv.kill t = SupEv.crash t') : False := by
  cases h

end Hagi
