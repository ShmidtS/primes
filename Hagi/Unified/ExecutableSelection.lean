/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Data.List.MinMax
import Mathlib.Tactic
set_option linter.style.header false

/-!
# Executable finite selection with logical guard and relation counters
(cycle 77)

This module instruments the existing `List.filter` and `List.argmin`
algorithms. It does not implement another minimum engine. Logical
composite-guard and pair-relation calls are counted, not physical
instructions, wall time, FLOPs, or allocations. In particular, a
comparison may evaluate its cost function more than once, and a
short-circuiting guard need not evaluate every field or successor.
-/

namespace Hagi.Unified.ExecutableSelection

/-- Filter a finite list while counting logical composite-guard calls. -/
def auditedFilter {α : Type*} (guard : α → Bool) : List α → List α × ℕ
  | [] => ([], 0)
  | a :: as =>
      let (accepted, n) := auditedFilter guard as
      (if guard a then a :: accepted else accepted, n + 1)

/-- The instrumented filter retains precisely the ordinary filter's
candidates. -/
theorem auditedFilter_fst {α : Type*} (guard : α → Bool) (as : List α) :
    (auditedFilter guard as).1 = as.filter guard := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases h : guard a <;> simp [auditedFilter, h, ih]

/-- Every supplied action is inspected by one logical composite guard. -/
theorem auditedFilter_snd {α : Type*} (guard : α → Bool) (as : List α) :
    (auditedFilter guard as).2 = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases h : guard a <;> simp [auditedFilter, h, ih]

/-- Same step as the library argmin fold, plus one counter increment
when there is an incumbent and hence a relation call. -/
private def argminStep {α R : Type*} [LinearOrder R] (cost : α → R)
    (incumbent : Option α × ℕ) (a : α) : Option α × ℕ :=
  (List.argAux (fun b c => cost b < cost c) incumbent.1 a,
    incumbent.2 + if incumbent.1.isSome then 1 else 0)

/-- Audited finite minimum. The second component counts relation cells
visited by the fold; it is not a measurement of run-time instructions. -/
def auditedArgmin {α R : Type*} [LinearOrder R] (cost : α → R) (as : List α) :
    Option α × ℕ :=
  as.foldl (argminStep cost) (none, 0)

private theorem foldl_argminStep_fst {α R : Type*} [LinearOrder R]
    (cost : α → R) (as : List α) (best : Option α) (n : ℕ) :
    (as.foldl (argminStep cost) (best, n)).1 =
      as.foldl (List.argAux fun b c => cost b < cost c) best := by
  induction as generalizing best n with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      exact ih _ _

private theorem foldl_argminStep_snd_some {α R : Type*} [LinearOrder R]
    (cost : α → R) (as : List α) (a : α) (n : ℕ) :
    (as.foldl (argminStep cost) (some a, n)).2 = n + as.length := by
  induction as generalizing a n with
  | nil => rfl
  | cons b as ih =>
      simp only [List.foldl_cons]
      by_cases h : cost b < cost a
      · have hi := ih b (n + 1)
        simp only [argminStep, List.argAux, h, ↓reduceIte,
          Option.isSome_some, List.length_cons]
        omega
      · have hi := ih a (n + 1)
        simp only [argminStep, List.argAux, h, ↓reduceIte,
          Option.isSome_some, List.length_cons]
        omega

private theorem foldl_argminStep_snd_none_cons {α R : Type*} [LinearOrder R]
    (cost : α → R) (a : α) (as : List α) (n : ℕ) :
    ((a :: as).foldl (argminStep cost) (none, n)).2 = n + as.length := by
  simp only [List.foldl_cons]
  simpa [argminStep, List.argAux] using foldl_argminStep_snd_some cost as a n

/-- The audited fold selects exactly the same candidate as `List.argmin`;
its first-on-tie and all minimum properties are inherited, not duplicated. -/
theorem auditedArgmin_fst {α R : Type*} [LinearOrder R] (cost : α → R)
    (as : List α) : (auditedArgmin cost as).1 = List.argmin cost as := by
  exact foldl_argminStep_fst cost as none 0

/-- Zero comparisons for no candidates; otherwise exactly one fewer than
the number of admitted candidates. This follows from the fold itself. -/
theorem auditedArgmin_snd {α R : Type*} [LinearOrder R] (cost : α → R)
    (as : List α) : (auditedArgmin cost as).2 = as.length - 1 := by
  cases as with
  | nil => rfl
  | cons a as =>
      simpa [auditedArgmin] using foldl_argminStep_snd_none_cons cost a as 0

end Hagi.Unified.ExecutableSelection
