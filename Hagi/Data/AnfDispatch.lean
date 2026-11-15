/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Data.AnfCompose

set_option linter.style.header false

/-!
# ANF dispatch with collision abstention

Track E5 ladder rung 3 (TD E5-C302 remaining rungs 3+4: argument
ranges + collision abstention), C306. The Python V3 compiler
dispatches among candidate stencils by their argument ranges; when
two candidates' ranges overlap AMBIGUOUSLY and the candidates
disagree, the compiler ABSTAINS rather than guessing. This module
lands that policy as a certified dispatch on the AnfTransform
carriers:

- `AnfCand`: a candidate — a Boolean stencil
  `(Fin n → Bool) → Bool` plus its `argRanges`, the context
  signature's range data (a `Finset (Fin n)` of argument
  positions).
- `inRange`: a candidate applies at context `x` iff the context
  supplies EXACTLY the candidate's argument positions — the
  context's true-position set `{i | x i}` equals `argRanges`
  (`∀ i, x i = decide (i ∈ R)`). Decidable, so dispatch is
  computable. Modeling note (probe-audited): the weaker subset
  reading ("all of R is supplied") is UNSOUND for the
  disjointness composition — two candidates with empty ranges
  both trivially apply and may disagree — so exact-match is the
  honest range model.
- `collides`: two candidates collide at `x` iff both are in range
  at `x` AND their outputs disagree.
- `dispatchOrAbstain`: exactly one candidate in range → its
  value; none → the default; both → agreement check — agreeing
  values are returned, disagreeing values ABSTAIN (`none`).
- `dispatch_sound`: acceptance correctness — if dispatch returns
  `some v`, then `v` equals the value of every candidate that is
  in range at `x` (the unique applicable one; when both apply,
  acceptance itself certified agreement).
- `dispatch_sound_default`: the `some v` with no candidate in
  range is exactly the default.
- `abstain_sound`: no false coverage — when two candidates
  collide at `x`, dispatch returns `none` (never a value).
- `guard_disjoint_no_collision`: the composition with C302's
  `stencil_guard_sound` story — candidates with DISJOINT
  (nonempty) `argRanges` NEVER collide (both in range at `x`
  would force the ranges equal, contradicting disjointness), so
  the abstention never fires spuriously for support-disjoint
  candidates. The lemma needs no supportedness hypothesis — it
  holds for arbitrary stencils, strengthening the C302 guard
  composition.
- `anfFin2_dispatch_abstain`, `anfFin2_dispatch_ok`: the Fin 2
  anchor — a colliding pair (both ranges `{0}`, stencils `x₀` and
  `x₁`, context `[true, false]` → abstain) and a disjoint pair
  (`{0}` vs `{1}` → dispatch returns the applicable candidate's
  value), both by `decide`.

Honest scope (E5 ladder, follow-up beats): multi-candidate (> 2)
dispatch via the Python arg-range PRIORITY ordering is NOT claimed
here — only two-candidate dispatch with agreement/abstention.
End-to-end Python V3 compiler equivalence NOT claimed.
-/

namespace Hagi.Data.AnfDispatch

/-! ## Candidates, ranges, collisions -/

/-- A dispatch candidate: a Boolean stencil on the finite variable
set plus its `argRanges` — the context signature's range data, the
`Finset` of argument positions the candidate is declared for. -/
structure AnfCand (n : ℕ) where
  /-- The stencil function (truth table over `Fin n → Bool`). -/
  stencil : (Fin n → Bool) → Bool
  /-- The candidate's argument positions (context-signature range
  data). -/
  argRanges : Finset (Fin n)

/-- A candidate applies at context `x` iff the context's
argument-position set is EXACTLY the candidate's range: `x i`
is the membership bit of `i` in `argRanges`. Decidable. -/
def inRange {n : ℕ} (R : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∀ i, x i = decide (i ∈ R)

instance {n : ℕ} (R : Finset (Fin n)) (x : Fin n → Bool) :
    Decidable (inRange R x) :=
  Fintype.decidableForallFintype

/-- Two candidates collide at `x`: both are in range at `x` and
their outputs disagree — the ambiguous-overlap situation in which
the Python V3 compiler abstains. -/
def collides {n : ℕ} (a b : AnfCand n) (x : Fin n → Bool) : Prop :=
  inRange a.argRanges x ∧ inRange b.argRanges x ∧ a.stencil x ≠ b.stencil x

/-! ## The dispatch-or-abstain policy -/

/-- The Python V3 dispatch policy, certified form: exactly one
candidate in range → its value; none in range → the default;
both in range → agreement check — equal outputs are returned,
disagreeing outputs ABSTAIN (`none`, the compiler's error
signal). -/
def dispatchOrAbstain {n : ℕ} (dflt : Bool) (a b : AnfCand n)
    (x : Fin n → Bool) : Option Bool :=
  if inRange a.argRanges x then
    if inRange b.argRanges x then
      if a.stencil x = b.stencil x then some (a.stencil x) else none
    else some (a.stencil x)
  else
    if inRange b.argRanges x then some (b.stencil x) else some dflt

/-! ## Soundness -/

/-- Acceptance correctness: if dispatch returns `some v`, then
`v` is the value of every candidate that is in range at `x` —
the unique applicable candidate's value (when both apply, the
returned `some` itself certified that the two agree). -/
theorem dispatch_sound {n : ℕ} (dflt : Bool) (a b : AnfCand n)
    (x : Fin n → Bool) (v : Bool)
    (h : dispatchOrAbstain dflt a b x = some v) :
    (inRange a.argRanges x → v = a.stencil x) ∧
      (inRange b.argRanges x → v = b.stencil x) := by
  constructor
  · intro ha
    by_cases hb : inRange b.argRanges x
    · by_cases heq : a.stencil x = b.stencil x
      · have hd : dispatchOrAbstain dflt a b x = some (a.stencil x) := by
          rw [dispatchOrAbstain]; simp [ha, hb, heq]
        rw [hd] at h; injection h with h; exact h.symm
      · have hd : dispatchOrAbstain dflt a b x = none := by
          rw [dispatchOrAbstain]; simp [ha, hb, heq]
        rw [hd] at h; exact absurd h (by simp)
    · have hd : dispatchOrAbstain dflt a b x = some (a.stencil x) := by
        rw [dispatchOrAbstain]; simp [ha, hb]
      rw [hd] at h; injection h with h; exact h.symm
  · intro hb
    by_cases ha : inRange a.argRanges x
    · by_cases heq : a.stencil x = b.stencil x
      · have hd : dispatchOrAbstain dflt a b x = some (b.stencil x) := by
          rw [dispatchOrAbstain]; simp [ha, hb, heq]
        rw [hd] at h; injection h with h; exact h.symm
      · have hd : dispatchOrAbstain dflt a b x = none := by
          rw [dispatchOrAbstain]; simp [ha, hb, heq]
        rw [hd] at h; exact absurd h (by simp)
    · have hd : dispatchOrAbstain dflt a b x = some (b.stencil x) := by
        rw [dispatchOrAbstain]; simp [ha, hb]
      rw [hd] at h; injection h with h; exact h.symm

/-- Default correctness: the only value dispatch can return when
NO candidate is in range at `x` is the default. -/
theorem dispatch_sound_default {n : ℕ} (dflt : Bool) (a b : AnfCand n)
    (x : Fin n → Bool) (v : Bool)
    (ha : ¬ inRange a.argRanges x) (hb : ¬ inRange b.argRanges x)
    (h : dispatchOrAbstain dflt a b x = some v) : v = dflt := by
  have hd : dispatchOrAbstain dflt a b x = some dflt := by
    rw [dispatchOrAbstain]; simp [ha, hb]
  rw [hd] at h; injection h with h; exact h.symm

/-- Abstention soundness (no false coverage): when two candidates
collide at `x` (both in range, outputs disagree), dispatch
ABSTAINS — it returns `none`, never a possibly-wrong value. -/
theorem abstain_sound {n : ℕ} (dflt : Bool) (a b : AnfCand n)
    (x : Fin n → Bool) (hcol : collides a b x) :
    dispatchOrAbstain dflt a b x = none := by
  obtain ⟨ha, hb, hne⟩ := hcol
  rw [dispatchOrAbstain]
  simp [ha, hb, hne]

/-- The disjointness composition with C302's guarded-support
story: candidates with DISJOINT nonempty `argRanges` never
collide — both being in range at a context `x` would force the
ranges to be equal (the context's position set determines the
range), contradicting disjointness. Holds for arbitrary stencils
(no supportedness needed), so support-disjoint guarded candidates
(C302 `stencil_guard_sound`) are never spuriously abstained. -/
theorem guard_disjoint_no_collision {n : ℕ} (a b : AnfCand n)
    (hdisj : Disjoint a.argRanges b.argRanges)
    (hne : a.argRanges.Nonempty ∨ b.argRanges.Nonempty) :
    ∀ x, ¬ collides a b x := by
  intro x hcol
  obtain ⟨ha, hb, _⟩ := hcol
  have hrw : a.argRanges = b.argRanges := by
    ext i
    cases hx : x i with
    | true =>
      have h1 := ha i; rw [hx] at h1; simp at h1
      have h2 := hb i; rw [hx] at h2; simp at h2
      simp [h1, h2]
    | false =>
      have h1 := ha i; rw [hx] at h1; simp at h1
      have h2 := hb i; rw [hx] at h2; simp at h2
      simp [h1, h2]
  rw [hrw] at hdisj
  have hbe : b.argRanges = ∅ := by
    have hint := Finset.disjoint_iff_inter_eq_empty.1 hdisj
    rw [Finset.inter_self] at hint
    exact hint
  rcases hne with ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [hrw, hbe] at hi; exact absurd hi (by simp)
  · rw [hbe] at hi; exact absurd hi (by simp)

/-! ## Fin 2 anchors -/

/-- Anchor (abstention fires): two Fin 2 candidates both declared
for the argument range `{0}` with stencils `x₀` and `x₁`; at the
context `[true, false]` (the characteristic point of `{0}`) both
are in range and disagree (`x₀ = true ≠ false = x₁`), so dispatch
abstains (decide). -/
theorem anfFin2_dispatch_abstain :
    dispatchOrAbstain false
      ⟨fun x : Fin 2 → Bool => x 0, {0}⟩
      ⟨fun x : Fin 2 → Bool => x 1, {0}⟩
      (fun i => i = 0) = none := by
  decide

/-- Anchor (dispatch succeeds): two Fin 2 candidates with
DISJOINT ranges `{0}` (stencil `x₀`) and `{1}` (stencil `x₁`); at
the context `[true, false]` only the first is in range, so
dispatch returns exactly its value `true` (decide). -/
theorem anfFin2_dispatch_ok :
    dispatchOrAbstain false
      ⟨fun x : Fin 2 → Bool => x 0, {0}⟩
      ⟨fun x : Fin 2 → Bool => x 1, {1}⟩
      (fun i => i = 0) = some true := by
  decide

end Hagi.Data.AnfDispatch
