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

## Priority dispatch (C314, final E5 rung)

The module ALSO carries the second dispatch policy, formalized in
C314 — the Python V3 arg-range PRIORITY ordering over > 2 stencil
candidates:

- `dispatchPriority`: iterate candidates in list order (priority);
  the FIRST in-range candidate's value wins; later in-range
  candidates are SHADOWED; `none` iff nothing applies. Unlike
  `dispatchOrAbstain` (abstain-on-collide), priority RESOLVES
  overlap by ORDER — BOTH semantics are intentional parts of the
  design; `dispatch_two_eq_priority` proves they coincide on the
  non-colliding overlap (with at least one candidate in range;
  outside it they differ by design: priority returns `none`, the
  abstaining dispatcher its default).
- `dispatchPriority_sound`: acceptance correctness — `some v`
  splits the list as `cs₁ ++ c :: cs₂` with `c` the FIRST
  in-range candidate (all of `cs₁` out of range) and `v` its
  value.
- `dispatchPriority_shadow`: the honest shadowing statement — a
  candidate after an in-range one never determines the result:
  the returned value is some PRECEDING in-range candidate's
  value (a disagreeing later value is provably not returned, by
  `some`-injectivity).
- `dispatchPriority_agree_sound`: under pairwise agreement of all
  in-range candidates, priority dispatch returns exactly the
  common value — the safety pairing with shadowing (the arg-range
  priority must be set so that shadowing only happens on agreeing
  ranges).
- Fin 2 anchors with THREE candidates (decide): shadowing (the
  first two share `{0}` and disagree — first wins) and agreement
  (in-range candidates agree — common value returned).

Honest scope: STATIC priority lists — dynamic re-ranking NOT
claimed; end-to-end Python V3 compiler equivalence NOT claimed.
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


/-! ## Priority dispatch (list order = priority order) -/

/-- The Python V3 arg-range PRIORITY dispatch, certified form:
iterate candidates in list order (priority); return the FIRST
in-range candidate's value; `none` if no candidate applies.
Unlike C306's `dispatchOrAbstain` (which abstains when two
candidates collide disagreeing), priority dispatch RESOLVES
overlap by order: an earlier candidate wins, later in-range
candidates are shadowed (see `dispatchPriority_shadow` for the
honest statement of that fact). -/
def dispatchPriority {n : ℕ} (cands : List (AnfCand n)) (x : Fin n → Bool) :
    Option Bool :=
  match cands with
  | [] => none
  | c :: cs => if inRange c.argRanges x then some (c.stencil x) else dispatchPriority cs x

/-- Coverage: if some candidate in the list is in range, the
priority dispatch returns a value (never abstains). -/
theorem dispatchPriority_eq_some_of_inRange {n : ℕ} (cs : List (AnfCand n))
    (x : Fin n → Bool) (c : AnfCand n) (hc : c ∈ cs) (hin : inRange c.argRanges x) :
    ∃ v, dispatchPriority cs x = some v := by
  induction cs with
  | nil => cases hc
  | cons d ds ih =>
    by_cases hd : inRange d.argRanges x
    · exact ⟨d.stencil x, by simp [dispatchPriority, hd]⟩
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact absurd hin hd
      · have hdd : dispatchPriority (d :: ds) x = dispatchPriority ds x := by
          simp [dispatchPriority, hd]
        rw [hdd]
        exact ih hc

/-- Soundness: if priority dispatch returns `some v`, then the
list splits as `cs₁ ++ c :: cs₂` where `c` is the FIRST in-range
candidate (everything in `cs₁` is out of range) and `v` is
exactly `c`'s value. (First = earliest in list order = highest
priority; the split form is the honest index-free statement of
"first".) -/
theorem dispatchPriority_sound {n : ℕ} (cs : List (AnfCand n)) (x : Fin n → Bool)
    (v : Bool) (h : dispatchPriority cs x = some v) :
    ∃ (cs₁ : List (AnfCand n)) (c : AnfCand n) (cs₂ : List (AnfCand n)),
      cs = cs₁ ++ c :: cs₂ ∧ inRange c.argRanges x ∧ v = c.stencil x ∧
        ∀ d ∈ cs₁, ¬ inRange d.argRanges x := by
  induction cs generalizing v with
  | nil => simp [dispatchPriority] at h
  | cons c cs ih =>
    by_cases hc : inRange c.argRanges x
    · refine ⟨[], c, cs, by simp, hc, ?_, by simp⟩
      have hd : dispatchPriority (c :: cs) x = some (c.stencil x) := by
        simp [dispatchPriority, hc]
      rw [hd] at h
      injection h with h
      exact h.symm
    · have hd : dispatchPriority (c :: cs) x = dispatchPriority cs x := by
        simp [dispatchPriority, hc]
      rw [hd] at h
      obtain ⟨cs₁, d, cs₂, hsplit, hin, hval, hpre⟩ := ih v h
      refine ⟨c :: cs₁, d, cs₂, by rw [hsplit]; simp, hin, hval, ?_⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hc
      · exact hpre e he

/-- Shadowing (the honest statement): if candidate `c` appears
AFTER an in-range candidate `d` (`cs = cs₁ ++ d :: cs₂` with
`c ∈ cs₂`), the dispatch result is the value of some in-range
candidate `e` that ALSO precedes `c` (`c ∈ post`), never `c`'s
own dispatch. When `(cs.get i).stencil x` happens to coincide
with `e`'s value the Booleans agree, but that is agreement, not
dispatch — priority resolved the overlap by ORDER; in particular
a DISAGREEING later candidate's value is provably not returned
(`some` injectivity applied to this theorem: the returned value
is `e.stencil x` for a preceding `e`, so `some c.stencil x` is
returned only under `c.stencil x = e.stencil x`). -/
theorem dispatchPriority_shadow {n : ℕ} (cs₁ cs₂ : List (AnfCand n))
    (d c : AnfCand n) (x : Fin n → Bool)
    (hd : inRange d.argRanges x) (hc : c ∈ cs₂) :
    ∃ (e : AnfCand n) (pre post : List (AnfCand n)),
      cs₁ ++ d :: cs₂ = pre ++ e :: post ∧ inRange e.argRanges x ∧ c ∈ post ∧
        dispatchPriority (cs₁ ++ d :: cs₂) x = some (e.stencil x) := by
  induction cs₁ generalizing d c with
  | nil =>
    refine ⟨d, [], cs₂, by simp, hd, hc, ?_⟩
    simp [dispatchPriority, hd]
  | cons a cs₁ ih =>
    by_cases ha : inRange a.argRanges x
    · refine ⟨a, [], cs₁ ++ d :: cs₂, by simp, ha,
        List.mem_append_right _ (List.mem_cons_of_mem _ hc), ?_⟩
      simp [dispatchPriority, ha]
    · obtain ⟨e, pre, post, hsplit, hin, hcpost, hres⟩ := ih d c hd hc
      refine ⟨e, a :: pre, post, by simp [hsplit], hin, hcpost, ?_⟩
      have hstep : dispatchPriority (a :: (cs₁ ++ d :: cs₂)) x
          = dispatchPriority (cs₁ ++ d :: cs₂) x := by
        simp only [dispatchPriority, ha, ite_false]
      rw [List.cons_append, hstep]
      exact hres

/-- Agreement soundness: if candidate `c` is in range and EVERY
in-range candidate in the list agrees with it at `x`, the
priority dispatch returns exactly the common value — under
pairwise agreement the arg-range priority ordering is safe
(shadowing only hides agreeing candidates). This is the
safety-relevant pairing with `dispatchPriority_shadow`. -/
theorem dispatchPriority_agree_sound {n : ℕ} (cs : List (AnfCand n))
    (x : Fin n → Bool) (c : AnfCand n) (hc : c ∈ cs)
    (hin : inRange c.argRanges x)
    (hagr : ∀ d ∈ cs, inRange d.argRanges x → d.stencil x = c.stencil x) :
    dispatchPriority cs x = some (c.stencil x) := by
  induction cs with
  | nil => cases hc
  | cons d ds ih =>
    by_cases hd : inRange d.argRanges x
    · have hag : d.stencil x = c.stencil x := hagr d (by simp) hd
      have hdd : dispatchPriority (d :: ds) x = some (d.stencil x) := by
        simp only [dispatchPriority, hd, ite_true]
      rw [hdd, hag]
    · have hdd : dispatchPriority (d :: ds) x = dispatchPriority ds x := by
        simp only [dispatchPriority, hd, ite_false]
      rw [hdd]
      refine ih ?_ ?_
      · rcases List.mem_cons.1 hc with rfl | hc
        · exact absurd hin hd
        · exact hc
      · intro e he hin'
        exact hagr e (List.mem_cons_of_mem _ he) hin'

/-- Semantic bridge to C306: for a two-candidate list with NO
collision and at least one candidate in range, the priority
dispatch returns exactly what `dispatchOrAbstain` returns — the
two dispatchers are consistent on the non-colliding overlap of
their domains. (Outside that overlap the semantics differ by
design: with NO candidate in range, priority returns `none`
while the abstaining dispatcher returns its default.) -/
theorem dispatch_two_eq_priority {n : ℕ} (dflt : Bool) (a b : AnfCand n)
    (x : Fin n → Bool) (hnc : ¬ collides a b x)
    (hany : inRange a.argRanges x ∨ inRange b.argRanges x) :
    dispatchPriority [a, b] x = dispatchOrAbstain dflt a b x := by
  rcases hany with ha | hb
  · by_cases hb' : inRange b.argRanges x
    · have heq : a.stencil x = b.stencil x := by
        by_contra h
        exact hnc ⟨ha, hb', h⟩
      simp [dispatchPriority, dispatchOrAbstain, ha, hb', heq]
    · simp [dispatchPriority, dispatchOrAbstain, ha, hb']
  · by_cases ha' : inRange a.argRanges x
    · have heq : a.stencil x = b.stencil x := by
        by_contra h
        exact hnc ⟨ha', hb, h⟩
      simp [dispatchPriority, dispatchOrAbstain, ha', hb, heq]
    · simp [dispatchPriority, dispatchOrAbstain, ha', hb]

/-! ## Fin 2 anchors: three candidates -/

/-- Anchor (shadowing fires): three Fin 2 candidates; the first
two are BOTH declared for `{0}` (priority order!) with stencils
`x₀` and `¬x₀` — they disagree at the context `[true, false]`;
the third is out of range. Priority dispatch returns the FIRST
candidate's value `true`; the disagreeing second candidate is
shadowed (its `false` is never returned) — by `decide`. -/
theorem anfFin2_priority_shadow :
    dispatchPriority
      [⟨fun x : Fin 2 → Bool => x 0, {0}⟩,
       ⟨fun x : Fin 2 → Bool => !x 0, {0}⟩,
       ⟨fun x : Fin 2 → Bool => x 1, {1}⟩]
      (fun i => i = 0) = some true := by
  decide

/-- Anchor (agreement): three Fin 2 candidates; two are declared
for `{0}` with the SAME stencil `x₀` (in range and agreeing at
`[true, false]`), the third is out of range. Priority dispatch
returns the common value `true` — the `dispatchPriority_agree_
sound` instance — by `decide`. -/
theorem anfFin2_priority_agree :
    dispatchPriority
      [⟨fun x : Fin 2 → Bool => x 0, {0}⟩,
       ⟨fun x : Fin 2 → Bool => !x 0, {1}⟩,
       ⟨fun x : Fin 2 → Bool => x 0, {0}⟩]
      (fun i => i = 0) = some true := by
  decide

end Hagi.Data.AnfDispatch
