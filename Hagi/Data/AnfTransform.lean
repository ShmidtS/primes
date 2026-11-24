/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

set_option linter.style.header false

/-!
# ANF/Möbius (Zhegalkin) transform: the compiler-correctness core

Track E5. The Python V3 compiler
side synthesizes Boolean functions into ANF (algebraic normal form)
via the Möbius/Zhegalkin butterfly and evaluates back; this module
lands the ANF CORE bridge on the Lean side, over the exact Boolean
Venn carriers' ambient function space `(Fin n → Bool) → Bool`
(truth tables over a finite type — the `Hagi.Data.BoolVenn` masks
are the `n = 2` instance of this carrier).

Contents:

- `anfTransform`: the Zhegalkin transform as the recursive butterfly
  on the last coordinate — `T f = (T f₀, T f₀ ⊕ T f₁)` where `f₀`
  (`f₁`) is the `last = false` (`true`) half of the truth table.
  Computable definition; `anf_snoc_false`/`anf_snoc_true` are its
  computation rules at a `Fin.snoc` point.
- `anf_add`: the transform is linear over pointwise xor (GF(2)).
- `anf_inversion`: the correctness core — the transform is an
  INVOLUTION (`T (T f) = f` for every `n`): the Möbius inversion on
  the Boolean lattice, proved by the butterfly induction (false
  half: IH; true half: linearity + GF(2) cancellation
  `a ⊕ (a ⊕ b) = b`).
- `anf_subcube`: the truth-table-derived characterization — the
  ANF coefficient at `S` is the parity of `f` over the subcube
  `{x | x ⊆ S}` (`c_S = ⊕_{x ⊆ S} f(x)`), stated in `ZMod 2`
  parity arithmetic (`anfBit`), via the image-split of the subcube
  at the last coordinate (`Finset.sum_image`/`sum_union`).
- `anfEval` + `anf_eval_eq`: evaluating the ANF (the xor of the
  coefficient monomials — the transform itself, since a monomial
  `∧_{i ∈ S} xᵢ` at `x` survives exactly on `S ⊆ x`) reproduces
  `f`: the compile roundtrip `eval ∘ transform = id`, the seed of
  the ANF-compiler correctness story (truth table ↔ ANF synthesis).
- `anfFin2_xor`, `anfFin2_and`, `anfFin2_xor_coeffs`: numeric
  anchors on the `Fin 2` XOR/AND truth tables (decide): transform →
  eval → original, and the XOR coefficient spot check (constant
  term false, single-variable term true — the canonical linear ANF).

Honest scope (E5 ladder, follow-up beats): `compose3`, context
signatures, argument ranges, and collision abstention are NOT
claimed here — only the core transform/involution/roundtrip. The
Walsh–Hadamard `vennWalsh` (`Hagi.Data.BoolVenn`) is a
different transform (±1 character spectrum over ℤ); the ANF
transform is the GF(2) butterfly.
-/

namespace Hagi.Data.AnfTransform

/-! ## The butterfly definition and its computation rules -/

/-- The Zhegalkin (Möbius/ANF) transform as the recursive butterfly:
split the truth table into the `last = false` half `f₀` and the
`last = true` half `f₁`; the transform is `(T f₀, T f₀ ⊕ T f₁)`.
Computable; at `n = 0` it is the identity. -/
def anfTransform : {n : ℕ} → ((Fin n → Bool) → Bool) → ((Fin n → Bool) → Bool)
  | 0, f => f
  | n + 1, f => fun S =>
      if S (Fin.last n) then
        anfTransform (fun t => f (Fin.snoc t false)) (Fin.init S) ^^
          anfTransform (fun t => f (Fin.snoc t true)) (Fin.init S)
      else anfTransform (fun t => f (Fin.snoc t false)) (Fin.init S)

/-- Computation rule of the butterfly at a `Fin.snoc` point
(definitional: `Fin.snoc_last` + `Fin.init_snoc`). -/
theorem anf_snoc {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool)
    (t : Fin n → Bool) (b : Bool) :
    anfTransform f (Fin.snoc t b) =
      (if b = true then
        (anfTransform (fun t => f (Fin.snoc t false)) t ^^
          anfTransform (fun t => f (Fin.snoc t true)) t)
      else anfTransform (fun t => f (Fin.snoc t false)) t) := by
  simp only [anfTransform, Fin.snoc_last, Fin.init_snoc]

/-- False-half computation rule: the coefficient at `snoc t false`
is the transform of the false half. -/
theorem anf_snoc_false {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool)
    (t : Fin n → Bool) :
    anfTransform f (Fin.snoc t false)
      = anfTransform (fun t => f (Fin.snoc t false)) t := by
  rw [anf_snoc]
  split
  · next h => exact absurd h (by simp)
  · rfl

/-- True-half computation rule: the coefficient at `snoc t true`
is `false`-half transform ⊕ `true`-half transform. -/
theorem anf_snoc_true {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool)
    (t : Fin n → Bool) :
    anfTransform f (Fin.snoc t true)
      = (anfTransform (fun t => f (Fin.snoc t false)) t ^^
          anfTransform (fun t => f (Fin.snoc t true)) t) := by
  rw [anf_snoc]
  split
  · rfl
  · next h => exact absurd h (by simp)

/-- GF(2) four-term shuffle (decide-level; the pinned Mathlib has no
`Std.Commutative Bool.xor` instances to delegate to). -/
theorem anf_xor4 (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-! ## Linearity and the involution -/

/-- Linearity: the transform is additive over pointwise xor —
GF(2)-linearity of the butterfly. -/
theorem anf_add {n : ℕ} (g h : (Fin n → Bool) → Bool) :
    ∀ S, anfTransform (fun S => g S ^^ h S) S
      = (anfTransform g S ^^ anfTransform h S) := by
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    obtain ⟨t, b, rfl⟩ : ∃ t b, S = Fin.snoc t b :=
      ⟨Fin.init S, S (Fin.last n), (Fin.snoc_init_self S).symm⟩
    cases b with
    | false =>
      rw [anf_snoc_false, anf_snoc_false, anf_snoc_false]
      exact ih (fun s => g (Fin.snoc s false))
        (fun s => h (Fin.snoc s false)) t
    | true =>
      rw [anf_snoc_true, anf_snoc_true, anf_snoc_true,
        ih (fun s => g (Fin.snoc s false)) (fun s => h (Fin.snoc s false)) t,
        ih (fun s => g (Fin.snoc s true)) (fun s => h (Fin.snoc s true)) t,
        anf_xor4]

/-- THE correctness core: the Zhegalkin transform is an involution
— applying it twice returns the original truth table. This is the
Möbius inversion on the Boolean lattice (the textbook
`Σ_{T⊆S} Σ_{U⊆T} ≡ 1 mod 2` argument, realized structurally: the
false half is the IH outright, the true half is linearity
`anf_add` plus the GF(2) cancellation `a ⊕ (a ⊕ b) = b`). -/
theorem anf_inversion {n : ℕ} (f : (Fin n → Bool) → Bool) :
    anfTransform (anfTransform f) = f := by
  induction n with
  | zero => funext S; rfl
  | succ n ih =>
    have ih0 := congrFun (ih (fun t => f (Fin.snoc t false)))
    have ih1 := congrFun (ih (fun t => f (Fin.snoc t true)))
    have h0f : (fun t => anfTransform f (Fin.snoc t false))
        = anfTransform (fun t => f (Fin.snoc t false)) :=
      funext (anf_snoc_false f)
    have h1f : (fun t => anfTransform f (Fin.snoc t true))
        = (fun t => (anfTransform (fun t => f (Fin.snoc t false)) t ^^
            anfTransform (fun t => f (Fin.snoc t true)) t)) :=
      funext fun t => anf_snoc_true f t
    funext S
    obtain ⟨t, b, rfl⟩ : ∃ t b, S = Fin.snoc t b :=
      ⟨Fin.init S, S (Fin.last n), (Fin.snoc_init_self S).symm⟩
    cases b with
    | false =>
      rw [anf_snoc_false, h0f]
      exact ih0 t
    | true =>
      rw [anf_snoc_true, h0f, h1f, anf_add, ih0, ih1, ← Bool.xor_assoc,
        Bool.xor_self]
      simp

/-! ## The subcube parity characterization -/

/-- The subcube below `S`: the truth-table points `x ⊆ S`
(pointwise implication). -/
def subcube {n : ℕ} (S : Fin n → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => ∀ i, x i → S i)

/-- The false half of a subcube is the snoc-false image of the
smaller subcube. -/
theorem subcube_snoc_false {n : ℕ} (t : Fin n → Bool) :
    subcube (Fin.snoc t false)
      = (subcube t).image
        (fun x => (Fin.snoc x false : Fin (n + 1) → Bool)) := by
  ext x
  simp only [subcube, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro h
    have hlast : x (Fin.last n) = false := by
      cases hb : x (Fin.last n) with
      | false => rfl
      | true => exact absurd (h (Fin.last n) hb) (by simp)
    refine ⟨Fin.init x, ?_, ?_⟩
    · intro i hi; simpa [Fin.snoc_castSucc] using h (Fin.castSucc i) hi
    · rw [← hlast, Fin.snoc_init_self]
  · rintro ⟨x', hx', rfl⟩ i hi
    induction i using Fin.lastCases with
    | cast j =>
      have hj : x' j = true := by simpa [Fin.snoc_castSucc] using hi
      simpa [Fin.snoc_castSucc] using hx' j hj
    | last => exact absurd hi (by simp [Fin.snoc_last])

/-- The full subcube splits at the last coordinate into the two
snoc images (disjoint: the halves differ at the last bit). -/
theorem subcube_snoc_true {n : ℕ} (t : Fin n → Bool) :
    subcube (Fin.snoc t true)
      = ((subcube t).image
          (fun x => (Fin.snoc x false : Fin (n + 1) → Bool)) ∪
        (subcube t).image
          (fun x => (Fin.snoc x true : Fin (n + 1) → Bool))) := by
  ext x
  simp only [subcube, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · intro h
    cases hb : x (Fin.last n) with
    | false =>
      refine Or.inl ⟨Fin.init x, ?_, ?_⟩
      · intro i hi; simpa [Fin.snoc_castSucc] using h (Fin.castSucc i) hi
      · rw [← hb, Fin.snoc_init_self]
    | true =>
      refine Or.inr ⟨Fin.init x, ?_, ?_⟩
      · intro i hi; simpa [Fin.snoc_castSucc] using h (Fin.castSucc i) hi
      · rw [← hb, Fin.snoc_init_self]
  · rintro (⟨x', hx', rfl⟩ | ⟨x', hx', rfl⟩) i hi
    · induction i using Fin.lastCases with
      | cast j =>
        have hj : x' j = true := by simpa [Fin.snoc_castSucc] using hi
        simpa [Fin.snoc_castSucc] using hx' j hj
      | last => exact absurd hi (by simp [Fin.snoc_last])
    · induction i using Fin.lastCases with
      | cast j =>
        have hj : x' j = true := by simpa [Fin.snoc_castSucc] using hi
        simpa [Fin.snoc_castSucc] using hx' j hj
      | last => simp [Fin.snoc_last]

/-- The two snoc maps are injective (for `Finset.sum_image`). -/
theorem anfSnocInjOn {n : ℕ} (c : Bool) (s : Finset (Fin n → Bool)) :
    Set.InjOn (fun x : Fin n → Bool => (Fin.snoc x c : Fin (n + 1) → Bool))
      (s : Set _) := by
  intro a _ b _ h
  simpa [Fin.init_snoc] using congrArg Fin.init h

/-- The two snoc images are disjoint (the halves differ at the last
bit). -/
theorem anfDisjointSnocImages {n : ℕ} (t : Fin n → Bool) :
    Disjoint ((subcube t).image
        (fun x => (Fin.snoc x false : Fin (n + 1) → Bool)))
      ((subcube t).image
        (fun x => (Fin.snoc x true : Fin (n + 1) → Bool))) := by
  rw [Finset.disjoint_iff_ne]
  intro x hx y hy hcon
  rcases Finset.mem_image.1 hx with ⟨a, _, rfl⟩
  rcases Finset.mem_image.1 hy with ⟨b, _, rfl⟩
  exact absurd (congrFun hcon (Fin.last n)) (by simp)

/-- The Bool → GF(2) coercion for parity sums. -/
def anfBit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- XOR is addition in GF(2). -/
theorem anfBit_xor (a b : Bool) :
    anfBit (a ^^ b) = (anfBit a + anfBit b) := by
  unfold anfBit; cases a <;> cases b <;> decide

/-- The truth-table-derived characterization: the ANF coefficient
at `S` is the parity of `f` over the subcube `x ⊆ S` — the textbook
`c_S = ⊕_{x ⊆ S} f(x)`. The butterfly definition and the subcube
sum are the same transform. -/
theorem anf_subcube : ∀ {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Fin n → Bool), anfBit (anfTransform f S)
      = (∑ x ∈ subcube S, anfBit (f x)) := by
  intro n
  induction n with
  | zero =>
    intro f S
    have hsingle : ∀ x : Fin 0 → Bool, x = Fin.elim0 :=
      fun x => funext fun i => Fin.elim0 i
    rw [Finset.sum_eq_single (Fin.elim0 : Fin 0 → Bool)]
    · rw [hsingle S]; rfl
    · intro x _ hx; exact absurd (hsingle x) hx
    · intro h; exact absurd (Finset.mem_univ _) h
  | succ n ih =>
    intro f S
    obtain ⟨t, b, rfl⟩ : ∃ t b, S = Fin.snoc t b :=
      ⟨Fin.init S, S (Fin.last n), (Fin.snoc_init_self S).symm⟩
    cases b with
    | false =>
      rw [subcube_snoc_false, Finset.sum_image
        (anfSnocInjOn false (subcube t)), anf_snoc_false f t]
      exact ih (fun s => f (Fin.snoc s false)) t
    | true =>
      rw [subcube_snoc_true, Finset.sum_union
        (anfDisjointSnocImages t),
        Finset.sum_image (anfSnocInjOn false (subcube t)),
        Finset.sum_image (anfSnocInjOn true (subcube t)),
        ← ih (fun s => f (Fin.snoc s false)) t,
        ← ih (fun s => f (Fin.snoc s true)) t,
        ← anfBit_xor, anf_snoc_true f t]

/-! ## Evaluation and the compile roundtrip -/

/-- ANF evaluation: the polynomial `⊕_S c_S · ∧_{i ∈ S} xᵢ`. The
monomial at `x` survives exactly on `S ⊆ x`, so the evaluation sum
IS the transform of the coefficient table at `x`. -/
def anfEval {n : ℕ} (c : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    Bool := anfTransform c x

/-- The compiler-correctness seed: synthesizing ANF coefficients
from the truth table (`anfTransform`) and evaluating the ANF back
(`anfEval`) returns the original function — the truth table ↔ ANF
roundtrip, for every `n`. -/
theorem anf_eval_eq {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∀ x, anfEval (anfTransform f) x = f x := by
  intro x
  rw [anfEval, anf_inversion f]

/-! ## Numeric anchors on the two-variable (Fin 2) truth tables -/

/-- Anchor (XOR): transform → eval → original on the `Fin 2` XOR
truth table — the canonical linear ANF carrier. -/
theorem anfFin2_xor :
    anfEval (anfTransform (fun x : Fin 2 → Bool => x 0 ^^ x 1))
      = (fun x : Fin 2 → Bool => x 0 ^^ x 1) := by
  funext x
  rw [anf_eval_eq]

/-- Anchor (AND): transform → eval → original on the `Fin 2` AND
truth table — the canonical degree-2 ANF carrier. -/
theorem anfFin2_and :
    anfEval (anfTransform (fun x : Fin 2 → Bool => x 0 && x 1))
      = (fun x : Fin 2 → Bool => x 0 && x 1) := by
  funext x
  rw [anf_eval_eq]

/-- Coefficient spot check (XOR): the constant coefficient is
`false` and the single-variable coefficient `{0}` is `true` — the
transform of XOR is the linear ANF `x₀ ⊕ x₁` (decide). -/
theorem anfFin2_xor_coeffs :
    anfTransform (fun x : Fin 2 → Bool => x 0 ^^ x 1) (fun _ => false)
      = false ∧
    anfTransform (fun x : Fin 2 → Bool => x 0 ^^ x 1)
      (fun i => i = 0) = true := by
  decide

end Hagi.Data.AnfTransform

set_option linter.style.header false

/-!
# ANF composition (compose3 seed) with guarded support

Track E5 ladder rung 2 (rung 1: `compose3`). The
Python V3 compiler composes Boolean stencil functions via
`compose3(f, g, h) = f(g(x), h(x))` nests over ANF-compiled truth
tables. This module lands the SEED case honestly on the
`Hagi.Data.AnfTransform` carriers:

- `anfCompose`: the truth-table-level composition — outer
  `f : Bool → Bool → Bool`, inner `g, h : (Fin n → Bool) → Bool`
  on their shared variable set — `anfCompose f g h x
  = f (g x) (h x)`.
- `anfCompose_coeff`: the ANF coefficients of the composition are
  the transform of the composed truth table, in the subcube-parity
  form (`c_S = ⊕_{x ⊆ S} f(g(x), h(x))` — an INSTANCE of
  `anf_subcube`, packaged as the compose3 API).
- `anfCompose_eval`: the compile roundtrip for the composition —
  evaluating the synthesized ANF reproduces the composed function
  (an INSTANCE of `anf_eval_eq`, compose3 packaging). Composition
  at the eval level is definitional; the theorem pins the
  synthesis pipeline to it.
- `anfAgreeOn` / `anfSupportedOn` / `stencil_guard_sound`:
  context-guard soundness seed — support-dependence (`g x = g y`
  whenever `x`, `y` agree on the index set `S`) composes: if `g`
  and `h` are S-supported then so is `anfCompose f g h` for ANY
  outer `f`. This is the Python context-signature abstention
  CORRECTNESS direction: a guarded composition never claims
  coverage beyond its components' support (no false coverage).
  The converse fails (constant outer `f` kills dependence) and is
  not claimed.
- `anfFin2_compose`, `anfFin2_compose_spot`: the Fin 2 anchor —
  outer OR, inner AND and XOR — transform → eval roundtrip, plus a
  decide-level numeric spot through the full pipeline.

Degree note (documentation only, not claimed as a theorem): over
GF(2) ANF, `deg (f ∘ (g, h)) ≤ deg f · max (deg g, deg h)`; the
truth-table carrier here has no monomial/degree API yet — proving
it needs a polynomial representation first (a later rung).

Honest scope: collision abstention and argument-range dispatch are
NOT claimed here — only the composition seed, its synthesis instances, and
support soundness.
-/

namespace Hagi.Data.AnfCompose

open Hagi.Data.AnfTransform

/-! ## The compose3 seed at the truth-table level -/

/-- The Python `compose3(f, g, h) = f(g(x), h(x))` nest on the
AnfTransform carriers: outer `f` on `Bool × Bool`, inner `g`, `h`
on the shared finite variable set `Fin n`. -/
def anfCompose {n : ℕ} (f : Bool → Bool → Bool)
    (g h : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => f (g x) (h x)

/-- The ANF coefficients of the composition, in the subcube-parity
form: the coefficient at `S` is the parity of the composed table
`x ↦ f (g x) (h x)` over `{x ⊆ S}` — an instance of `anf_subcube`,
packaged as the compose3 API. -/
theorem anfCompose_coeff {n : ℕ} (f : Bool → Bool → Bool)
    (g h : (Fin n → Bool) → Bool) (S : Fin n → Bool) :
    anfBit (anfTransform (anfCompose f g h) S)
      = (∑ x ∈ subcube S, anfBit (f (g x) (h x))) :=
  anf_subcube _ _

/-- The compile roundtrip for the composition: the ANF synthesized
from the composed truth table evaluates back to the composed
function — an instance of `anf_eval_eq`, packaged as the compose3
API the Python compiler uses. -/
theorem anfCompose_eval {n : ℕ} (f : Bool → Bool → Bool)
    (g h : (Fin n → Bool) → Bool) :
    ∀ x, anfEval (anfTransform (anfCompose f g h)) x
      = f (g x) (h x) :=
  fun x => anf_eval_eq _ x

/-! ## Context-guard (support) soundness -/

/-- Agreement of two truth-table points on an index support `S`. -/
def anfAgreeOn {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → Bool) :
    Prop := ∀ i ∈ S, x i = y i

/-- Support-dependence: `g` depends only on the indices in `S` —
`g` is constant on the fibers of the `S`-slice. -/
def anfSupportedOn {n : ℕ} (S : Finset (Fin n))
    (g : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, anfAgreeOn S x y → g x = g y

/-- Context guards compose (the Python context-signature
abstention correctness direction — no false coverage): if the
inner functions `g`, `h` each depend only on the index set `S`,
then the composed function `anfCompose f g h` depends only on
`S`, for ANY outer `f` — a guard on the composition is justified
by guards on the components. -/
theorem stencil_guard_sound {n : ℕ} (S : Finset (Fin n))
    (f : Bool → Bool → Bool)
    (g h : (Fin n → Bool) → Bool)
    (hg : anfSupportedOn S g) (hh : anfSupportedOn S h) :
    anfSupportedOn S (anfCompose f g h) := by
  intro x y hxy
  show f (g x) (h x) = f (g y) (h y)
  rw [hg x y hxy, hh x y hxy]

/-! ## Fin 2 anchor: f = OR, g = AND, h = XOR -/

/-- Anchor: compose → transform → eval roundtrip on the Fin 2
OR∘(AND, XOR) nest — the Python-analog two-variable setting. -/
theorem anfFin2_compose :
    anfEval (anfTransform (anfCompose (fun a b => a || b)
      (fun x : Fin 2 → Bool => x 0 && x 1)
      (fun x : Fin 2 → Bool => x 0 ^^ x 1)))
      = (fun x : Fin 2 → Bool => (x 0 && x 1) || (x 0 ^^ x 1)) := by
  funext x
  rw [anfCompose_eval]

/-- Numeric spot (decide): the anchor composed function at the
`[true, false]` point is `true` (AND = false, XOR = true, OR =
true), computed through the full transform → eval pipeline. -/
theorem anfFin2_compose_spot :
    anfEval (anfTransform (anfCompose (fun a b => a || b)
      (fun x : Fin 2 → Bool => x 0 && x 1)
      (fun x : Fin 2 → Bool => x 0 ^^ x 1)))
      (fun i => i = 0) = true := by
  decide

end Hagi.Data.AnfCompose

set_option linter.style.header false

/-!
# ANF dispatch with collision abstention

Track E5 ladder rung 3 (rungs 3+4: argument ranges + collision
abstention). The Python V3 compiler
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
- `guard_disjoint_no_collision`: the composition with the guarded-support
  story — candidates with DISJOINT
  (nonempty) `argRanges` NEVER collide (both in range at `x`
  would force the ranges equal, contradicting disjointness), so
  the abstention never fires spuriously for support-disjoint
  candidates. The lemma needs no supportedness hypothesis — it
  holds for arbitrary stencils, strengthening the guard
  composition.
- `anfFin2_dispatch_abstain`, `anfFin2_dispatch_ok`: the Fin 2
  anchor — a colliding pair (both ranges `{0}`, stencils `x₀` and
  `x₁`, context `[true, false]` → abstain) and a disjoint pair
  (`{0}` vs `{1}` → dispatch returns the applicable candidate's
  value), both by `decide`.

## Priority dispatch (final E5 rung)

The module ALSO carries the second dispatch policy — the Python V3
arg-range PRIORITY ordering over > 2 stencil candidates:

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

/-- The disjointness composition with the guarded-support
story: candidates with DISJOINT nonempty `argRanges` never
collide — both being in range at a context `x` would force the
ranges to be equal (the context's position set determines the
range), contradicting disjointness. Holds for arbitrary stencils
(no supportedness needed), so support-disjoint guarded candidates
(`stencil_guard_sound`) are never spuriously abstained. -/
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
Unlike `dispatchOrAbstain` (which abstains when two
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

/-- Semantic bridge to for a two-candidate list with NO
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
