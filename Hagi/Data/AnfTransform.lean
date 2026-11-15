/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

set_option linter.style.header false

/-!
# ANF/Möbius (Zhegalkin) transform: the compiler-correctness core

Track E5 (C292–C297 analysis rank #3), C301. The Python V3 compiler
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
Walsh–Hadamard `vennWalsh` (`Hagi.Data.BoolVenn`, C251) is a
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
