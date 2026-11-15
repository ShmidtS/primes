/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Data.AnfTransform

set_option linter.style.header false

/-!
# ANF composition (compose3 seed) with guarded support

Track E5 ladder rung 2 (TD E5-C301 rung 1: `compose3`), C302. The
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

Honest scope (E5 ladder, follow-up beats): collision abstention
and argument-range dispatch are NOT claimed here — only the
composition seed, its synthesis instances, and support soundness.
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
