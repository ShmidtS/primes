/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# The parent-preserving ternary lift `Q(π/2)`

This module formalizes the outer orthogonal lift of the HAGI_v2 ternary
F3 tree (`ParentPreservingTernaryLift`,
`src/hagi/model/merge.py`, `docs/ARCHITECTURE_V2.md`):

> The matrix is orthogonal and fixes `(1, 1, 1)`. Consequently, lifting
> three identical parent copies is the identity on their diagonal.

The lift is the rotation

```
    ⎡ 2/3  -1/3   2/3 ⎤
Q = ⎢ 2/3   2/3  -1/3 ⎥,
    ⎣-1/3   2/3   2/3 ⎦
```

applied per channel to the three parent branches. Formalized here:

* `Hagi.parentPreservingQ_mul_transpose` — `Q * Qᵀ = 1`: the lift is
  orthogonal (a rotation), so it preserves the dot product — the lift
  itself is information-neutral.
* `Hagi.parentPreservingQ_diag` — `Q *ᵥ (x, x, x) = (x, x, x)`: the
  lift fixes the diagonal *pointwise*. This is the entire reason the
  depth of the F3 tree is meaningful: lifting three identical copies
  of a parent is the identity, so the parent's logits survive the lift
  (the concat==child invariant of the tree path,
  `tests/test_merge_invariants.py`).
* `Hagi.parentPreservingQ_leafSub` — the leaf subspace
  `{(x₁, x₂, x₃) | x₁ + x₂ + x₃ = 0}` (the sibling-difference signal)
  is invariant under `Q`: sibling differences stay sibling
  differences, they never leak into the parent's root mode.
* `Hagi.diagonalAdd_preserves_equality` — the root-mode cortex
  invariant (ARCHITECTURE_V2 "Решение: кора ходит по root-моде"): if
  the three leaves are equal and the added contribution is the same in
  every leaf (i.e. lies on the diagonal — exactly how `RootModeCortex`
  writes), then the leaves remain equal, so `BlockTreeNorm` still sees
  identical statistics and the identity invariant holds at
  initialization.
-/

open scoped Matrix

namespace Hagi

/-- Entry table of the lift `Q(π/2)`, indexed by the first three
naturals (`_PARENT_PRESERVING_TERNARY_Q` in `src/hagi/model/merge.py`). -/
noncomputable def Qentry : ℕ → ℕ → ℝ
  | 0, 0 => (2 : ℝ) / 3
  | 0, 1 => -1 / 3
  | 0, 2 => 2 / 3
  | 1, 0 => 2 / 3
  | 1, 1 => 2 / 3
  | 1, 2 => -1 / 3
  | 2, 0 => -1 / 3
  | 2, 1 => 2 / 3
  | 2, 2 => 2 / 3
  | _, _ => 0

noncomputable def parentPreservingQ : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => Qentry (i : ℕ) (j : ℕ)

/-- **The lift is orthogonal.** `Q * Qᵀ = 1`: the parent-preserving lift
is a rotation, preserving the dot product — information-neutral. -/
theorem parentPreservingQ_mul_transpose :
    parentPreservingQ * parentPreservingQᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      parentPreservingQ, Matrix.of_apply, Qentry] <;>
    norm_num

/-- **The lift fixes the diagonal pointwise.** `Q *ᵥ (x, x, x) = (x, x, x)`
for every channel value `x`. Lifting three identical copies of a parent
is the identity on their diagonal — the property that makes the depth
of the ternary tree meaningful (the parent's logits survive the lift;
STATUS.md: «Это единственное свойство, ради которого существует
глубина»). -/
theorem parentPreservingQ_diag (x : ℝ) :
    parentPreservingQ *ᵥ (fun _ => x) = fun _ => x := by
  ext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      parentPreservingQ, Matrix.of_apply, Qentry] <;>
    norm_num <;> field_simp <;> ring

/-- **The leaf subspace is invariant.** The sibling-difference signals
`(x₁, x₂, x₃)` with `x₁ + x₂ + x₃ = 0` stay in that subspace under
the lift: sibling differences never leak into the parent's root mode
(ARCHITECTURE_V2: «листовые моды … выше не поднимаются»). -/
theorem parentPreservingQ_leafSub (v : Fin 3 → ℝ)
    (hv : v 0 + v 1 + v 2 = 0) :
    (parentPreservingQ *ᵥ v) 0 + (parentPreservingQ *ᵥ v) 1
      + (parentPreservingQ *ᵥ v) 2 = 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    parentPreservingQ, Matrix.of_apply, Qentry]
  norm_num
  linarith

/-- **The root-mode cortex invariant.** If the three leaves are equal
and the added contribution is the same in every leaf (it lies on the
diagonal — how `RootModeCortex` writes, unfolding one value to all
leaves), then the leaves remain equal: `BlockTreeNorm` still sees
identical statistics, and the lift's identity invariant survives the
cortex at initialization. (A dense cortex, writing *different* values
to the leaves, breaks this — hence `config.py:1356` rejecting it for
the tree, ARCHITECTURE_V2 "Почему плотная кора ломает дерево".) -/
theorem diagonalAdd_preserves_equality {V : Type*} [AddCommGroup V]
    (leaves add : Fin 3 → V) (h : ∀ i, leaves i = leaves 0)
    (hc : ∀ i, add i = add 0) (i : Fin 3) :
    leaves i + add i = leaves 0 + add 0 := by
  rw [h i, hc i]

/-- The root projector: the mean of the three branches, broadcast
back to the diagonal — what the root-mode cortex reads and writes
(ARCHITECTURE_V2: `root(h)` is the mean over the leaves; the write
unfolds one value to all leaves). -/
noncomputable def rootProj (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun _ => (v 0 + v 1 + v 2) / 3

theorem rootProj_is_mean (v : Fin 3 → ℝ) (i : Fin 3) :
    rootProj v i = (v 0 + v 1 + v 2) / 3 := rfl

/-- **The lift does not change what the cortex reads.** The root
projector (the mean of the branches) commutes with the
parent-preserving lift: `Q *ᵥ rootProj v = rootProj v` and
`rootProj (Q *ᵥ v) = rootProj v`. The parent channel carries exactly
the mean of the children — before and after the lift — and only it
(the leaf coordinates mix the differences, `parentPreservingQ_leafSub`).
Formal counterpart of ARCHITECTURE_V2's "root-мода … lift её не
трогает", and the explanation of the measured F3 < flat verdict on
init: the root carries the *mean of states*, never the best child,
so any advantage over the mean must come from joint training or the
mixer, not from the lift itself. -/
theorem parentPreservingQ_root_fixed (v : Fin 3 → ℝ) :
    parentPreservingQ *ᵥ rootProj v = rootProj v ∧
      rootProj (parentPreservingQ *ᵥ v) = rootProj v := by
  constructor
  · ext i
    have hdiag := parentPreservingQ_diag ((v 0 + v 1 + v 2) / 3)
    exact congrFun hdiag i
  · -- root of Qv: use leafSub on v - rootProj v
    ext i
    fin_cases i <;>
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, rootProj,
        parentPreservingQ, Matrix.of_apply, Qentry] <;>
      norm_num <;>
      ring

end Hagi
