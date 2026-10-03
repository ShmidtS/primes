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

/-! ## The one-parameter mixer: root + contrast rotation -/

section MixerParam

/-!
**Prescription for the code (§10–11 of the synthesis).** The
mixer stage between the root and the leaves has exactly one
degree of freedom: an angle θ in the contrast plane. This
section constructs the one-parameter family `Q θ = P_root +
R θ * P_contrast` (the root projector plus a 2D rotation of the
contrast plane), proves it is orthogonal and root-fixing for
*every* θ, and fixes the provenance of the production
`Q(π/2)`: the actual Rodrigues angle of the parent-preserving
matrix is `π/3` (trace 2 ⇒ cos θ = 1/2 — a 60° rotation of the
contrast plane), a lemma about the spectrum.
-/

/-- **The one-parameter mixer in the explicit (e₁, e₂, root)
basis.** `Q θ` is the identity on the root axis (third
coordinate) and the 2D rotation by θ on the contrast plane —
`Q θ = P_root + R θ * P_c` transported to the standard basis of
the production `parentPreservingQ` family (the constructive
root-invariant mixer: one parameter, one invariant). -/
noncomputable def mixerQ (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0;
     Real.sin θ, Real.cos θ, 0;
     0, 0, 1]

/-- **Orthogonality for every θ.** The one-parameter mixer is
orthogonal: `Q θ * (Q θ)ᵀ = 1` — the 2D rotation block
(cos² + sin² = 1) plus the identity on the root axis. -/
theorem mixerQ_orthogonal (θ : ℝ) :
    mixerQ θ * (mixerQ θ)ᵀ = 1 := by
  have key : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := by
    rw [Real.sin_sq_add_cos_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mixerQ, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_three]
  all_goals linarith [key]

/-- **Root-fixing for every θ** (in the mixer basis: the third
axis). The production `parentPreservingQ` is the transport of
this family to the leaf basis; the root invariance is
constructive — no projection needed, the third row *is* the
root axis. -/
theorem mixerQ_root_fixed (θ : ℝ) :
    mixerQ θ *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
  ext i
  fin_cases i
  · simp [mixerQ, Matrix.mulVec, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_three]
  · simp [mixerQ, Matrix.mulVec, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_three]
  · simp [mixerQ, Matrix.mulVec, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_three]

end MixerParam


/-- **Provenance of the production angle (§9).** The
parent-preserving lift `Q(π/2)` (the seed of the
`_PARENT_PRESERVING_TERNARY_Q` digest) is a Rodrigues rotation
about the root axis `(1,1,1)` by the angle `π/3`, not `π/2`: its
trace is `2`, and for a 3D rotation `tr R = 1 + 2 cos θ`, so
`cos θ = 1/2` — a 60° rotation of the contrast plane. The name
`Q(π/2)` is the *parameterization* convention of the code (the
Rodrigues half-angle), not the geometric angle; this lemma fixes
the provenance so the docstrings stop propagating the wrong
angle. The eigenvalues on the contrast plane are
`e^{±iπ/3} = cos(π/3) ± i sin(π/3)`. -/
theorem parentPreservingQ_trace :
    ∑ i, parentPreservingQ i i = 2 := by
  simp [parentPreservingQ, Qentry, Fin.sum_univ_three]
  norm_num

/-- **The geometric angle is π/3 (60°), not π/2.** For a 3D
rotation, `tr Q = 1 + 2 cos θ`; with `tr = 2` this gives
`cos θ = 1/2`, i.e. θ = π/3 — the production `Q(π/2)` is a
*60-degree* Rodrigues rotation about the root axis, and the `π/2`
in the name is a parameterization convention, not the geometric
angle. -/
theorem parentPreservingQ_cos_angle :
    ((∑ i, parentPreservingQ i i) - 1) / 2 = 1/2 := by
  rw [parentPreservingQ_trace]
  norm_num

/-- The geometric angle itself: θ = π/3. -/
theorem parentPreservingQ_theta :
    ∑ i, parentPreservingQ i i = 1 + 2 * Real.cos (Real.pi / 3) := by
  rw [parentPreservingQ_trace]
  norm_num

end Hagi
