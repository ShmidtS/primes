/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# The parent-preserving ternary lift

The lift is the rotation

```
    ⎡ 2/3  -1/3   2/3 ⎤
Q = ⎢ 2/3   2/3  -1/3 ⎥,
    ⎣-1/3   2/3   2/3 ⎦
```

applied per channel to the three parent branches (`Qentry`,
`parentPreservingQ`).

* `parentPreservingQ_mul_transpose` — `Q * Qᵀ = 1` (orthogonal).
* `parentPreservingQ_diag` — `Q *ᵥ (x, x, x) = (x, x, x)`: lifting
  three identical copies of a parent is the identity.
* `parentPreservingQ_leafSub` — the leaf subspace
  `{v | v 0 + v 1 + v 2 = 0}` is invariant under `Q`.
* `diagonalAdd_preserves_equality` — if the three leaves are equal
  and the added contributions are equal, the sums remain equal.
* `parentPreservingQ_root_fixed` — the root projector commutes with
  `Q`.
* `parentPreservingQ_trace`, `parentPreservingQ_cos_angle`,
  `parentPreservingQ_theta` — the trace is `2`, i.e. the geometric
  rotation angle about the root axis is `π/3`.
* `mixerQ`, `mixerQ_orthogonal`, `mixerQ_root_fixed` — the
  one-parameter mixer (2D rotation of the contrast plane plus the
  identity on the root axis), orthogonal and root-fixing for every
  `θ`.
-/

open scoped Matrix

namespace Hagi.Core

/-- Entry table of the lift `Q`, indexed by the first three
naturals. -/
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

/-- The lift is orthogonal: `parentPreservingQ * parentPreservingQᵀ = 1`. -/
theorem parentPreservingQ_mul_transpose :
    parentPreservingQ * parentPreservingQᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      parentPreservingQ, Matrix.of_apply, Qentry] <;>
    norm_num

/-- The lift fixes the diagonal pointwise:
`parentPreservingQ *ᵥ (fun _ => x) = fun _ => x` for every `x`. -/
theorem parentPreservingQ_diag (x : ℝ) :
    parentPreservingQ *ᵥ (fun _ => x) = fun _ => x := by
  ext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      parentPreservingQ, Matrix.of_apply, Qentry] <;>
    norm_num <;> field_simp <;> ring

/-- The leaf subspace `{v | v 0 + v 1 + v 2 = 0}` is invariant
under the lift. -/
theorem parentPreservingQ_leafSub (v : Fin 3 → ℝ)
    (hv : v 0 + v 1 + v 2 = 0) :
    (parentPreservingQ *ᵥ v) 0 + (parentPreservingQ *ᵥ v) 1
      + (parentPreservingQ *ᵥ v) 2 = 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    parentPreservingQ, Matrix.of_apply, Qentry]
  norm_num
  linarith

/-- If the three leaves are equal (`h`) and the added
contributions are equal (`hc`), then `leaves i + add i =
leaves 0 + add 0` for every `i`. -/
theorem diagonalAdd_preserves_equality {V : Type*} [AddCommGroup V]
    (leaves add : Fin 3 → V) (h : ∀ i, leaves i = leaves 0)
    (hc : ∀ i, add i = add 0) (i : Fin 3) :
    leaves i + add i = leaves 0 + add 0 := by
  rw [h i, hc i]

/-- The root projector: the mean of the three branches, broadcast
back to the diagonal. -/
noncomputable def rootProj (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun _ => (v 0 + v 1 + v 2) / 3

theorem rootProj_is_mean (v : Fin 3 → ℝ) (i : Fin 3) :
    rootProj v i = (v 0 + v 1 + v 2) / 3 := rfl

/-- The root projector commutes with the lift:
`Q *ᵥ rootProj v = rootProj v` and `rootProj (Q *ᵥ v) = rootProj v`. -/
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
The one-parameter mixer family: a 2D rotation of the contrast
plane plus the identity on the root axis; orthogonal and
root-fixing for every `θ`.
-/

/-- The one-parameter mixer in the explicit (e₁, e₂, root)
basis: the 2D rotation by θ on the contrast plane and the
identity on the root axis. -/
noncomputable def mixerQ (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0;
     Real.sin θ, Real.cos θ, 0;
     0, 0, 1]

/-- `mixerQ θ * (mixerQ θ)ᵀ = 1` for every `θ`. -/
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

/-- `mixerQ θ *ᵥ ![0, 0, 1] = ![0, 0, 1]` for every `θ`: the
mixer fixes the root axis. -/
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


/-- The trace of the lift is `2`. -/
theorem parentPreservingQ_trace :
    ∑ i, parentPreservingQ i i = 2 := by
  simp [parentPreservingQ, Qentry, Fin.sum_univ_three]
  norm_num

/-- `((∑ i, parentPreservingQ i i) - 1) / 2 = 1/2`; combined
with `tr R = 1 + 2 cos θ` for a 3D rotation, the geometric
rotation angle is `π/3`. -/
theorem parentPreservingQ_cos_angle :
    ((∑ i, parentPreservingQ i i) - 1) / 2 = 1/2 := by
  rw [parentPreservingQ_trace]
  norm_num

/-- The trace equals `1 + 2 * Real.cos (Real.pi / 3)`: the
geometric rotation angle is `π/3`. -/
theorem parentPreservingQ_theta :
    ∑ i, parentPreservingQ i i = 1 + 2 * Real.cos (Real.pi / 3) := by
  rw [parentPreservingQ_trace]
  norm_num

end Hagi.Core

namespace Hagi
export Hagi.Core (Qentry parentPreservingQ parentPreservingQ_mul_transpose parentPreservingQ_diag parentPreservingQ_leafSub diagonalAdd_preserves_equality rootProj rootProj_is_mean parentPreservingQ_root_fixed mixerQ mixerQ_orthogonal mixerQ_root_fixed parentPreservingQ_trace parentPreservingQ_cos_angle parentPreservingQ_theta)
end Hagi
