/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

set_option linter.style.header false

/-!
# CortexFiber: the energy laws of the shared-cortex ⊕ expert-fiber
geometry (R181)

Source: the hierarchical-geometry hypothesis for HAGI — the
representation lives on

  h = ρ · (U z + Σ V_i r_i) / ‖U z + Σ V_i r_i‖

with a shared orthonormal semantic cortex `U` (dim c ≪ d) and
small orthogonal expert fibers `V_i` (rank r_i ≪ c). The
layerwise expansion→contraction funnel and the specific dims
(256–512, r = 8–64) are EMPIRICAL hypotheses — NOT theorems
here. What IS formalized are the three energy laws that make
the geometry coherent:

* `orthoNorm`: an orthonormal cortex is an isometry —
  ‖U z‖² = ‖z‖² exactly (the cortex never distorts).
* `fiberCross`: orthogonal fibers do not interfere —
  ⟨U z, V r⟩ = 0 exactly when UᵀV = 0 (the no-cross-talk
  law behind "orthogonal alignment before merge").
* `fiberPythagoras`: the cortex⊕fiber split is Pythagorean —
  ‖U z + V r‖² = ‖z‖² + ‖r‖²: energy decomposes WITHOUT a
  cross term; the shared and the expert parts are
  independently controllable (SafeQP constraints on the
  cortex do not fight the fiber updates, and vice versa).
* `fiberParamCount`: an expert fiber of rank r < d costs
  r·d coordinates against d² for a full expert matrix — the
  arithmetic of "an expert is a deformation of the shared
  geometry, not a second model".

NOT claimed: that trained experts actually align to a common
U (the alignment premise is explicit, h_align_-style); that
the optimal cortex dimension is 256–512; that real
representations are spherical.
-/

namespace Hagi.Cortex

open Finset Matrix

/-- Orthonormal columns: Uᵀ U = I (a shared semantic cortex
basis / an aligned fiber basis). -/
def IsOrthoCol {d c : ℕ} (U : Matrix (Fin d) (Fin c) ℝ) : Prop :=
  Uᵀ * U = 1


/-- The key transpose identity: the mixed product equals the
gram-form vecMul. -/
theorem mulVec_vecMul_gram {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (V : Matrix (Fin d) (Fin r) ℝ) (z : Fin c → ℝ) :
    (U *ᵥ z) ᵥ* V = z ᵥ* (Uᵀ * V) := by
  ext i
  simp only [Matrix.vecMul, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- **The cortex is an isometry**: an orthonormal basis
preserves energy exactly — the shared geometry never distorts
the semantic coordinate. -/
theorem orthoNorm {d c : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (hU : IsOrthoCol U) (z : Fin c → ℝ) :
    (U.mulVec z) ⬝ᵥ (U.mulVec z) = z ⬝ᵥ z := by
  have key : (U.mulVec z) ⬝ᵥ (U.mulVec z)
      = z ⬝ᵥ ((Uᵀ * U).mulVec z) := by
    rw [Matrix.dotProduct_mulVec, mulVec_vecMul_gram, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [key, hU, Matrix.one_mulVec]

/-- **Orthogonal fibers do not interfere**: if the cortex and
the fiber bases are orthogonal (Uᵀ V = 0), the cross inner
product vanishes EXACTLY — the no-cross-talk law behind
"orthogonal alignment before merge". -/
theorem fiberCross {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (V : Matrix (Fin d) (Fin r) ℝ) (hUV : Uᵀ * V = 0)
    (z : Fin c → ℝ) (w : Fin r → ℝ) :
    (U.mulVec z) ⬝ᵥ (V.mulVec w) = 0 := by
  have key : (U.mulVec z) ⬝ᵥ (V.mulVec w)
      = z ⬝ᵥ ((Uᵀ * V).mulVec w) := by
    rw [Matrix.dotProduct_mulVec, mulVec_vecMul_gram, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [key, hUV, Matrix.zero_mulVec, dotProduct_zero]

/-- **The cortex ⊕ fiber split is Pythagorean**: with an
orthonormal cortex, an orthonormal fiber, and orthogonality
between them, the energy decomposes WITHOUT a cross term —
‖U z + V w‖² = ‖z‖² + ‖w‖². The shared and expert parts are
independently controllable: SafeQP constraints on the cortex
do not fight fiber updates, and vice versa; merge energies
are additive. -/
theorem fiberPythagoras {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (V : Matrix (Fin d) (Fin r) ℝ)
    (hU : IsOrthoCol U) (hV : IsOrthoCol V) (hUV : Uᵀ * V = 0)
    (z : Fin c → ℝ) (w : Fin r → ℝ) :
    (U.mulVec z + V.mulVec w) ⬝ᵥ (U.mulVec z + V.mulVec w)
      = z ⬝ᵥ z + w ⬝ᵥ w := by
  have h1 : (U.mulVec z + V.mulVec w) ⬝ᵥ (U.mulVec z + V.mulVec w)
      = (U.mulVec z) ⬝ᵥ (U.mulVec z)
        + 2 * ((U.mulVec z) ⬝ᵥ (V.mulVec w))
        + (V.mulVec w) ⬝ᵥ (V.mulVec w) := by
    rw [dotProduct_add, add_dotProduct, add_dotProduct]
    nlinarith [dotProduct_comm (U *ᵥ z) (V *ᵥ w)]
  rw [h1, orthoNorm U hU z, fiberCross U V hUV z w, orthoNorm V hV w]
  ring

/-- **An expert fiber is a deformation, not a model**: a rank-r
fiber against a d-dimensional body costs r·d matrix
coordinates against d·d for a full expert layer — linear in
the body dimension, not quadratic; with r < d the saving is
strict. (Arithmetic certificate of the min-volume principle:
grow the geometry by NEW LOW-RANK DIRECTIONS, not by full
copies.) -/
theorem fiberParamCount {d r : ℕ} (hr : r < d) :
    r * d < d * d := by
  have h0 : 0 < d := lt_of_le_of_lt (Nat.zero_le r) hr
  exact Nat.mul_lt_mul_of_lt_of_le hr (Nat.le_refl d) h0

end Hagi.Cortex
