/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.CortexFiber
/-!
# FiberSplit: the cortex ⊕ new-direction decomposition of a fiber

For an orthonormal cortex basis `U` and any fiber matrix `A`,
the projection identity
`A = U * (Uᵀ * A) + (A - U * (Uᵀ * A))` splits the fiber into a
cortex-embedded part and a residual:

* `fiberSplitOrtho` — the residual is orthogonal to the cortex:
  `Uᵀ * (A - U * (Uᵀ * A)) = 0`.
* `fiberActionNoInterference` — the two parts of the action
  never interfere: `(U *ᵥ z) ⬝ᵥ ((A - U * (Uᵀ * A)) *ᵥ x) = 0`.
* `fiberSplitEnergy` — the energies add exactly, with no cross
  term.
-/

namespace Hagi.Architecture

open Finset Matrix

/-- The residual of the cortex projection is orthogonal to
the cortex: `Uᵀ * (A - U * (Uᵀ * A)) = 0`. -/
theorem fiberSplitOrtho {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (hU : IsOrthoCol U) (A : Matrix (Fin d) (Fin r) ℝ) :
    Uᵀ * (A - U * (Uᵀ * A)) = 0 := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU,
    Matrix.one_mul, sub_self]

/-- The cortex part and the residual part of the action have
zero cross inner product. -/
theorem fiberActionNoInterference {d c r : ℕ}
    (U : Matrix (Fin d) (Fin c) ℝ) (hU : IsOrthoCol U)
    (A : Matrix (Fin d) (Fin r) ℝ)
    (z : Fin c → ℝ) (x : Fin r → ℝ) :
    (U *ᵥ z) ⬝ᵥ ((A - U * (Uᵀ * A)) *ᵥ x) = 0 := by
  refine fiberCross U (A - U * (Uᵀ * A)) ?_ z x
  exact fiberSplitOrtho U hU A

/-- The action energy decomposes without a cross term:
`(A *ᵥ x) ⬝ᵥ (A *ᵥ x) = ((Uᵀ * A) *ᵥ x) ⬝ᵥ ((Uᵀ * A) *ᵥ x) +
((A - U * (Uᵀ * A)) *ᵥ x) ⬝ᵥ ((A - U * (Uᵀ * A)) *ᵥ x)`. -/
theorem fiberSplitEnergy {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (hU : IsOrthoCol U) (A : Matrix (Fin d) (Fin r) ℝ)
    (x : Fin r → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x)
      = ((Uᵀ * A) *ᵥ x) ⬝ᵥ ((Uᵀ * A) *ᵥ x)
        + ((A - U * (Uᵀ * A)) *ᵥ x) ⬝ᵥ ((A - U * (Uᵀ * A)) *ᵥ x) := by
  have hA : A *ᵥ x = (U * (Uᵀ * A)) *ᵥ x
      + (A - U * (Uᵀ * A)) *ᵥ x := by
    rw [← Matrix.add_mulVec, add_sub_cancel]
  have hsplit : (A *ᵥ x) ⬝ᵥ (A *ᵥ x)
      = ((U * (Uᵀ * A)) *ᵥ x) ⬝ᵥ ((U * (Uᵀ * A)) *ᵥ x)
        + 2 * ((U * (Uᵀ * A)) *ᵥ x ⬝ᵥ ((A - U * (Uᵀ * A)) *ᵥ x))
        + ((A - U * (Uᵀ * A)) *ᵥ x) ⬝ᵥ ((A - U * (Uᵀ * A)) *ᵥ x) := by
    rw [hA, dotProduct_add, add_dotProduct, add_dotProduct]
    linarith [dotProduct_comm ((A - U * (Uᵀ * A)) *ᵥ x)
      ((U * (Uᵀ * A)) *ᵥ x)]
  have hcross : (U * (Uᵀ * A)) *ᵥ x
      ⬝ᵥ ((A - U * (Uᵀ * A)) *ᵥ x) = 0 := by
    rw [← Matrix.mulVec_mulVec]
    exact fiberActionNoInterference U hU A ((Uᵀ * A) *ᵥ x) x
  have hUenergy : ((U * (Uᵀ * A)) *ᵥ x) ⬝ᵥ ((U * (Uᵀ * A)) *ᵥ x)
      = ((Uᵀ * A) *ᵥ x) ⬝ᵥ ((Uᵀ * A) *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec]
    exact orthoNorm U hU (((Uᵀ * A)) *ᵥ x)
  rw [hsplit, hcross, hUenergy]
  ring

end Hagi.Architecture

open Matrix
open Finset

/-!
# OrthoInjection — geometric capability injection

A new skill residual is injected only into the subspace
orthogonal to the retained cortex state:
`h' = h + (A - U * (Uᵀ * A)) *ᵥ x`.

* `fiber_cortex_zero` — the injected fiber has zero cortex
  coordinates.
* `fiber_injection_preserves_cortex` — the cortex coordinates
  of the state are unchanged by the injection, for any
  payload `x`.
* `fiber_injection_norm_split` — the injected energy adds
  orthogonally to the cortex component.
-/

namespace Hagi.Architecture

/-- The injected fiber has zero cortex coordinates: the whole
payload lands in the orthogonal subspace. -/
theorem fiber_cortex_zero {d c r : ℕ}
    (U : Matrix (Fin d) (Fin c) ℝ) (hU : IsOrthoCol U)
    (A : Matrix (Fin d) (Fin r) ℝ) :
    Uᵀ * (A - U * (Uᵀ * A)) = 0 := by
  have h1 : Uᵀ * (A - U * (Uᵀ * A))
      = Uᵀ * A - (Uᵀ * U) * (Uᵀ * A) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc]
  have h2 : Uᵀ * U = 1 := hU
  rw [h1, h2, Matrix.one_mul, sub_self]

/-- The cortex coordinates of the state are unchanged by the
injection, for any payload `x`. -/
theorem fiber_injection_preserves_cortex {d c r : ℕ}
    (U : Matrix (Fin d) (Fin c) ℝ) (hU : IsOrthoCol U)
    (A : Matrix (Fin d) (Fin r) ℝ)
    (h : Fin d → ℝ) (x : Fin r → ℝ) :
    Uᵀ *ᵥ (h + (A - U * (Uᵀ * A)) *ᵥ x)
      = Uᵀ *ᵥ h := by
  have h1 : Uᵀ *ᵥ ((A - U * (Uᵀ * A)) *ᵥ x) = 0 := by
    have hz : Uᵀ * (A - U * (Uᵀ * A)) = 0 :=
      fiber_cortex_zero U hU A
    rw [Matrix.mulVec_mulVec, hz, Matrix.zero_mulVec]
  rw [Matrix.mulVec_add, h1, add_zero]

/-- The injected energy adds orthogonally to the cortex
component of the state: the total splits without a cross
term. -/
theorem fiber_injection_norm_split {d c r : ℕ}
    (U : Matrix (Fin d) (Fin c) ℝ) (hU : IsOrthoCol U)
    (A : Matrix (Fin d) (Fin r) ℝ)
    (z : Fin c → ℝ) (x : Fin r → ℝ) :
    (U.mulVec z + (A - U * (Uᵀ * A)) *ᵥ x) ⬝ᵥ
      (U.mulVec z + (A - U * (Uᵀ * A)) *ᵥ x)
    = (U.mulVec z) ⬝ᵥ (U.mulVec z)
      + ((A - U * (Uᵀ * A)) *ᵥ x) ⬝ᵥ
        ((A - U * (Uᵀ * A)) *ᵥ x) := by
  have hint : (U.mulVec z) ⬝ᵥ ((A - U * (Uᵀ * A)) *ᵥ x) = 0 :=
    fiberActionNoInterference U hU A z x
  have hint2 : ((A - U * (Uᵀ * A)) *ᵥ x) ⬝ᵥ (U *ᵥ z) = 0 := by
    rw [dotProduct_comm]; exact hint
  simp only [dotProduct_add, add_dotProduct, hint, hint2]
  ring

end Hagi.Architecture
