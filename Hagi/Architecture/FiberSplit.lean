/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.CortexFiber

set_option linter.style.header false

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

namespace Hagi.Cortex

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

end Hagi.Cortex
