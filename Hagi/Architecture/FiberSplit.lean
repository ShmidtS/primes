/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.CortexFiber

set_option linter.style.header false

/-!
# FiberSplit: every expert fiber decomposes into a cortex
part and a genuinely new direction (R183)

The geometric Grow law of the cortex⊕fiber architecture: for
any expert fiber matrix A and any shared cortex basis U
(orthonormal columns), the projection identity

  A = U · (Uᵀ A) + R,   where R = A − U·(UᵀA),

splits the fiber into a cortex-embedded part U·(UᵀA) and a
residual R whose cortex coordinates are EXACTLY zero:

* `fiberSplitOrtho`: Uᵀ R = 0 — the residual is orthogonal to
  the cortex by construction (the "expert either uses existing
  cortex directions or adds a genuinely new orthogonal
  subspace" law, as a theorem, no hypothesis beyond IsOrthoCol
  U).
* `fiberActionNoInterference`: the ACTION decomposition
  inherits the no-cross-talk law: ⟨U z, R x⟩ = 0 for all
  z, x — the cortex part and the new-direction part of the
  expert's action never interfere (R181 `fiberCross`
  instantiated at the split); by `fiberPythagoras` their
  energies add exactly.

Grow = adding R-directions; Merge = moving UᵀA-parts into the
cortex and aligning residuals — the algebraic skeleton of the
HAGI cycle.
-/

namespace Hagi.Cortex

open Finset Matrix

/-- **The cortex split**: the residual of the cortex
projection is orthogonal to the cortex exactly — Uᵀ(A −
U·(UᵀA)) = 0. Every expert fiber is a cortex part plus a
genuinely new direction; nothing leaks. -/
theorem fiberSplitOrtho {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (hU : IsOrthoCol U) (A : Matrix (Fin d) (Fin r) ℝ) :
    Uᵀ * (A - U * (Uᵀ * A)) = 0 := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU,
    Matrix.one_mul, sub_self]

/-- **No interference at the split**: the cortex part and the
new-direction part of the expert action have exactly zero
cross inner product — Grow adds directions that the cortex
never fights. -/
theorem fiberActionNoInterference {d c r : ℕ}
    (U : Matrix (Fin d) (Fin c) ℝ) (hU : IsOrthoCol U)
    (A : Matrix (Fin d) (Fin r) ℝ)
    (z : Fin c → ℝ) (x : Fin r → ℝ) :
    (U *ᵥ z) ⬝ᵥ ((A - U * (Uᵀ * A)) *ᵥ x) = 0 := by
  refine fiberCross U (A - U * (Uᵀ * A)) ?_ z x
  exact fiberSplitOrtho U hU A

/-- **The split energy law**: the expert's action energy
decomposes EXACTLY as
‖A x‖² = ‖(UᵀA) x‖² + ‖(A − U·(UᵀA)) x‖² — the cortex
coordinate part plus the new-direction part, no cross term
(the Grow bookkeeping: what the expert does inside the cortex
and what it adds outside are exactly separable; merging the
cortex part back is free by construction). -/
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
