/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.FiberSplit

open Matrix
open Finset

/-!
# OrthoInjection — geometric capability injection

The user-facing principle (the HAGI reading of orthogonal
input injection): a NEW information channel must not compete
geometrically with the carried-over state. Applied to
capability fibers: a new skill residual is injected only into
the subspace orthogonal to the retained cortex state:

  h' = h + P_⊥ (A x),   P_⊥ = I − U Uᵀ.

Main results:

* `fiber_cortex_zero`: the injected fiber has ZERO cortex
  coordinates (matrix form of `fiberSplitOrtho`);
* `fiber_injection_preserves_cortex`: the cortex coordinates
  of the state are UNCHANGED by the injection — the retained
  representation is untouched, whatever the skill payload x;
* `fiber_injection_norm_split`: the injected energy adds
  orthogonally (no cancellation against the carried state).
-/

namespace Hagi.Cortex

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

/-- **Capability injection preserves the cortex state**: the
cortex coordinates of the state are exactly what they were
before the injection — for ANY skill payload x. -/
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

/-- **Orthogonal energy split**: the injected skill energy
adds without interfering with the cortex component of the
carried state (no cancellation: growth is never paid for by
destroying carried structure). -/
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

end Hagi.Cortex
