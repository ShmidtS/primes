/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.AlignedMerge

/-!
# SharedStateComposition — energy and parameter cost of omni fusion

* `sharedStateEnergy`: for orthonormal leaves with `Uᵀ * V = 0`
  the composed-state energy is the exact sum of the leaf
  energies.
* `omniParamCost` / `sharedStateCostBound`: k rank-r leaves
  over a d-dim cortex cost `k·r·d` entries, below `d·d` when
  `k·r < d`.
* `sharedStatePerturbed`: the composed energy exceeds the
  Pythagorean sum by at most a term linear in the residual
  misalignment `frobSq (Vᵀ * W)`.
-/

namespace Hagi.Omni

open Matrix

/-! ### Exact composition at full alignment -/

/-- For orthonormal `U`, `V` with `Uᵀ * V = 0`:
`(U *ᵥ z + V *ᵥ w) ⬝ᵥ (U *ᵥ z + V *ᵥ w) = z ⬝ᵥ z + w ⬝ᵥ w`. -/
theorem sharedStateEnergy {d c r : ℕ} (U : Matrix (Fin d) (Fin c) ℝ)
    (V : Matrix (Fin d) (Fin r) ℝ)
    (hU : Hagi.Cortex.IsOrthoCol U) (hV : Hagi.Cortex.IsOrthoCol V)
    (hUV : Uᵀ * V = 0) (z : Fin c → ℝ) (w : Fin r → ℝ) :
    (U.mulVec z + V.mulVec w) ⬝ᵥ (U.mulVec z + V.mulVec w)
      = z ⬝ᵥ z + w ⬝ᵥ w :=
  Hagi.Cortex.fiberPythagoras U V hU hV hUV z w

/-! ### The parameter arithmetic of the omni state -/

/-- The entry count of a matrix. -/
def entryCount {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℕ := m * n

/-- **The leaf cost**: one rank-r modality leaf over a d-dim
cortex costs r·d entries. -/
theorem omniLeafCost {d r : ℕ} (V : Matrix (Fin d) (Fin r) ℝ) :
    entryCount V = r * d := by
  unfold entryCount
  exact Nat.mul_comm d r

/-- `∑ i : Fin k, r * d = k * (r * d)`. -/
theorem omniParamCost (k r d : ℕ) :
    ∑ i : Fin k, r * d = k * (r * d) := by
  rw [Finset.sum_const]
  simp

/-- If `0 < d` and `k * r < d` then the k-leaf parameter
count `k * (r * d)` is strictly below `d * d`. -/
theorem sharedStateCostBound (k r d : ℕ) (hd : 0 < d)
    (hkr : k * r < d) :
    ∑ i : Fin k, r * d < d * d := by
  rw [omniParamCost k r d]
  nlinarith [hkr, hd, Nat.succ_le_of_lt hd]

/-- For orthonormal `V`, `W`: the composed energy is at most
`r ⬝ᵥ r + s ⬝ᵥ s + 2 * √(frobSq (Vᵀ * W)) * ‖r‖ * ‖s‖`; at
`Vᵀ * W = 0` this is the equality of `sharedStateEnergy`. -/
theorem sharedStatePerturbed {d r1 r2 : ℕ}
    (V : Matrix (Fin d) (Fin r1) ℝ) (W : Matrix (Fin d) (Fin r2) ℝ)
    (hV : Hagi.Cortex.IsOrthoCol V) (hW : Hagi.Cortex.IsOrthoCol W)
    (r : Fin r1 → ℝ) (s : Fin r2 → ℝ) :
    (V *ᵥ r + W *ᵥ s) ⬝ᵥ (V *ᵥ r + W *ᵥ s)
      ≤ (r ⬝ᵥ r) + (s ⬝ᵥ s)
        + 2 * (Hagi.Cortex.frobSq (Vᵀ * W)).sqrt
            * (r ⬝ᵥ r).sqrt * (s ⬝ᵥ s).sqrt :=
  Hagi.Cortex.mergeEnergyPerturbed V W hV hW r s

end Hagi.Omni
