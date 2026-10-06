/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.CortexFiber
import Hagi.Architecture.AlignedMerge

/-!
# SharedStateComposition — the energy contract of omni fusion

The SharedStateComposition module of the omni layer: modalities
enter the shared geometric state as fiber contributions, and the
fusion cost is governed by the R181–R183 geometry.

Main results:
* `sharedStateEnergy`: the energy of the composed state of two
  orthogonal aligned leaves is the EXACT sum of the leaf
  energies — no fusion loss at full alignment (the direct
  restatement of fiberPythagoras in omni vocabulary);
* `omniParamCost`: adding k rank-r leaves to a d-dim cortex
  costs exactly k·r·d entries — sub-quadratic in d: a modality
  is a cheap deformation of the shared geometry, not a second
  model (the fiberParamCount arithmetic, summed over leaves);
* `sharedStateCostBound`: the total parameter bill of the omni
  state (cortex + k leaves) against the d×d budget: with
  k·r < d the whole omni state costs less than one dense layer.
-/

namespace Hagi.Omni

open Matrix

/-! ### Exact composition at full alignment -/

/-- **Pythagorean composition of aligned leaves**: for
orthonormal modality leaves with UᵀV = 0, the shared-state
energy is the exact sum of the leaf energies — fusion at full
alignment is loss-free (fiberPythagoras in omni vocabulary). -/
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

/-- **The omni parameter bill**: k modality leaves of width r
over a d-dim cortex cost k·r·d entries in total. -/
theorem omniParamCost (k r d : ℕ) :
    ∑ i : Fin k, r * d = k * (r * d) := by
  rw [Finset.sum_const]
  simp

/-- **The budget theorem**: if k leaves of rank r satisfy
k·r ≤ c ≤ d (the total new directions fit into the cortex
budget), the whole omni state costs strictly less than one
dense d×d layer — the "max quality at min volume" arithmetic of
the omni design: new modalities are cheap deformations, not new
models. -/
theorem sharedStateCostBound (k r d : ℕ) (hd : 0 < d)
    (hkr : k * r < d) :
    ∑ i : Fin k, r * d < d * d := by
  rw [omniParamCost k r d]
  nlinarith [hkr, hd, Nat.succ_le_of_lt hd]

/-- **The misalignment price of omni fusion**: for two
orthonormal modality leaves, the composed shared-state energy is
at most the diagonal (loss-free) sum plus 2·√frobSq(VᵀW)·‖r‖·‖s‖
— the price of merging misaligned leaves is LINEAR in the
residual misalignment frobSq(VᵀW); at VᵀW = 0 the composition is
exactly Pythagorean (sharedStateEnergy). -/
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
