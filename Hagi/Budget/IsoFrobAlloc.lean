/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.IsoFrobCascade
import Hagi.Budget.WeightedExpAlloc

set_option linter.style.header false

open scoped BigOperators

/-!
# RankBudget adapter: cascade-weighted sensitivities (A8 F7)

With cascade-weighted sensitivities `c_j := isoFrobEnergy (J_{>j})
* hScale_j` (the A8 isotropic-Frobenius calibration; `hScale` is
the measured per-layer `‖h_j‖²` scale, a premise-level input),
the additive exponential-residual model of
`Hagi.Budget.RankBudget`/`WeightedExpAlloc` becomes the honest
deep-net specialization: `weightedExpAllocation_isoFrob_optimal`
transports the closed-form optimality to the cascade-weighted
cost coefficients. The `(c_j, κ_j)` exponential-tail hypothesis
of RankBudget remains an input assumption; only the SENSITIVITY
WEIGHTS are derived (from `Hagi.Architecture.IsoFrobCascade`).
-/

namespace Hagi.Budget

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

open Hagi.Architecture (isoFrobEnergy isoCascadeEnergy)

/-- The A8 F7 cascade-weighted sensitivity:
`c_j := isoFrobEnergy (J_tail j) * hScale j`. -/
noncomputable def isoFrobSensitivity (Jtail : ι → Matrix (Fin d) (Fin d) ℝ)
    (hScale : ι → ℝ) (j : ι) : ℝ :=
  isoFrobEnergy (Jtail j) * hScale j

theorem isoFrobSensitivity_pos (Jtail : ι → Matrix (Fin d) (Fin d) ℝ)
    (hScale : ι → ℝ) (hd : 0 < d)
    (hJ : ∀ j, 0 < Hagi.Core.frobSq (Jtail j))
    (hs : ∀ j, 0 < hScale j) (j : ι) :
    0 < isoFrobSensitivity Jtail hScale j := by
  unfold isoFrobSensitivity isoFrobEnergy
  exact mul_pos (div_pos (hJ j) (Nat.cast_pos.mpr hd)) (hs j)

/-- The adapter corollary: instantiating the RankBudget/
WeightedExpAlloc machinery at the cascade-weighted sensitivities
`c = isoFrobSensitivity` transports the closed-form optimality:
the additive model BECOMES the honest deep-net specialization. -/
theorem weightedExpAllocation_isoFrob_optimal
    (Jtail : ι → Matrix (Fin d) (Fin d) ℝ) (hScale : ι → ℝ)
    (κ w : ι → ℝ) (B : ℝ) (r : ι → ℝ)
    (hd : 0 < d) (hJ : ∀ j, 0 < Hagi.Core.frobSq (Jtail j))
    (hs : ∀ j, 0 < hScale j)
    (hκ : ∀ j, 0 < κ j) (hw : ∀ j, 0 < w j)
    (hbudget : ∑ j, w j * r j = B) :
    ∑ j, isoFrobSensitivity Jtail hScale j
        * Real.exp (-κ j * Hagi.Budget.weightedExpAllocation
            (isoFrobSensitivity Jtail hScale) κ w B j)
      ≤ ∑ j, isoFrobSensitivity Jtail hScale j
          * Real.exp (-κ j * r j) := by
  exact Hagi.Budget.weightedExpAllocation_optimal
    (isoFrobSensitivity Jtail hScale) κ w B r
    (fun j => isoFrobSensitivity_pos Jtail hScale hd hJ hs j)
    hκ hw hbudget


end Hagi.Budget
