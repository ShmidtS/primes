/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hagi.Semantics.StateUnification
import Hagi.System.DerivedState
set_option linter.style.header false

/-!
# DerivedStateCoherence — the coherence tie for DerivedState (A18.6)

The genuine `Hagi.Semantics.coherentGrowth` statement about the
derived growth state of `Hagi.System.DerivedState`. The abstract
`GrowthState` has no weights/params invariant (audit W1 / break
theorem `growth_coherent_advance_iff`); the DERIVED state carries the
invariant BY CONSTRUCTION: `weights := θ`, `params := θ`, so with the
coordinate projection `f p := (p : Fin d → ℝ)` coherence is an invariant
of the construction, not a repair-theorem patch.

Layering: this bridge lives in `Hagi/Semantics/` (layer 5) because the
 symbol `coherentGrowth` is defined there; the System-layer module
(layer 3, LayerLint) cannot import it. Same commit as
`Hagi/System/DerivedState.lean`.
-/

open InnerProductSpace

namespace Hagi.Semantics

open Hagi.System Hagi.System.DerivedState

variable {d : ℕ} {I : Type} [Fintype I]

/-- The canonical projection for derived states: the coordinate view of
the parameter vector. -/
noncomputable def derivedProj {d : ℕ} :
    (EuclideanSpace ℝ (Fin d)) → (Fin d → ℝ) :=
  fun p => (p : Fin d → ℝ)

/-- **The invariant, BY CONSTRUCTION**: the derived growth state is
coherent for the canonical coordinate projection — `f params = weights`
holds because both are the same weight vector `θ`. No repair theorem
needed; contrast `growth_coherent_advance_iff` (the abstract break). -/
theorem derived_coherent (ds : FixedDataset I d) (η : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    coherentGrowth (derivedGrowthState ds η θ) derivedProj := by
  simp [coherentGrowth, derivedProj, derivedGrowthState]

/-- The computed channel survives the transition: after the joint step
the derived state's energy field is the loss at the stepped weights
`θ − η • ∇` (nothing measured, nothing stale). -/
theorem derived_joint_energy_channel (ds : FixedDataset I d) (η : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    (Hagi.System.joint (derivedGrowthState ds η θ)).energy
      = energyOf ds (θ - η • gradOf ds θ) := by
  simp [Hagi.System.joint, derivedGrowthState, derivedEffects]

/-- The repair degenerates to a no-op on derived states: since the
invariant already holds, `repairGrowth` fixes the state (`growth_repair_
fixes_coherent` instantiated — construction beats patching). -/
theorem derived_repair_fixes (ds : FixedDataset I d) (η : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    repairGrowth (derivedGrowthState ds η θ) derivedProj
      = derivedGrowthState ds η θ :=
  growth_repair_fixes_coherent (derivedGrowthState ds η θ) derivedProj
    (derived_coherent ds η θ)

end Hagi.Semantics
