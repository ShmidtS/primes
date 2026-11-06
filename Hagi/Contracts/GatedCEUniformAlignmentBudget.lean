/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.GatedCEAlignmentBudget
import Hagi.Model.GatedCEUniformCurvature

set_option linter.style.header false

/-!
# Uniform-curvature accounting of squared gated alignment

The feature-only curvature bound specializes the conditional budget without
introducing trajectory hypotheses.  These corollaries cover squared alignment,
raw alignment, and residual-transpose coordinate convergence.  They make no
residual, parameter, global-optimum, or model-quality claims.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.GatedCEUniformAlignmentBudget

open Hagi.State Hagi.Model
open Hagi.Model.GatedCEGradient Hagi.Model.GatedCEDescent
open Hagi.Model.GatedCESafeStep Hagi.Model.GatedCEPositiveCurvature
open Hagi.Model.GatedCEUniformCurvature
open Hagi.Contracts.CEStep Hagi.Contracts.GatedCEStep
open Hagi.Contracts.GatedCETrajectory Hagi.Contracts.GatedCESummability
open Hagi.Contracts.GatedCEAlignmentBudget
open Filter Topology

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- Initial gated CE bounds every finite sum of squared current alignments. -/
theorem fixedGatedAlignment_sum_sq_le_uniform [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (T : ℕ) :
    ∑ s ∈ Finset.range T, (fixedGatedAlignment X t S opCost opRisk write s) ^ 2 ≤
      4 * gatedCurvatureUniformBound X * gatedCEObjective X t S := by
  exact fixedGatedAlignment_sum_sq_le_initial X t S opCost opRisk write
    (gatedCurvatureUniformBound X) (gatedCurvatureUniformBound_pos X)
    (fun s => gatedCurvature_le_uniformBound X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t) T

/-- Squared current alignment is summable under the feature-only bound. -/
theorem fixedGatedAlignment_sq_summable_uniform [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Summable (fun s => (fixedGatedAlignment X t S opCost opRisk write s) ^ 2) := by
  exact fixedGatedAlignment_sq_summable X t S opCost opRisk write
    (gatedCurvatureUniformBound X) (gatedCurvatureUniformBound_pos X)
    (fun s => gatedCurvature_le_uniformBound X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t)

/-- Infinite-time summability forces squared current alignment to zero. -/
theorem fixedGatedAlignment_sq_tendsto_zero_uniform [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fun s => (fixedGatedAlignment X t S opCost opRisk write s) ^ 2)
      atTop (𝓝 0) := by
  exact fixedGatedAlignment_sq_tendsto_zero X t S opCost opRisk write
    (gatedCurvatureUniformBound X) (gatedCurvatureUniformBound_pos X)
    (fun s => gatedCurvature_le_uniformBound X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t)

/-- Feature-only curvature forces current alignment to zero. -/
theorem fixedGatedAlignment_tendsto_zero_uniform [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fixedGatedAlignment X t S opCost opRisk write) atTop (𝓝 0) := by
  exact fixedGatedAlignment_tendsto_zero X t S opCost opRisk write
    (gatedCurvatureUniformBound X) (gatedCurvatureUniformBound_pos X)
    (fun s => gatedCurvature_le_uniformBound X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t)

/-- Feature-only curvature forces each residual-transpose coordinate to zero. -/
theorem fixedGatedResidualTranspose_tendsto_zero_uniform [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (j : Fin n) :
    Tendsto (fun s => gatedResidualTranspose X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t j)
      atTop (𝓝 0) := by
  exact fixedGatedResidualTranspose_tendsto_zero X t S opCost opRisk write
    (gatedCurvatureUniformBound X) (gatedCurvatureUniformBound_pos X)
    (fun s => gatedCurvature_le_uniformBound X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t) j

end Hagi.Contracts.GatedCEUniformAlignmentBudget
