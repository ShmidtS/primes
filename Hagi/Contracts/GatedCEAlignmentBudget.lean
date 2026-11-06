/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.GatedCESummability
import Hagi.Model.GatedCEPositiveCurvature

set_option linter.style.header false

/-!
# Infinite accounting of squared gated alignment

A uniform upper bound on the actual current curvature converts the exact
safe-step majorizer drop into a budget for squared residual-transpose
alignment.  The finite-sum argument follows `BatchCEAlignmentBudget`, while
summability and convergence use the same `summable_of_sum_range_le` pattern as
`GatedCESummability`.

Every alignment, curvature, and drop is evaluated at the current parameters
of the canonical recursive state.  These results do not assert summability of
the alignment itself, residual or parameter convergence, a global optimum, or
any model-quality claim.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.GatedCEAlignmentBudget

open Hagi.State Hagi.Model
open Hagi.Model.GatedCEGradient Hagi.Model.GatedCEDescent
open Hagi.Model.GatedCESafeStep Hagi.Model.GatedCEPositiveCurvature
open Hagi.Contracts.CEStep Hagi.Contracts.GatedCEStep
open Hagi.Contracts.GatedCETrajectory Hagi.Contracts.GatedCESummability
open Filter Topology

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- Squared residual-transpose alignment at the actual current parameters of
the canonical fixed-target gated trajectory. -/
noncomputable def fixedGatedAlignment (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) : ℝ :=
  gatedAlignment X
    (coreParameters (fixedGatedState X t S opCost opRisk write s)) t

/-- A uniform curvature bound controls each squared current alignment by the
corresponding exact safe-step majorizer drop. -/
theorem fixedGatedAlignment_sq_le_four_mul
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (K : ℝ) (hK : 0 < K)
    (hcurvature : ∀ s : ℕ, gatedCurvature X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t ≤ K)
    (s : ℕ) :
    (fixedGatedAlignment X t S opCost opRisk write s) ^ 2 ≤
      4 * K * fixedGatedDrop X t S opCost opRisk write s := by
  by_cases hA : fixedGatedAlignment X t S opCost opRisk write s = 0
  · have hA0 : gatedAlignment X
        (coreParameters (fixedGatedState X t S opCost opRisk write s)) t = 0 := hA
    have hdrop : fixedGatedDrop X t S opCost opRisk write s = 0 := by
      unfold fixedGatedDrop
      exact gatedSafeDrop_eq_zero_of_alignment_eq_zero X
        (coreParameters (fixedGatedState X t S opCost opRisk write s)) t hA0
    rw [hA, hdrop]
    norm_num
  · have hAnonneg : 0 ≤ fixedGatedAlignment X t S opCost opRisk write s :=
      gatedAlignment_nonneg X
        (coreParameters (fixedGatedState X t S opCost opRisk write s)) t
    have hApos : 0 < fixedGatedAlignment X t S opCost opRisk write s :=
      lt_of_le_of_ne hAnonneg (Ne.symm hA)
    have hCpos : 0 < gatedCurvature X
        (coreParameters (fixedGatedState X t S opCost opRisk write s)) t :=
      gatedCurvature_pos_of_alignment_pos X
        (coreParameters (fixedGatedState X t S opCost opRisk write s)) t hApos
    have hD : 0 ≤ fixedGatedDrop X t S opCost opRisk write s :=
      fixedGatedDrop_nonneg X t S opCost opRisk write s
    have hid : (fixedGatedAlignment X t S opCost opRisk write s) ^ 2 =
        4 * gatedCurvature X
          (coreParameters (fixedGatedState X t S opCost opRisk write s)) t *
          fixedGatedDrop X t S opCost opRisk write s := by
      unfold fixedGatedAlignment fixedGatedDrop
      simp only [gatedSafeDrop, ne_of_gt hCpos, ↓reduceIte]
      field_simp
    have hCD : gatedCurvature X
          (coreParameters (fixedGatedState X t S opCost opRisk write s)) t *
          fixedGatedDrop X t S opCost opRisk write s ≤
        K * fixedGatedDrop X t S opCost opRisk write s :=
      mul_le_mul (hcurvature s) le_rfl hD hK.le
    calc
      (fixedGatedAlignment X t S opCost opRisk write s) ^ 2 =
          4 * gatedCurvature X
            (coreParameters (fixedGatedState X t S opCost opRisk write s)) t *
            fixedGatedDrop X t S opCost opRisk write s := hid
      _ = 4 * (gatedCurvature X
            (coreParameters (fixedGatedState X t S opCost opRisk write s)) t *
            fixedGatedDrop X t S opCost opRisk write s) := by ring
      _ ≤ 4 * (K * fixedGatedDrop X t S opCost opRisk write s) :=
        mul_le_mul_of_nonneg_left hCD (by norm_num)
      _ = 4 * K * fixedGatedDrop X t S opCost opRisk write s := by ring

/-- Initial gated CE bounds every finite sum of squared current alignments. -/
theorem fixedGatedAlignment_sum_sq_le_initial [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (K : ℝ) (hK : 0 < K)
    (hcurvature : ∀ s : ℕ, gatedCurvature X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t ≤ K)
    (T : ℕ) :
    ∑ s ∈ Finset.range T, (fixedGatedAlignment X t S opCost opRisk write s) ^ 2 ≤
      4 * K * gatedCEObjective X t S := by
  calc
    ∑ s ∈ Finset.range T, (fixedGatedAlignment X t S opCost opRisk write s) ^ 2 ≤
        ∑ s ∈ Finset.range T, 4 * K * fixedGatedDrop X t S opCost opRisk write s :=
      Finset.sum_le_sum fun s _hs =>
        fixedGatedAlignment_sq_le_four_mul X t S opCost opRisk write
          K hK hcurvature s
    _ = 4 * K * ∑ s ∈ Finset.range T,
        fixedGatedDrop X t S opCost opRisk write s := by
      rw [Finset.mul_sum]
    _ ≤ 4 * K * gatedCEObjective X t S :=
      mul_le_mul_of_nonneg_left
        (fixedGatedDrop_sum_le_initial X t S opCost opRisk write T)
        (mul_nonneg (by norm_num) hK.le)

/-- Squared current alignment is summable under the uniform curvature bound. -/
theorem fixedGatedAlignment_sq_summable [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (K : ℝ) (hK : 0 < K)
    (hcurvature : ∀ s : ℕ, gatedCurvature X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t ≤ K) :
    Summable (fun s => (fixedGatedAlignment X t S opCost opRisk write s) ^ 2) := by
  exact summable_of_sum_range_le
    (fun s => sq_nonneg (fixedGatedAlignment X t S opCost opRisk write s))
    (fixedGatedAlignment_sum_sq_le_initial X t S opCost opRisk write
      K hK hcurvature)

/-- Infinite-time summability forces squared current alignment to zero. -/
theorem fixedGatedAlignment_sq_tendsto_zero [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (K : ℝ) (hK : 0 < K)
    (hcurvature : ∀ s : ℕ, gatedCurvature X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t ≤ K) :
    Tendsto (fun s => (fixedGatedAlignment X t S opCost opRisk write s) ^ 2)
      atTop (𝓝 0) :=
  (fixedGatedAlignment_sq_summable X t S opCost opRisk write
    K hK hcurvature).tendsto_atTop_zero

/-- Squared residual-transpose alignment at current parameters is nonnegative. -/
theorem fixedGatedAlignment_nonneg
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) :
    0 ≤ fixedGatedAlignment X t S opCost opRisk write s := by
  exact gatedAlignment_nonneg X
    (coreParameters (fixedGatedState X t S opCost opRisk write s)) t

/-- Infinite-time summability of the squares forces current alignment to zero. -/
theorem fixedGatedAlignment_tendsto_zero [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (K : ℝ) (hK : 0 < K)
    (hcurvature : ∀ s : ℕ, gatedCurvature X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t ≤ K) :
    Tendsto (fixedGatedAlignment X t S opCost opRisk write) atTop (𝓝 0) := by
  have hsqrt := (fixedGatedAlignment_sq_tendsto_zero X t S opCost opRisk write
    K hK hcurvature).sqrt
  simpa only [Real.sqrt_zero] using hsqrt.congr (fun s =>
    Real.sqrt_sq (fixedGatedAlignment_nonneg X t S opCost opRisk write s))

/-- One squared residual-transpose coordinate is bounded by current alignment. -/
theorem fixedGatedResidualTranspose_sq_le_alignment
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (s : ℕ) (j : Fin n) :
    (gatedResidualTranspose X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t j) ^ 2 ≤
      fixedGatedAlignment X t S opCost opRisk write s := by
  unfold fixedGatedAlignment gatedAlignment
  exact Finset.single_le_sum (fun i _hi => sq_nonneg
    (gatedResidualTranspose X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t i))
    (Finset.mem_univ j)

/-- Each current residual-transpose coordinate tends to zero. -/
theorem fixedGatedResidualTranspose_tendsto_zero [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (K : ℝ) (hK : 0 < K)
    (hcurvature : ∀ s : ℕ, gatedCurvature X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t ≤ K)
    (j : Fin n) :
    Tendsto (fun s => gatedResidualTranspose X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t j)
      atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun s => Real.sqrt
      (fixedGatedAlignment X t S opCost opRisk write s)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (fixedGatedAlignment_tendsto_zero X t S opCost opRisk write
        K hK hcurvature).sqrt
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  change Tendsto (fun s => |gatedResidualTranspose X
    (coreParameters (fixedGatedState X t S opCost opRisk write s)) t j|)
    atTop (𝓝 0)
  exact squeeze_zero (fun s => abs_nonneg _)
    (fun s => Real.abs_le_sqrt
      (fixedGatedResidualTranspose_sq_le_alignment
        X t S opCost opRisk write s j))
    hsqrt

end Hagi.Contracts.GatedCEAlignmentBudget
