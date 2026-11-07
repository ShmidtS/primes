/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.GatedCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.GatedCESafeStep
import Hagi.Model.CEHeldout
import Hagi.Model.GatedCEPositiveCurvature
import Hagi.Model.GatedCEUniformCurvature

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.GatedCETrajectory

open Hagi.State Hagi.Model
open Hagi.Model.GatedCEGradient Hagi.Model.GatedCEDescent
open Hagi.Model.GatedCESafeStep
open Hagi.Contracts.CEStep Hagi.Contracts.GatedCEStep
open Filter Topology

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- Repeated canonical gated training on one fixed target.  Every successor
uses the original `gatedCETrainStep`, with its direction and safe step computed
from the current recursive state rather than from an earlier iterate. -/
noncomputable def fixedGatedState (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : ℕ → TrainState n a r c k
  | 0 => S
  | s + 1 => gatedCETrainStep X t (fixedGatedState X t S opCost opRisk write s)
      opCost opRisk write

@[simp] theorem fixedGatedState_zero
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    fixedGatedState X t S opCost opRisk write 0 = S := rfl

@[simp] theorem fixedGatedState_succ
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) :
    fixedGatedState X t S opCost opRisk write (s + 1) =
      gatedCETrainStep X t (fixedGatedState X t S opCost opRisk write s)
        opCost opRisk write := rfl

/-- The actual one-target gated CE along the canonical recursive trajectory. -/
noncomputable def fixedGatedObjective (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) : ℝ :=
  gatedCEObjective X t (fixedGatedState X t S opCost opRisk write s)

@[simp] theorem fixedGatedObjective_zero
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    fixedGatedObjective X t S opCost opRisk write 0 = gatedCEObjective X t S := rfl

/-- At each successor, the canonical step uses the current parameters for both
its residual direction and its safe step size. -/
theorem coreParameters_fixedGatedState_succ
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) :
    coreParameters (fixedGatedState X t S opCost opRisk write (s + 1)) =
      gatedNextParameters X
        (coreParameters (fixedGatedState X t S opCost opRisk write s)) t
        (gatedSafeStepSize X
          (coreParameters (fixedGatedState X t S opCost opRisk write s)) t) :=
  coreParameters_gatedCETrainStep X t
    (fixedGatedState X t S opCost opRisk write s) opCost opRisk write

/-- The computed nonnegative majorizer drop at the current parameters lower-
bounds the exact actual CE decrease of the canonical successor. -/
theorem gatedSafeDrop_le_fixedGatedObjective_actualDrop [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) :
    gatedSafeDrop X
        (coreParameters (fixedGatedState X t S opCost opRisk write s)) t ≤
      fixedGatedObjective X t S opCost opRisk write s -
        fixedGatedObjective X t S opCost opRisk write (s + 1) := by
  exact gatedSafeDrop_le_gatedCETrainStep_drop X t
    (fixedGatedState X t S opCost opRisk write s) opCost opRisk write

/-- One canonical successor is bounded by the old actual loss minus the
current majorizer drop.  The two distinct drops are not added together. -/
theorem fixedGatedObjective_succ_le_actual_sub_drop [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) :
    fixedGatedObjective X t S opCost opRisk write (s + 1) ≤
      fixedGatedObjective X t S opCost opRisk write s -
        gatedSafeDrop X
          (coreParameters (fixedGatedState X t S opCost opRisk write s)) t := by
  have h := gatedSafeDrop_le_fixedGatedObjective_actualDrop X t S
    opCost opRisk write s
  linarith

/-- Canonical fixed-target updates never increase the actual gated CE. -/
theorem fixedGatedObjective_succ_le [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) :
    fixedGatedObjective X t S opCost opRisk write (s + 1) ≤
      fixedGatedObjective X t S opCost opRisk write s := by
  have h := fixedGatedObjective_succ_le_actual_sub_drop X t S
    opCost opRisk write s
  have hnonneg := gatedSafeDrop_nonneg X
    (coreParameters (fixedGatedState X t S opCost opRisk write s)) t
  linarith

/-- Exact old-minus-new actual objective differences telescope. -/
theorem fixedGatedObjective_actual_telescope
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ s ∈ Finset.range T,
        (fixedGatedObjective X t S opCost opRisk write s -
          fixedGatedObjective X t S opCost opRisk write (s + 1)) =
      gatedCEObjective X t S - fixedGatedObjective X t S opCost opRisk write T := by
  simpa using Finset.sum_range_sub' (fixedGatedObjective X t S opCost opRisk write) T

/-- The total actual loss decrease dominates the total computed majorizer
drops, each evaluated at that step's actual current parameters. -/
theorem fixedGatedObjective_sum_gatedSafeDrop_le_telescope [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ s ∈ Finset.range T, gatedSafeDrop X
        (coreParameters (fixedGatedState X t S opCost opRisk write s)) t ≤
      gatedCEObjective X t S - fixedGatedObjective X t S opCost opRisk write T := by
  exact ObjectiveTrajectory.sum_drop_le_initial_sub
    (fixedGatedObjective X t S opCost opRisk write)
    (fun s => gatedSafeDrop X
      (coreParameters (fixedGatedState X t S opCost opRisk write s)) t) T
    (gatedSafeDrop_le_fixedGatedObjective_actualDrop X t S opCost opRisk write)

/-- Antitonicity follows from actual per-successor loss nonincrease. -/
theorem fixedGatedObjective_antitone [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Antitone (fixedGatedObjective X t S opCost opRisk write) :=
  antitone_nat_of_succ_le (fixedGatedObjective_succ_le X t S opCost opRisk write)

/-- Every actual gated one-target CE value along the trajectory is nonnegative. -/
theorem fixedGatedObjective_nonneg [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) :
    0 ≤ fixedGatedObjective X t S opCost opRisk write s :=
  CEHeldout.ceOneHot_nonneg t
    (gatedForward X (coreParameters (fixedGatedState X t S opCost opRisk write s)))

/-- The actual fixed-target gated CE converges to a real lower bound. -/
theorem fixedGatedObjective_tendsto_ciInf [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fixedGatedObjective X t S opCost opRisk write) atTop
      (𝓝 (⨅ s, fixedGatedObjective X t S opCost opRisk write s)) := by
  exact ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg
    (fixedGatedObjective X t S opCost opRisk write)
    (fixedGatedObjective_antitone X t S opCost opRisk write)
    (fixedGatedObjective_nonneg X t S opCost opRisk write)

/-- The real loss infimum is nonnegative, without being declared optimal. -/
theorem fixedGatedObjective_ciInf_nonneg [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    0 ≤ ⨅ s, fixedGatedObjective X t S opCost opRisk write s :=
  ObjectiveTrajectory.ciInf_nonneg _
    (fixedGatedObjective_nonneg X t S opCost opRisk write)

end Hagi.Contracts.GatedCETrajectory

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.GatedCESummability

open Hagi.State Hagi.Model
open Hagi.Model.GatedCEGradient Hagi.Model.GatedCEDescent
open Hagi.Model.GatedCESafeStep
open Hagi.Contracts.CEStep Hagi.Contracts.GatedCEStep
open Hagi.Contracts.GatedCETrajectory
open Filter Topology

section ZeroAlignment

variable {V : Type} [Fintype V]
variable {n : ℕ}

/-- Zero squared residual-transpose alignment makes the direction zero. -/
theorem gatedDirection_eq_zero_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) : gatedDirection X θ t = 0 := by
  have hR : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      gatedResidualTranspose X θ t j = 0 := by
    apply (Finset.sum_sq_eq_zero_iff Finset.univ
      (gatedResidualTranspose X θ t)).mp
    simpa only [gatedAlignment] using hA
  apply PiLp.ext
  intro j
  simp [gatedDirection_ofLp, hR j (Finset.mem_univ j)]

/-- Zero alignment makes both second-order terms vanish with the direction. -/
theorem gatedCurvature_eq_zero_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) : gatedCurvature X θ t = 0 := by
  have hD := gatedDirection_eq_zero_of_alignment_eq_zero X θ t hA
  simp [gatedCurvature, gatedResidualSecondOrderMass, gatedStepRange,
    gatedUnitAbsLogit, gatedUnitSecondOrderMass, hD]

/-- The certified majorizer drop is exactly zero at zero alignment. -/
theorem gatedSafeDrop_eq_zero_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) : gatedSafeDrop X θ t = 0 := by
  have hC := gatedCurvature_eq_zero_of_alignment_eq_zero X θ t hA
  simp [gatedSafeDrop, hC, hA]

/-- Even with the unit curvature fallback, zero alignment gives no update. -/
theorem gatedNextParameters_eq_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) :
    gatedNextParameters X θ t (gatedSafeStepSize X θ t) = θ := by
  rw [gatedNextParameters, gatedDirection_eq_zero_of_alignment_eq_zero X θ t hA]
  simp

/-- The actual CE after the computed safe step is exactly the old CE. -/
theorem gated_ceOneHot_safeStep_eq_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (θ : EuclideanSpace ℝ (Fin n)) (t : V)
    (hA : gatedAlignment X θ t = 0) :
    Hagi.ceOneHot t (gatedForward X
      (gatedNextParameters X θ t (gatedSafeStepSize X θ t))) =
        Hagi.ceOneHot t (gatedForward X θ) := by
  rw [gatedNextParameters_eq_of_alignment_eq_zero X θ t hA]

end ZeroAlignment

section ExecutedZeroAlignment

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- The canonical executed transition preserves gated CE at zero alignment. -/
theorem gatedCEObjective_gatedCETrainStep_eq_of_alignment_eq_zero
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hA : gatedAlignment X (coreParameters S) t = 0) :
    gatedCEObjective X t (gatedCETrainStep X t S opCost opRisk write) =
      gatedCEObjective X t S := by
  rw [gatedCEObjective, gatedCEObjective, coreParameters_gatedCETrainStep]
  exact gated_ceOneHot_safeStep_eq_of_alignment_eq_zero X (coreParameters S) t hA

end ExecutedZeroAlignment

section InfiniteAccounting

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- The current majorizer-drop sequence `fixedGatedDrop`, evaluated using the
actual parameters of `fixedGatedState s`, never at stale or successor parameters. -/
noncomputable def fixedGatedDrop (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) : ℝ :=
  gatedSafeDrop X
    (coreParameters (fixedGatedState X t S opCost opRisk write s)) t

/-- Every current safe-step majorizer drop is nonnegative. -/
theorem fixedGatedDrop_nonneg (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (s : ℕ) :
    0 ≤ fixedGatedDrop X t S opCost opRisk write s :=
  gatedSafeDrop_nonneg X
    (coreParameters (fixedGatedState X t S opCost opRisk write s)) t

/-- Actual telescoping and final CE nonnegativity bound every partial sum of
current drops by the initial gated CE. -/
theorem fixedGatedDrop_sum_le_initial [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ s ∈ Finset.range T, fixedGatedDrop X t S opCost opRisk write s ≤
      gatedCEObjective X t S := by
  calc
    ∑ s ∈ Finset.range T, fixedGatedDrop X t S opCost opRisk write s ≤
        gatedCEObjective X t S -
          fixedGatedObjective X t S opCost opRisk write T :=
      fixedGatedObjective_sum_gatedSafeDrop_le_telescope
        X t S opCost opRisk write T
    _ ≤ gatedCEObjective X t S :=
      sub_le_self _ (fixedGatedObjective_nonneg X t S opCost opRisk write T)

/-- The sequence of actual current majorizer drops is summable. -/
theorem fixedGatedDrop_summable [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Summable (fixedGatedDrop X t S opCost opRisk write) := by
  exact summable_of_sum_range_le
    (fixedGatedDrop_nonneg X t S opCost opRisk write)
    (fixedGatedDrop_sum_le_initial X t S opCost opRisk write)

/-- Infinite-time summability forces the current majorizer drops to zero. -/
theorem fixedGatedDrop_tendsto_zero [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fixedGatedDrop X t S opCost opRisk write) atTop (𝓝 0) :=
  (fixedGatedDrop_summable X t S opCost opRisk write).tendsto_atTop_zero

/-- The total sum of actual current majorizer drops is at most initial CE. -/
theorem fixedGatedDrop_tsum_le_initial [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    ∑' s, fixedGatedDrop X t S opCost opRisk write s ≤
      gatedCEObjective X t S :=
  (fixedGatedDrop_summable X t S opCost opRisk write).tsum_le_of_sum_range_le
    (fixedGatedDrop_sum_le_initial X t S opCost opRisk write)

end InfiniteAccounting

end Hagi.Contracts.GatedCESummability

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
