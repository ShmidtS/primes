import Hagi.Contracts.GatedCEStepCertificate
import Hagi.Model.GatedCESafeStep
import Hagi.Model.CEHeldout

/-!
# Fixed-target nonlinear gated CE trajectory

A fixed categorical target is re-evaluated after every actual canonical
`gatedCETrainStep`.  The proof structure follows the established
`Hagi.Contracts.BatchCETrajectory` development.  The residual-transpose
direction and nonlinear safe step are therefore recomputed from each
successor's own weights.  The supplied cost, risk, and optional write remain
fixed logical transition inputs.

The actual loss differences telescope and dominate the sum of nonnegative
safe-step majorizer drops.  Nonnegative CE and antitonicity imply convergence
of the loss values to their real infimum.  The infimum is not asserted to be
zero, and neither parameters nor residuals are asserted to converge.

This is not a repeated feasible-certificate, generalization, external-quality,
optimal-rate, or physical-resource theorem.
-/

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
  rw [← fixedGatedObjective_actual_telescope X t S opCost opRisk write T]
  exact Finset.sum_le_sum fun s _hs =>
    gatedSafeDrop_le_fixedGatedObjective_actualDrop X t S opCost opRisk write s

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
  apply tendsto_atTop_ciInf (fixedGatedObjective_antitone X t S opCost opRisk write)
  refine ⟨0, ?_⟩
  rintro z ⟨s, rfl⟩
  exact fixedGatedObjective_nonneg X t S opCost opRisk write s

/-- The real loss infimum is nonnegative, without being declared optimal. -/
theorem fixedGatedObjective_ciInf_nonneg [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    0 ≤ ⨅ s, fixedGatedObjective X t S opCost opRisk write s :=
  le_ciInf (fixedGatedObjective_nonneg X t S opCost opRisk write)

end Hagi.Contracts.GatedCETrajectory
