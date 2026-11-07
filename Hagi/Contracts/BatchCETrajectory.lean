import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Unified.GuardedRobustTrajectory

/-!
# Repeated common-direction batch CE transitions

A fixed finite batch is re-evaluated after every actual `State.trainStep`.
The common residual and safe step therefore always use the successor's own
weights, rather than reusing stale first-step quantities.  Nonempty vocabulary
is enough for nonnegative CE and for the per-step majorizer.

The actual loss differences telescope and dominate the sum of certified
majorizer residuals.  Nonnegative CE and antitonicity imply convergence of the
loss values to their real infimum.  That infimum is not asserted to be zero,
to be a global optimum, or to make parameters or residuals converge.

The batch and ledger inputs are supplied and deterministic.  This is not an
IID, fresh-data, external-quality or hardware-compute theorem.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}




/-- Execute repeatedly on the same finite batch, recomputing the mean residual
and safe step from every actual successor.  Ledger/write arguments stay fixed
logical inputs to the unmodified ordinary transition. -/
noncomputable def fixedBatchState (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : ℕ → TrainState n a r c k
  | 0 => S
  | t + 1 => batchTrainStep X y (fixedBatchState X y S opCost opRisk write t)
      opCost opRisk write

@[simp] theorem fixedBatchState_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    fixedBatchState X y S opCost opRisk write 0 = S := rfl

@[simp] theorem fixedBatchState_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    fixedBatchState X y S opCost opRisk write (t + 1) =
      batchTrainStep X y (fixedBatchState X y S opCost opRisk write t)
        opCost opRisk write := rfl

/-- The actual mean batch CE along the recursive transition. -/
noncomputable def fixedBatchObjective (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  batchCEObjective X y (fixedBatchState X y S opCost opRisk write t)

@[simp] theorem fixedBatchObjective_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    fixedBatchObjective X y S opCost opRisk write 0 = batchCEObjective X y S := rfl

/-- One recursive successor bounds the actual mean loss by minus the computed
majorizer residual.  This is an inequality, not an assertion that the actual
decrease equals that residual. -/
theorem fixedBatchObjective_succ_le_actual_sub_drop [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    fixedBatchObjective X y S opCost opRisk write (t + 1) ≤
      fixedBatchObjective X y S opCost opRisk write t -
        batchCertifiedDrop X
          (coreParameters (fixedBatchState X y S opCost opRisk write t)) y := by
  have h := batchCertifiedDrop_le_actualDrop X y
    (fixedBatchState X y S opCost opRisk write t) opCost opRisk write
  unfold fixedBatchObjective
  rw [fixedBatchState_succ]
  linarith

/-- Repeated batch updates never increase their supplied-batch objective. -/
theorem fixedBatchObjective_succ_le [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    fixedBatchObjective X y S opCost opRisk write (t + 1) ≤
      fixedBatchObjective X y S opCost opRisk write t := by
  have h := fixedBatchObjective_succ_le_actual_sub_drop X y S
    opCost opRisk write t
  have hnonneg := batchCertifiedDrop_nonneg X
    (coreParameters (fixedBatchState X y S opCost opRisk write t)) y
  linarith

/-- The exact actual objective differences telescope without any positive-range
or nonzero-batch hypothesis. -/
theorem fixedBatchObjective_actual_telescope
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ t ∈ Finset.range T,
        (fixedBatchObjective X y S opCost opRisk write t -
          fixedBatchObjective X y S opCost opRisk write (t + 1)) =
      batchCEObjective X y S - fixedBatchObjective X y S opCost opRisk write T := by
  simpa using Finset.sum_range_sub' (fixedBatchObjective X y S opCost opRisk write) T

/-- Total actual loss decrease over a finite trajectory dominates the total
computed certified residuals.  This does not equal the residuals to extra CE
loss decrease. -/
theorem fixedBatchObjective_sum_certifiedDrop_le_telescope [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (T : ℕ) :
    ∑ t ∈ Finset.range T, batchCertifiedDrop X
        (coreParameters (fixedBatchState X y S opCost opRisk write t)) y ≤
      batchCEObjective X y S - fixedBatchObjective X y S opCost opRisk write T := by
  exact ObjectiveTrajectory.sum_drop_le_initial_sub
    (fixedBatchObjective X y S opCost opRisk write)
    (fun t => batchCertifiedDrop X
      (coreParameters (fixedBatchState X y S opCost opRisk write t)) y) T
    (fun t => batchCertifiedDrop_le_actualDrop X y
      (fixedBatchState X y S opCost opRisk write t) opCost opRisk write)

/-- Antitonicity follows from per-successor actual loss nonincrease. -/
theorem fixedBatchObjective_antitone [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Antitone (fixedBatchObjective X y S opCost opRisk write) :=
  antitone_nat_of_succ_le (fixedBatchObjective_succ_le X y S opCost opRisk write)

/-- Every trajectory loss is nonnegative, including the raw empty mean. -/
theorem fixedBatchObjective_nonneg [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    0 ≤ fixedBatchObjective X y S opCost opRisk write t :=
  batchLoss_nonneg X (coreParameters (fixedBatchState X y S opCost opRisk write t)) y

/-- The actual fixed-batch mean CE converges to a real lower bound.  Neither
zero infimum nor convergence of parameters/residuals follows from this fact. -/
theorem fixedBatchObjective_tendsto_ciInf [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fixedBatchObjective X y S opCost opRisk write) atTop
      (𝓝 (⨅ t, fixedBatchObjective X y S opCost opRisk write t)) := by
  exact ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg
    (fixedBatchObjective X y S opCost opRisk write)
    (fixedBatchObjective_antitone X y S opCost opRisk write)
    (fixedBatchObjective_nonneg X y S opCost opRisk write)

/-- The actual loss infimum is nonnegative, without being declared optimal. -/
theorem fixedBatchObjective_ciInf_nonneg [Nonempty V]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    0 ≤ ⨅ t, fixedBatchObjective X y S opCost opRisk write t :=
  ObjectiveTrajectory.ciInf_nonneg _
    (fixedBatchObjective_nonneg X y S opCost opRisk write)

/-- The empty fixed batch has zero raw mean at every time. -/
theorem fixedBatchObjective_empty [Nonempty V]
    (X : Fin 0 → Matrix V (Fin n) ℝ) (y : Fin 0 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    fixedBatchObjective X y S opCost opRisk write t = 0 := by
  simp [fixedBatchObjective, batchCEObjective, batchLoss,
    Hagi.Probability.FiniteFamilyConfidence.empiricalMean]

end Hagi.Contracts.BatchCETrajectory

/-!
# Positive-threshold budgeted Pareto batch trajectories

The existing scaled guarded two-action path is specialized to the canonical
batch controller. Mean and per-sample non-regression follow directly from the
actual action zero/one successors and require no sign assumption on the
threshold. Positive thresholds are used only for discrete progress bounds and
stabilization.
-/

namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Hagi.Unified.ParetoExecution Hagi.Unified.FixedBiasBinaryProgress
open Hagi.Unified.GuardedRobustTrajectory Hagi.Unified.GuardedRobustSelection
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- Every scaled batch successor is either the current state or the guarded
canonical batch update. This does not depend on the threshold's sign. -/
theorem batchCEPath_succ_eq_or
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1) =
      scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i ∨
    scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1) =
      budgetedParetoBatchTrainStep X y
        (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y opCost opRisk write) δ M C h0 S0 i)
        opCost opRisk write := by
  rw [scaledBiasBinaryPath_succ]
  obtain ⟨action, _ha, hstep⟩ :=
    Hagi.Unified.GuardedRobustSelection.guardedRobustNext_exists
    (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write)
    (scaledBiasBinaryValueEstimate (batchParetoProblem (n := n) (a := a)
      (r := r) (k := k) X y opCost opRisk write) δ) (δ / 2)
    (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y opCost opRisk write) δ M C h0 S0 i) M C (0 : Fin 2) h0
  have hcases : action.val = 0 ∨ action.val = 1 := by omega
  rcases hcases with hzero | hone
  · left
    have ha0 : action = 0 := Fin.ext hzero
    subst action
    rw [hstep, batchParetoProblem_step_zero]
  · right
    have ha1 : action = 1 := Fin.ext hone
    subst action
    rw [hstep, batchParetoProblem_step_one]

/-- Actual mean CE does not increase at a scaled guarded successor, including
at empty batches and without any positive-threshold premise. -/
theorem batchCEPath_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    batchCEObjective X y
        (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1)) ≤
      batchCEObjective X y
        (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y opCost opRisk write) δ M C h0 S0 i) := by
  rcases batchCEPath_succ_eq_or X y opCost opRisk write δ M C h0 S0 i with
    hstay | hupdate
  · rw [hstay]
  · rw [hupdate]
    exact batchCEObjective_budgetedParetoBatchTrainStep_le
      X y _ opCost opRisk write

/-- The actual mean batch CE is antitone along the guarded path. -/
theorem batchCEPath_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    Antitone (fun i => batchCEObjective X y
      (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i)) :=
  antitone_nat_of_succ_le (batchCEPath_succ_le X y opCost opRisk write δ M C h0 S0)

/-- Actual mean CE converges to its conditional infimum for every batch size. -/
theorem batchCEPath_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    Tendsto (fun i => batchCEObjective X y
      (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i)) atTop
      (𝓝 (⨅ i, batchCEObjective X y
        (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y opCost opRisk write) δ M C h0 S0 i))) :=
  Hagi.Contracts.ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (batchCEPath_antitone X y opCost opRisk write δ M C h0 S0)
    (fun _ => batchCEObjective_nonneg X y _)

/-- The empty-batch path objective has the raw zero convention at all times. -/
theorem batchCEPath_empty
    (X : Fin 0 → Matrix V (Fin n) ℝ) (y : Fin 0 → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    batchCEObjective X y
      (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i) = 0 :=
  emptyBatchCEObjective_zero X y _

/-- Each actual sample CE does not increase at a scaled guarded successor. -/
theorem batchSampleCEPath_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (b : Fin B) (i : ℕ) :
    batchSampleCE X y b
        (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1)) ≤
      batchSampleCE X y b
        (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y opCost opRisk write) δ M C h0 S0 i) := by
  rcases batchCEPath_succ_eq_or X y opCost opRisk write δ M C h0 S0 i with
    hstay | hupdate
  · rw [hstay]
  · rw [hupdate]
    exact batchSampleCE_budgetedParetoBatchTrainStep_le
      X y _ opCost opRisk write b

/-- Every real batch component is individually antitone along the path. -/
theorem batchSampleCEPath_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (b : Fin B) :
    Antitone (fun i => batchSampleCE X y b
      (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i)) :=
  antitone_nat_of_succ_le
    (batchSampleCEPath_succ_le X y opCost opRisk write δ M C h0 S0 b)

/-- Every real batch component converges to its own conditional infimum. -/
theorem batchSampleCEPath_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (b : Fin B) :
    Tendsto (fun i => batchSampleCE X y b
      (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i)) atTop
      (𝓝 (⨅ i, batchSampleCE X y b
        (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y opCost opRisk write) δ M C h0 S0 i))) :=
  Hagi.Contracts.ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (batchSampleCEPath_antitone X y opCost opRisk write δ M C h0 S0 b)
    (fun _ => batchSampleCE_nonneg X y b _)

/-- Nonnegative mean CE gives the batch controller an intrinsic value bound. -/
theorem batchCEProblem_value_le_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (S : TrainState n a r c k) :
    (batchParetoProblem X y opCost opRisk write).value S ≤ 0 :=
  neg_nonpos.mpr (batchCEObjective_nonneg X y S)

/-- At a positive threshold, the number of positive actual value gains is at
most the initial actual batch mean CE divided by the threshold. -/
theorem batchCEProgressCount_le_div
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (T : ℕ) :
    (scaledBiasBinaryProgressCount
      (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
        X y opCost opRisk write) δ M C h0 S0 T : ℝ) ≤
      batchCEObjective X y S0 / δ := by
  have hcount := scaledBiasBinaryProgressCount_le_div
    (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write) δ hδ M C h0 S0
    (fun S => batchParetoProblem_step_zero X y opCost opRisk write S) 0
    (fun _ => batchCEProblem_value_le_zero X y opCost opRisk write _) T
  rw [scaledBiasBinaryPath_zero] at hcount
  simpa only [batchParetoProblem, zero_sub, neg_neg] using hcount

/-- A nonnegative initial declared budget remains nonnegative along the entire
scaled path; neither positivity of the threshold nor of the cost is needed. -/
theorem batchCEPath_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (hbudget : 0 ≤ S0.res.budget) (T : ℕ) :
    0 ≤ (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y opCost opRisk write) δ M C h0 S0 T).res.budget := by
  induction T with
  | zero => exact hbudget
  | succ T ih =>
      rcases batchCEPath_succ_eq_or X y opCost opRisk write δ M C h0 S0 T with
        hstay | hupdate
      · rw [hstay]
        exact ih
      · rw [hupdate]
        exact budgetedParetoBatchTrainStep_budget_nonneg
          X y _ opCost opRisk write ih

/-- A positive actual value gain really executes the full guarded canonical
batch transition, so that accepted step contributes `opCost` to `res.flops`.
Other steps contribute zero. -/
theorem batchCEPath_flops_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1)).res.flops =
      (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i).res.flops +
      if 0 < scaledBiasBinaryGain (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i then opCost else 0 := by
  classical
  by_cases hpos : 0 < scaledBiasBinaryGain
      (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
        X y opCost opRisk write) δ M C h0 S0 i
  · have hsucc := scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
      (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
        X y opCost opRisk write) δ hδ M C h0 S0
      (fun S => batchParetoProblem_step_zero X y opCost opRisk write S) i hpos
    rw [batchParetoProblem_step_one] at hsucc
    have hactive : ((0 ≤ opCost) ∧ opCost ≤
        (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y opCost opRisk write) δ M C h0 S0 i).res.budget) ∧
        (∀ b, batchSampleCE X y b (batchTrainStep X y
          (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
            (k := k) X y opCost opRisk write) δ M C h0 S0 i)
          opCost opRisk write) ≤ batchSampleCE X y b
          (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
            (k := k) X y opCost opRisk write) δ M C h0 S0 i)) := by
      by_contra hinactive
      have hzero : scaledBiasBinaryGain
          (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
            X y opCost opRisk write) δ M C h0 S0 i = 0 := by
        rw [scaledBiasBinaryGain_eq_sub, hsucc,
          budgetedParetoBatchTrainStep_of_inactive
            X y _ opCost opRisk write hinactive, sub_self]
      linarith
    rw [hsucc, budgetedParetoBatchTrainStep_of_active
      X y _ opCost opRisk write hactive, batchTrainStep, trainStep_flops,
      batchTrainInput, ite_eq_left hpos]
  · have hnoup : ¬ estimatedUpgrade
        (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
          X y opCost opRisk write)
        (scaledBiasBinaryValueEstimate
          (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
            X y opCost opRisk write) δ) (δ / 2)
        (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y opCost opRisk write) δ M C h0 S0 i)
        M C (0 : Fin 2) := by
      intro hup
      exact hpos (scaledBiasBinaryGain_pos_of_upgrade
        (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
          X y opCost opRisk write) δ hδ M C h0 S0
        (fun S => batchParetoProblem_step_zero X y opCost opRisk write S) i hup)
    rw [scaledBiasBinaryPath_succ,
      Hagi.Unified.GuardedRobustSelection.guardedRobustNext_of_no_upgrade
        (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
          X y opCost opRisk write)
        (scaledBiasBinaryValueEstimate
          (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
            X y opCost opRisk write) δ) (δ / 2) _ M C (0 : Fin 2) h0 hnoup]
    rw [batchParetoProblem_step_zero, ite_eq_right hpos, add_zero]

/-- Exact declared-ledger telescope for accepted positive-gain batch steps. -/
theorem batchCEPath_flops_eq
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (T : ℕ) :
    (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 T).res.flops =
      S0.res.flops + opCost * (scaledBiasBinaryProgressCount
        (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
          X y opCost opRisk write) δ M C h0 S0 T : ℝ) := by
  apply scaledBiasBinaryTrainPath_flops_eq
    (batchParetoProblem X y opCost opRisk write) δ hδ M C h0 S0
    (fun S => batchParetoProblem_step_zero X y opCost opRisk write S) opCost ?_ T
  intro i hpos
  have h := batchCEPath_flops_succ X y opCost opRisk write δ hδ M C h0 S0 i
  rw [scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
    (batchParetoProblem X y opCost opRisk write) δ hδ M C h0 S0
    (fun S => batchParetoProblem_step_zero X y opCost opRisk write S) i hpos,
    ite_eq_left hpos] at h
  exact h

/-- With nonnegative supplied cost, accepted positive-gain batch updates have
declared `res.flops` increment at most `(opCost / δ) * initial mean CE`. -/
theorem batchCEPath_flops_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (T : ℕ) (hcost : 0 ≤ opCost) :
    (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 T).res.flops ≤
      S0.res.flops + (opCost / δ) * batchCEObjective X y S0 := by
  have h_value : (batchParetoProblem X y opCost opRisk write).value S0 =
      -batchCEObjective X y S0 := rfl
  have hbound := scaledBiasBinaryTrainPath_flops_le_of_value_nonpos
    (batchParetoProblem X y opCost opRisk write) δ hδ M C h0 S0
    (fun S => batchParetoProblem_step_zero X y opCost opRisk write S)
    opCost hcost (fun S => batchCEProblem_value_le_zero X y opCost opRisk write S)
    (by
      intro i hpos
      have h := batchCEPath_flops_succ X y opCost opRisk write δ hδ M C h0 S0 i
      rw [scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
        (batchParetoProblem X y opCost opRisk write) δ hδ M C h0 S0
        (fun S => batchParetoProblem_step_zero X y opCost opRisk write S) i hpos,
        ite_eq_left hpos] at h
      exact h) T
  rw [h_value, neg_neg] at hbound
  exact hbound

/-- Eventually every positive-threshold batch successor is stationary. -/
theorem batchCEPath_eventually_succ_eq
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, ∀ i ≥ N,
      scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1) =
      scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i :=
  scaledBiasBinaryPath_eventually_succ_eq
    (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write) δ hδ M C h0 S0
    (fun S => batchParetoProblem_step_zero X y opCost opRisk write S) 0
    (fun _ => batchCEProblem_value_le_zero X y opCost opRisk write _)

/-- The positive-threshold batch path eventually equals one of its own states. -/
theorem batchCEPath_eventually_eq
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, ∀ i ≥ N,
      scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i =
      scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 N :=
  scaledBiasBinaryPath_eventually_eq
    (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write) δ hδ M C h0 S0
    (fun S => batchParetoProblem_step_zero X y opCost opRisk write S) 0
    (fun _ => batchCEProblem_value_le_zero X y opCost opRisk write _)

/-- Under any supplied full-state topology, the path converges to an eventual
state. No optimality or objective-zero identification is asserted. -/
theorem batchCEPath_tendsto_eventual_state
    [TopologicalSpace (TrainState n a r c k)]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, Tendsto (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a)
      (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0) atTop
      (𝓝 (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 N)) :=
  scaledBiasBinaryPath_tendsto_eventual_value
    (batchParetoProblem (n := n) (a := a) (r := r) (k := k)
      X y opCost opRisk write) δ hδ M C h0 S0
    (fun S => batchParetoProblem_step_zero X y opCost opRisk write S) 0
    (fun _ => batchCEProblem_value_le_zero X y opCost opRisk write _)

/-- Actual initial mean CE decrease of the committed same-label guarded step. -/
noncomputable def sameZeroInitialMeanDrop : ℝ :=
  batchCEObjective mixedFeatures sameZeroLabels identityInitialState -
    batchCEObjective mixedFeatures sameZeroLabels identityParetoBatchStep

/-- The proved actual initial drop is strictly positive. -/
theorem sameZeroInitialMeanDrop_pos : 0 < sameZeroInitialMeanDrop := by
  rw [sameZeroInitialMeanDrop, identityParetoBatchStep_eq_batchTrainStep]
  exact sub_pos.mpr (batchCEObjective_batchTrainStep_lt
    mixedFeatures sameZeroLabels identityInitialState (1 / 2) (1 / 4) none
    sameZero_rangeSquare_pos)

/-- A concrete threshold defined from the proved actual drop, not guessed. -/
noncomputable def sameZeroScaledThreshold : ℝ := sameZeroInitialMeanDrop / 2

/-- Half the proved positive actual initial drop is a positive threshold. -/
theorem sameZeroScaledThreshold_pos : 0 < sameZeroScaledThreshold :=
  div_pos sameZeroInitialMeanDrop_pos (by norm_num)

/-- The same-label scaled guarded path, with unit memory cap and two logical
batch-operation cap units. -/
noncomputable def identityScaledBatchCEPath : ℕ → TrainState 2 0 0 0 0 :=
  scaledBiasBinaryPath
    (batchParetoProblem (n := 2) (a := 0) (r := 0) (c := 0) (k := 0)
      mixedFeatures sameZeroLabels (1 / 2) (1 / 4) none)
    sameZeroScaledThreshold 1 2
    (batchPareto_stay_feasible mixedFeatures sameZeroLabels
      (1 / 2) (1 / 4) none 1 2) identityInitialState

/-- The first real threshold upgrade executes `identityParetoBatchStep`, hence
the canonical guarded batch training transition rather than an identity step. -/
theorem identityScaledBatchCEPath_one :
    identityScaledBatchCEPath 1 = identityParetoBatchStep := by
  let p : ControllerProblem (Fin 2) (TrainState 2 0 0 0 0) :=
    batchParetoProblem mixedFeatures sameZeroLabels (1 / 2) (1 / 4) none
  let h0 : (0 : Fin 2) ∈ feasible p 1 2 := by
    dsimp only [p]
    exact batchPareto_stay_feasible mixedFeatures sameZeroLabels
      (1 / 2) (1 / 4) none 1 2
  have h1 : (1 : Fin 2) ∈ feasible p 1 2 := by
    dsimp only [p]
    exact (batchPareto_one_feasible_iff _ _ _ _ _ _ _).mpr (by norm_num)
  have hstep : p.step (1 : Fin 2) identityInitialState =
      identityParetoBatchStep := by
    change budgetedParetoBatchTrainStep mixedFeatures sameZeroLabels
      identityInitialState (1 / 2) (1 / 4) none = identityParetoBatchStep
    rfl
  have hstay : ∀ S : TrainState 2 0 0 0 0, p.step (0 : Fin 2) S = S := by
    intro S
    dsimp only [p]
    exact batchParetoProblem_step_zero _ _ _ _ _ _
  have hdrop : sameZeroScaledThreshold ≤ sameZeroInitialMeanDrop := by
    rw [sameZeroScaledThreshold]
    linarith only [sameZeroInitialMeanDrop_pos]
  change sameZeroScaledThreshold ≤
    batchCEObjective mixedFeatures sameZeroLabels identityInitialState -
      batchCEObjective mixedFeatures sameZeroLabels identityParetoBatchStep at hdrop
  have hup : estimatedUpgrade p
      (scaledBiasBinaryValueEstimate p sameZeroScaledThreshold)
      (sameZeroScaledThreshold / 2)
      (scaledBiasBinaryPath p sameZeroScaledThreshold 1 2 h0
        identityInitialState 0) 1 2 0 := by
    refine ⟨1, h1, ?_⟩
    change (-batchCEObjective mixedFeatures sameZeroLabels
        (p.step 0 (scaledBiasBinaryPath p sameZeroScaledThreshold 1 2 h0
          identityInitialState 0)) - sameZeroScaledThreshold / 2) +
        2 * (sameZeroScaledThreshold / 2) ≤
      -batchCEObjective mixedFeatures sameZeroLabels
        (p.step 1 (scaledBiasBinaryPath p sameZeroScaledThreshold 1 2 h0
          identityInitialState 0)) - sameZeroScaledThreshold / 2
    rw [scaledBiasBinaryPath_zero, hstay, hstep]
    linarith only [hdrop]
  have hnext := scaledBiasBinaryPath_succ_eq_step_one_of_upgrade p
    sameZeroScaledThreshold sameZeroScaledThreshold_pos 1 2 h0
    identityInitialState hstay 0 hup
  rw [scaledBiasBinaryPath_zero] at hnext
  unfold identityScaledBatchCEPath
  exact hnext.trans hstep

end Hagi.Contracts.BatchCETrajectory
