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

/-- Every scaled generic guarded successor either stays or executes the
current-state guarded input transition. The threshold need not be positive. -/
theorem guardedBatchCEPath_succ_eq_or
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 (i + 1) =
      scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 i ∨
    scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 (i + 1) =
      guardedBatchTrainStep X y inputFor
        (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y inputFor) δ M C h0 S0 i) := by
  rw [scaledBiasBinaryPath_succ]
  obtain ⟨action, _ha, hstep⟩ :=
    Hagi.Unified.GuardedRobustSelection.guardedRobustNext_exists
    (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
    (scaledBiasBinaryValueEstimate (guardedBatchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y inputFor) δ) (δ / 2)
    (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y inputFor) δ M C h0 S0 i) M C (0 : Fin 2) h0
  have hcases : action.val = 0 ∨ action.val = 1 := by omega
  rcases hcases with hzero | hone
  · left
    have ha0 : action = 0 := Fin.ext hzero
    subst action
    rw [hstep, guardedBatchParetoProblem_step_zero]
  · right
    have ha1 : action = 1 := Fin.ext hone
    subst action
    rw [hstep, guardedBatchParetoProblem_step_one]

/-- Generic guarded successors do not increase actual supplied-batch mean CE. -/
theorem guardedBatchCEPath_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    batchCEObjective X y
        (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y inputFor) δ M C h0 S0 (i + 1)) ≤
      batchCEObjective X y
        (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y inputFor) δ M C h0 S0 i) := by
  rcases guardedBatchCEPath_succ_eq_or X y inputFor δ M C h0 S0 i with
    hstay | hupdate
  · rw [hstay]
  · rw [hupdate]
    exact batchCEObjective_guardedBatchTrainStep_le X y inputFor _

/-- Actual supplied-batch mean CE is antitone along every generic guarded path. -/
theorem guardedBatchCEPath_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) :
    Antitone (fun i => batchCEObjective X y
      (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 i)) :=
  antitone_nat_of_succ_le (guardedBatchCEPath_succ_le X y inputFor δ M C h0 S0)

/-- Actual mean CE converges to its own conditional infimum, including when
the batch is empty. This is non-regression, not a strict-descent assertion. -/
theorem guardedBatchCEPath_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) :
    Tendsto (fun i => batchCEObjective X y
      (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 i)) atTop
      (𝓝 (⨅ i, batchCEObjective X y
        (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y inputFor) δ M C h0 S0 i))) :=
  Hagi.Contracts.ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (guardedBatchCEPath_antitone X y inputFor δ M C h0 S0)
    (fun _ => batchCEObjective_nonneg X y _)

/-- The generic guarded empty-batch path retains the explicit raw-zero mean
convention. -/
theorem guardedBatchCEPath_empty
    (X : Fin 0 → Matrix V (Fin n) ℝ) (y : Fin 0 → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    batchCEObjective X y
      (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 i) = 0 :=
  emptyBatchCEObjective_zero X y _

/-- Each real sample of the supplied batch is separately non-increasing along
the generic guarded path; the target at that sample supplies local nonemptiness
where the existing CE API needs it. -/
theorem guardedBatchSampleCEPath_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (b : Fin B) (i : ℕ) :
    batchSampleCE X y b
        (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y inputFor) δ M C h0 S0 (i + 1)) ≤
      batchSampleCE X y b
        (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y inputFor) δ M C h0 S0 i) := by
  rcases guardedBatchCEPath_succ_eq_or X y inputFor δ M C h0 S0 i with
    hstay | hupdate
  · rw [hstay]
  · rw [hupdate]
    exact batchSampleCE_guardedBatchTrainStep_le X y inputFor _ b

/-- Every real supplied-batch component is antitone along the generic path. -/
theorem guardedBatchSampleCEPath_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (b : Fin B) :
    Antitone (fun i => batchSampleCE X y b
      (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 i)) :=
  antitone_nat_of_succ_le
    (guardedBatchSampleCEPath_succ_le X y inputFor δ M C h0 S0 b)

/-- Every real supplied-batch component converges to its own conditional
infimum, independently of the other components. -/
theorem guardedBatchSampleCEPath_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (b : Fin B) :
    Tendsto (fun i => batchSampleCE X y b
      (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 i)) atTop
      (𝓝 (⨅ i, batchSampleCE X y b
        (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y inputFor) δ M C h0 S0 i))) :=
  Hagi.Contracts.ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (guardedBatchSampleCEPath_antitone X y inputFor δ M C h0 S0 b)
    (fun _ => batchSampleCE_nonneg X y b _)

/-- Nonnegative actual mean CE gives the generic controller value bound zero. -/
theorem guardedBatchCEProblem_value_le_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    (guardedBatchParetoProblem X y inputFor).value S ≤ 0 :=
  neg_nonpos.mpr (batchCEObjective_nonneg X y S)

/-- At a positive threshold, positive actual value gains are bounded by the
initial actual supplied-batch mean CE divided by that threshold. -/
theorem guardedBatchCEProgressCount_le_div
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (T : ℕ) :
    (scaledBiasBinaryProgressCount (guardedBatchParetoProblem (n := n) (a := a)
        (r := r) (k := k) X y inputFor) δ M C h0 S0 T : ℝ) ≤
      batchCEObjective X y S0 / δ := by
  have hcount := scaledBiasBinaryProgressCount_le_div
    (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
    δ hδ M C h0 S0
    (fun S => guardedBatchParetoProblem_step_zero X y inputFor S) 0
    (fun _ => guardedBatchCEProblem_value_le_zero X y inputFor _) T
  rw [scaledBiasBinaryPath_zero] at hcount
  simpa only [guardedBatchParetoProblem, zero_sub, neg_neg] using hcount

/-- A nonnegative initial budget stays nonnegative along the generic guarded
path; no positive threshold or positive operation cost is required. -/
theorem guardedBatchCEPath_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (hbudget : 0 ≤ S0.res.budget) (T : ℕ) :
    0 ≤ (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a)
      (r := r) (k := k) X y inputFor) δ M C h0 S0 T).res.budget := by
  induction T with
  | zero => exact hbudget
  | succ T ih =>
      rcases guardedBatchCEPath_succ_eq_or X y inputFor δ M C h0 S0 T with
        hstay | hupdate
      · rw [hstay]
        exact ih
      · rw [hupdate]
        exact guardedBatchTrainStep_budget_nonneg X y inputFor _ ih

/-- A positive actual gain forces both action one and an active generic guard.
Only that accepted whole-state transition adds the supplied operation cost;
a rejected guard or unselected update adds zero. -/
theorem guardedBatchCEPath_flops_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (opCost : ℝ)
    (hcost : ∀ S, (inputFor S).opCost = opCost) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 (i + 1)).res.flops =
      (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 i).res.flops +
      if 0 < scaledBiasBinaryGain (guardedBatchParetoProblem (n := n) (a := a)
        (r := r) (k := k) X y inputFor) δ M C h0 S0 i then opCost else 0 := by
  classical
  by_cases hpos : 0 < scaledBiasBinaryGain
      (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
      δ M C h0 S0 i
  · have hsucc := scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
      (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
      δ hδ M C h0 S0
      (fun S => guardedBatchParetoProblem_step_zero X y inputFor S) i hpos
    rw [guardedBatchParetoProblem_step_one] at hsucc
    have hactive : ((0 ≤ (inputFor (scaledBiasBinaryPath
          (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
            X y inputFor) δ M C h0 S0 i)).opCost) ∧
        (inputFor (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n)
          (a := a) (r := r) (k := k) X y inputFor) δ M C h0 S0 i)).opCost ≤
        (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y inputFor) δ M C h0 S0 i).res.budget) ∧
        (∀ b, batchSampleCE X y b (trainStep (scaledBiasBinaryPath
          (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
            X y inputFor) δ M C h0 S0 i) (inputFor (scaledBiasBinaryPath
          (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
            X y inputFor) δ M C h0 S0 i))) ≤ batchSampleCE X y b
          (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a)
            (r := r) (k := k) X y inputFor) δ M C h0 S0 i)) := by
      by_contra hinactive
      have hzero : scaledBiasBinaryGain
          (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
          δ M C h0 S0 i = 0 := by
        rw [scaledBiasBinaryGain_eq_sub, hsucc,
          guardedBatchTrainStep_of_inactive X y inputFor _ hinactive, sub_self]
      linarith
    rw [hsucc, guardedBatchTrainStep_flops_of_active X y inputFor _ hactive,
      hcost, ite_eq_left hpos]
  · have hnoup : ¬ estimatedUpgrade
        (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
        (scaledBiasBinaryValueEstimate (guardedBatchParetoProblem (n := n) (a := a)
          (r := r) (k := k) X y inputFor) δ) (δ / 2)
        (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
          (k := k) X y inputFor) δ M C h0 S0 i) M C (0 : Fin 2) := by
      intro hup
      exact hpos (scaledBiasBinaryGain_pos_of_upgrade
        (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
        δ hδ M C h0 S0
        (fun S => guardedBatchParetoProblem_step_zero X y inputFor S) i hup)
    rw [scaledBiasBinaryPath_succ,
      Hagi.Unified.GuardedRobustSelection.guardedRobustNext_of_no_upgrade
        (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
        (scaledBiasBinaryValueEstimate (guardedBatchParetoProblem (n := n) (a := a)
          (r := r) (k := k) X y inputFor) δ) (δ / 2) _ M C (0 : Fin 2) h0 hnoup]
    rw [guardedBatchParetoProblem_step_zero, ite_eq_right hpos, add_zero]

/-- Exact declared-ledger telescope, inherited directly from the shared
positive-gain path theorem rather than reproved by induction here. -/
theorem guardedBatchCEPath_flops_eq
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (opCost : ℝ)
    (hcost : ∀ S, (inputFor S).opCost = opCost) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (T : ℕ) :
    (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 T).res.flops =
      S0.res.flops + opCost * (scaledBiasBinaryProgressCount
        (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
          X y inputFor) δ M C h0 S0 T : ℝ) := by
  apply scaledBiasBinaryTrainPath_flops_eq
    (guardedBatchParetoProblem X y inputFor) δ hδ M C h0 S0
    (fun S => guardedBatchParetoProblem_step_zero X y inputFor S) opCost ?_ T
  intro i hpos
  have h := guardedBatchCEPath_flops_succ X y inputFor opCost hcost δ hδ M C h0 S0 i
  rw [scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
    (guardedBatchParetoProblem X y inputFor) δ hδ M C h0 S0
    (fun S => guardedBatchParetoProblem_step_zero X y inputFor S) i hpos,
    ite_eq_left hpos] at h
  exact h

/-- With nonnegative supplied cost, accepted positive-gain updates have exact
declared cost bounded by `(opCost / δ) * initial actual mean CE`. -/
theorem guardedBatchCEPath_flops_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (opCost : ℝ)
    (hcost : ∀ S, (inputFor S).opCost = opCost) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) (T : ℕ) (hopCost : 0 ≤ opCost) :
    (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 T).res.flops ≤
      S0.res.flops + (opCost / δ) * batchCEObjective X y S0 := by
  have h_value : (guardedBatchParetoProblem X y inputFor).value S0 =
      -batchCEObjective X y S0 := rfl
  have hbound := scaledBiasBinaryTrainPath_flops_le_of_value_nonpos
    (guardedBatchParetoProblem X y inputFor) δ hδ M C h0 S0
    (fun S => guardedBatchParetoProblem_step_zero X y inputFor S)
    opCost hopCost (fun S => guardedBatchCEProblem_value_le_zero X y inputFor S)
    (by
      intro i hpos
      have h := guardedBatchCEPath_flops_succ X y inputFor opCost hcost δ hδ M C h0 S0 i
      rw [scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
        (guardedBatchParetoProblem X y inputFor) δ hδ M C h0 S0
        (fun S => guardedBatchParetoProblem_step_zero X y inputFor S) i hpos,
        ite_eq_left hpos] at h
      exact h) T
  rw [h_value, neg_neg] at hbound
  exact hbound

/-- Eventually every positive-threshold generic guarded successor is
stationary. -/
theorem guardedBatchCEPath_eventually_succ_eq
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, ∀ i ≥ N,
      scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 (i + 1) =
      scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 i :=
  scaledBiasBinaryPath_eventually_succ_eq
    (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
    δ hδ M C h0 S0
    (fun S => guardedBatchParetoProblem_step_zero X y inputFor S) 0
    (fun _ => guardedBatchCEProblem_value_le_zero X y inputFor _)

/-- The generic guarded path eventually equals one of its own full states. -/
theorem guardedBatchCEPath_eventually_eq
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, ∀ i ≥ N,
      scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 i =
      scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 N :=
  scaledBiasBinaryPath_eventually_eq
    (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
    δ hδ M C h0 S0
    (fun S => guardedBatchParetoProblem_step_zero X y inputFor S) 0
    (fun _ => guardedBatchCEProblem_value_le_zero X y inputFor _)

/-- Under any supplied full-state topology, generic eventual constancy gives
convergence to an eventual state, with no optimality or zero-loss conclusion. -/
theorem guardedBatchCEPath_tendsto_eventual_state
    [TopologicalSpace (TrainState n a r c k)]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (guardedBatchParetoProblem
      (n := n) (a := a) (r := r) (k := k) X y inputFor) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, Tendsto (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a)
      (r := r) (k := k) X y inputFor) δ M C h0 S0) atTop
      (𝓝 (scaledBiasBinaryPath (guardedBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y inputFor) δ M C h0 S0 N)) :=
  scaledBiasBinaryPath_tendsto_eventual_value
    (guardedBatchParetoProblem (n := n) (a := a) (r := r) (k := k) X y inputFor)
    δ hδ M C h0 S0
    (fun S => guardedBatchParetoProblem_step_zero X y inputFor S) 0
    (fun _ => guardedBatchCEProblem_value_le_zero X y inputFor _)

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
        opCost opRisk write :=
  guardedBatchCEPath_succ_eq_or X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ M C h0 S0 i

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
          (k := k) X y opCost opRisk write) δ M C h0 S0 i) :=
  guardedBatchCEPath_succ_le X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ M C h0 S0 i

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
  guardedBatchCEPath_antitone X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ M C h0 S0

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
  guardedBatchCEPath_tendsto_ciInf X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ M C h0 S0

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
  guardedBatchCEPath_empty X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ M C h0 S0 i

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
          (k := k) X y opCost opRisk write) δ M C h0 S0 i) :=
  guardedBatchSampleCEPath_succ_le X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ M C h0 S0 b i

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
  guardedBatchSampleCEPath_antitone X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ M C h0 S0 b

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
  guardedBatchSampleCEPath_tendsto_ciInf X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ M C h0 S0 b

/-- Nonnegative mean CE gives the batch controller an intrinsic value bound. -/
theorem batchCEProblem_value_le_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (S : TrainState n a r c k) :
    (batchParetoProblem X y opCost opRisk write).value S ≤ 0 :=
  guardedBatchCEProblem_value_le_zero X y
    (fun S => batchTrainInput X y S opCost opRisk write) S

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
      batchCEObjective X y S0 / δ :=
  guardedBatchCEProgressCount_le_div X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ hδ M C h0 S0 T

/-- A nonnegative initial declared budget remains nonnegative along the entire
scaled path; neither positivity of the threshold nor of the cost is needed. -/
theorem batchCEPath_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (batchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (hbudget : 0 ≤ S0.res.budget) (T : ℕ) :
    0 ≤ (scaledBiasBinaryPath (batchParetoProblem (n := n) (a := a) (r := r)
      (k := k) X y opCost opRisk write) δ M C h0 S0 T).res.budget :=
  guardedBatchCEPath_budget_nonneg X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ M C h0 S0 hbudget T

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
        (k := k) X y opCost opRisk write) δ M C h0 S0 i then opCost else 0 :=
  guardedBatchCEPath_flops_succ X y
    (fun S => batchTrainInput X y S opCost opRisk write) opCost (fun _ => rfl)
    δ hδ M C h0 S0 i

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
          X y opCost opRisk write) δ M C h0 S0 T : ℝ) :=
  guardedBatchCEPath_flops_eq X y
    (fun S => batchTrainInput X y S opCost opRisk write) opCost (fun _ => rfl)
    δ hδ M C h0 S0 T

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
      S0.res.flops + (opCost / δ) * batchCEObjective X y S0 :=
  guardedBatchCEPath_flops_le X y
    (fun S => batchTrainInput X y S opCost opRisk write) opCost (fun _ => rfl)
    δ hδ M C h0 S0 T hcost

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
  guardedBatchCEPath_eventually_succ_eq X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ hδ M C h0 S0

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
  guardedBatchCEPath_eventually_eq X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ hδ M C h0 S0

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
  guardedBatchCEPath_tendsto_eventual_state X y
    (fun S => batchTrainInput X y S opCost opRisk write) δ hδ M C h0 S0

/-- Every minimum-norm guarded successor either stays or executes the guarded
current-state minimum-norm input. -/
theorem minimumNormBatchCEPath_succ_eq_or
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1) =
      scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i ∨
    scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1) =
      batchMinimumNormTrainStep X y
        (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a)
          (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 i)
        opCost opRisk write :=
  guardedBatchCEPath_succ_eq_or X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ M C h0 S0 i

/-- Actual mean CE does not increase at a minimum-norm guarded successor. -/
theorem minimumNormBatchCEPath_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    batchCEObjective X y
        (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a)
          (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1)) ≤
      batchCEObjective X y
        (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a)
          (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 i) :=
  guardedBatchCEPath_succ_le X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ M C h0 S0 i

/-- Actual mean batch CE is antitone along the minimum-norm guarded path. -/
theorem minimumNormBatchCEPath_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    Antitone (fun i => batchCEObjective X y
      (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i)) :=
  guardedBatchCEPath_antitone X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ M C h0 S0

/-- Actual mean CE along the minimum-norm path converges to its own conditional
infimum. The generic guard alone never supplies strict descent. -/
theorem minimumNormBatchCEPath_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    Tendsto (fun i => batchCEObjective X y
      (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i)) atTop
      (𝓝 (⨅ i, batchCEObjective X y
        (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a)
          (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 i))) :=
  guardedBatchCEPath_tendsto_ciInf X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ M C h0 S0

/-- The minimum-norm empty-batch path retains the raw zero-mean convention. -/
theorem minimumNormBatchCEPath_empty
    (X : Fin 0 → Matrix V (Fin n) ℝ) (y : Fin 0 → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    batchCEObjective X y
      (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i) = 0 :=
  guardedBatchCEPath_empty X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ M C h0 S0 i

/-- Each actual sample CE does not increase at a minimum-norm guarded
successor. -/
theorem minimumNormBatchSampleCEPath_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (b : Fin B) (i : ℕ) :
    batchSampleCE X y b
        (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a)
          (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1)) ≤
      batchSampleCE X y b
        (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a)
          (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 i) :=
  guardedBatchSampleCEPath_succ_le X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ M C h0 S0 b i

/-- Every real batch component is antitone along the minimum-norm path. -/
theorem minimumNormBatchSampleCEPath_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (b : Fin B) :
    Antitone (fun i => batchSampleCE X y b
      (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i)) :=
  guardedBatchSampleCEPath_antitone X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ M C h0 S0 b

/-- Every real sample CE along the minimum-norm path converges to its own
conditional infimum. -/
theorem minimumNormBatchSampleCEPath_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (b : Fin B) :
    Tendsto (fun i => batchSampleCE X y b
      (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i)) atTop
      (𝓝 (⨅ i, batchSampleCE X y b
        (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a)
          (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 i))) :=
  guardedBatchSampleCEPath_tendsto_ciInf X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ M C h0 S0 b

/-- Nonnegative mean CE bounds the minimum-norm controller value by zero. -/
theorem minimumNormBatchCEProblem_value_le_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (S : TrainState n a r c k) :
    (minimumNormBatchParetoProblem X y opCost opRisk write).value S ≤ 0 :=
  guardedBatchCEProblem_value_le_zero X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S

/-- Positive-gain count on the minimum-norm path is bounded by the initial
actual supplied-batch mean CE divided by the positive threshold. -/
theorem minimumNormBatchCEProgressCount_le_div
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (T : ℕ) :
    (scaledBiasBinaryProgressCount
      (minimumNormBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
        X y opCost opRisk write) δ M C h0 S0 T : ℝ) ≤
      batchCEObjective X y S0 / δ :=
  guardedBatchCEProgressCount_le_div X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ hδ M C h0 S0 T

/-- A nonnegative initial budget remains nonnegative along the minimum-norm
path, without any sign premise on threshold or operation cost. -/
theorem minimumNormBatchCEPath_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (hbudget : 0 ≤ S0.res.budget) (T : ℕ) :
    0 ≤ (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a)
      (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 T).res.budget :=
  guardedBatchCEPath_budget_nonneg X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write)
    δ M C h0 S0 hbudget T

/-- A positive actual gain on the minimum-norm path forces action one and an
active guard. Exactly accepted steps add `opCost`; rejected or unselected ones
add zero. -/
theorem minimumNormBatchCEPath_flops_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1)).res.flops =
      (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i).res.flops +
      if 0 < scaledBiasBinaryGain (minimumNormBatchParetoProblem (n := n) (a := a)
        (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 i then opCost else 0 :=
  guardedBatchCEPath_flops_succ X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write)
    opCost (fun _ => rfl) δ hδ M C h0 S0 i

/-- Exact accepted-step-only declared-cost telescope for the minimum-norm path. -/
theorem minimumNormBatchCEPath_flops_eq
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (T : ℕ) :
    (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 T).res.flops =
      S0.res.flops + opCost * (scaledBiasBinaryProgressCount
        (minimumNormBatchParetoProblem (n := n) (a := a) (r := r) (k := k)
          X y opCost opRisk write) δ M C h0 S0 T : ℝ) :=
  guardedBatchCEPath_flops_eq X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write)
    opCost (fun _ => rfl) δ hδ M C h0 S0 T

/-- Accepted minimum-norm updates have declared cost bounded by
`(opCost / δ) * initial actual mean CE` when the supplied cost is nonnegative. -/
theorem minimumNormBatchCEPath_flops_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (T : ℕ) (hcost : 0 ≤ opCost) :
    (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 T).res.flops ≤
      S0.res.flops + (opCost / δ) * batchCEObjective X y S0 :=
  guardedBatchCEPath_flops_le X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write)
    opCost (fun _ => rfl) δ hδ M C h0 S0 T hcost

/-- Eventually every positive-threshold minimum-norm successor is stationary. -/
theorem minimumNormBatchCEPath_eventually_succ_eq
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, ∀ i ≥ N,
      scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 (i + 1) =
      scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i :=
  guardedBatchCEPath_eventually_succ_eq X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ hδ M C h0 S0

/-- The minimum-norm positive-threshold path eventually equals one full own
state. -/
theorem minimumNormBatchCEPath_eventually_eq
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, ∀ i ≥ N,
      scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 i =
      scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a) (r := r)
        (k := k) X y opCost opRisk write) δ M C h0 S0 N :=
  guardedBatchCEPath_eventually_eq X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ hδ M C h0 S0

/-- Under a supplied full-state topology, the minimum-norm path converges to an
eventual own state. No optimality, zero-loss or parameter conclusion is added. -/
theorem minimumNormBatchCEPath_tendsto_eventual_state
    [TopologicalSpace (TrainState n a r c k)]
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, Tendsto (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n)
      (a := a) (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0) atTop
      (𝓝 (scaledBiasBinaryPath (minimumNormBatchParetoProblem (n := n) (a := a)
        (r := r) (k := k) X y opCost opRisk write) δ M C h0 S0 N)) :=
  guardedBatchCEPath_tendsto_eventual_state X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) δ hδ M C h0 S0

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

/-- Actual initial mean-CE decrease of the accepted singleton minimum-norm
step, measured from the old state to the complete new state. -/
noncomputable def minimumNormIdentityInitialMeanDrop : ℝ :=
  batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
      identityInitialState -
    batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
      identityMinimumNormBatchStep

/-- The committed singleton minimum-norm step has strictly positive actual
initial mean-CE drop. -/
theorem minimumNormIdentityInitialMeanDrop_pos :
    0 < minimumNormIdentityInitialMeanDrop := by
  rw [minimumNormIdentityInitialMeanDrop]
  exact sub_pos.mpr batchCEObjective_identityMinimumNormBatchStep_lt

/-- A threshold defined as half the proved actual singleton initial drop. -/
noncomputable def minimumNormIdentityScaledThreshold : ℝ :=
  minimumNormIdentityInitialMeanDrop / 2

/-- Half the strict singleton initial mean-CE drop is positive. -/
theorem minimumNormIdentityScaledThreshold_pos :
    0 < minimumNormIdentityScaledThreshold :=
  div_pos minimumNormIdentityInitialMeanDrop_pos (by norm_num)

/-- The singleton minimum-norm scaled path. One update consumes one memory
unit and one logical supplied-batch operation unit, matching `B = 1`. -/
noncomputable def identityMinimumNormScaledBatchCEPath :
    ℕ → TrainState 2 0 0 0 0 :=
  scaledBiasBinaryPath
    (minimumNormBatchParetoProblem (n := 2) (a := 0) (r := 0) (c := 0) (k := 0)
      minimumNormIdentityFeatures minimumNormIdentityLabels (1 / 2) (1 / 4) none)
    minimumNormIdentityScaledThreshold 1 1
    (minimumNormBatchPareto_stay_feasible minimumNormIdentityFeatures
      minimumNormIdentityLabels (1 / 2) (1 / 4) none 1 1) identityInitialState

/-- The first threshold upgrade executes the actual accepted current-state
minimum-norm update. It is neither the old mean candidate nor a field-only
identity operation. -/
theorem identityMinimumNormScaledBatchCEPath_one :
    identityMinimumNormScaledBatchCEPath 1 = identityMinimumNormBatchStep := by
  let p : ControllerProblem (Fin 2) (TrainState 2 0 0 0 0) :=
    minimumNormBatchParetoProblem minimumNormIdentityFeatures
      minimumNormIdentityLabels (1 / 2) (1 / 4) none
  let h0 : (0 : Fin 2) ∈ feasible p 1 1 := by
    dsimp only [p]
    exact minimumNormBatchPareto_stay_feasible minimumNormIdentityFeatures
      minimumNormIdentityLabels (1 / 2) (1 / 4) none 1 1
  have h1 : (1 : Fin 2) ∈ feasible p 1 1 := by
    dsimp only [p]
    exact (minimumNormBatchPareto_one_feasible_iff _ _ _ _ _ _ _).mpr (by norm_num)
  have hstep : p.step (1 : Fin 2) identityInitialState =
      identityMinimumNormBatchStep := by
    change batchMinimumNormTrainStep minimumNormIdentityFeatures
      minimumNormIdentityLabels identityInitialState (1 / 2) (1 / 4) none =
        identityMinimumNormBatchStep
    rfl
  have hstay : ∀ S : TrainState 2 0 0 0 0, p.step (0 : Fin 2) S = S := by
    intro S
    dsimp only [p]
    exact minimumNormBatchParetoProblem_step_zero _ _ _ _ _ _
  have hdrop : minimumNormIdentityScaledThreshold ≤
      minimumNormIdentityInitialMeanDrop := by
    rw [minimumNormIdentityScaledThreshold]
    linarith only [minimumNormIdentityInitialMeanDrop_pos]
  change minimumNormIdentityScaledThreshold ≤
    batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
        identityInitialState -
      batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
        identityMinimumNormBatchStep at hdrop
  have hup : estimatedUpgrade p
      (scaledBiasBinaryValueEstimate p minimumNormIdentityScaledThreshold)
      (minimumNormIdentityScaledThreshold / 2)
      (scaledBiasBinaryPath p minimumNormIdentityScaledThreshold 1 1 h0
        identityInitialState 0) 1 1 0 := by
    refine ⟨1, h1, ?_⟩
    change (-batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
        (p.step 0 (scaledBiasBinaryPath p minimumNormIdentityScaledThreshold 1 1 h0
          identityInitialState 0)) - minimumNormIdentityScaledThreshold / 2) +
        2 * (minimumNormIdentityScaledThreshold / 2) ≤
      -batchCEObjective minimumNormIdentityFeatures minimumNormIdentityLabels
        (p.step 1 (scaledBiasBinaryPath p minimumNormIdentityScaledThreshold 1 1 h0
          identityInitialState 0)) - minimumNormIdentityScaledThreshold / 2
    rw [scaledBiasBinaryPath_zero, hstay, hstep]
    linarith only [hdrop]
  have hnext := scaledBiasBinaryPath_succ_eq_step_one_of_upgrade p
    minimumNormIdentityScaledThreshold minimumNormIdentityScaledThreshold_pos
    1 1 h0 identityInitialState hstay 0 hup
  rw [scaledBiasBinaryPath_zero] at hnext
  unfold identityMinimumNormScaledBatchCEPath
  exact hnext.trans hstep

end Hagi.Contracts.BatchCETrajectory

namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- All direct current-state guarded inputs share the same actual recursive
path. Selection of an input remains separate from the existing guard. -/
noncomputable def guardedBatchInputPath (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) : ℕ → TrainState n a r c k
  | 0 => S
  | t + 1 => guardedBatchTrainStep X y inputFor
      (guardedBatchInputPath X y inputFor S t)

@[simp] theorem guardedBatchInputPath_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) : guardedBatchInputPath X y inputFor S 0 = S := rfl

@[simp] theorem guardedBatchInputPath_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (t : ℕ) :
    guardedBatchInputPath X y inputFor S (t + 1) =
      guardedBatchTrainStep X y inputFor (guardedBatchInputPath X y inputFor S t) := rfl

theorem guardedBatchInputPath_sampleCE_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    Antitone (fun t => batchSampleCE X y b (guardedBatchInputPath X y inputFor S t)) := by
  apply antitone_nat_of_succ_le
  intro t
  exact batchSampleCE_guardedBatchTrainStep_le X y inputFor
    (guardedBatchInputPath X y inputFor S t) b

theorem guardedBatchInputPath_objective_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    Antitone (fun t => batchCEObjective X y (guardedBatchInputPath X y inputFor S t)) := by
  apply antitone_nat_of_succ_le
  intro t
  exact batchCEObjective_guardedBatchTrainStep_le X y inputFor
    (guardedBatchInputPath X y inputFor S t)

theorem guardedBatchInputPath_sampleCE_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    Tendsto (fun t => batchSampleCE X y b (guardedBatchInputPath X y inputFor S t))
      atTop (𝓝 (⨅ t, batchSampleCE X y b
        (guardedBatchInputPath X y inputFor S t))) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (guardedBatchInputPath_sampleCE_antitone X y inputFor S b)
      (fun t => batchSampleCE_nonneg X y b (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_objective_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    Tendsto (fun t => batchCEObjective X y (guardedBatchInputPath X y inputFor S t))
      atTop (𝓝 (⨅ t, batchCEObjective X y (guardedBatchInputPath X y inputFor S t))) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (guardedBatchInputPath_objective_antitone X y inputFor S)
      (fun t => batchCEObjective_nonneg X y (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_sampleCE_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (b : Fin B) :
    0 ≤ ⨅ t, batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) :=
  ObjectiveTrajectory.ciInf_nonneg _
    (fun t => batchSampleCE_nonneg X y b (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_objective_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) :
    0 ≤ ⨅ t, batchCEObjective X y (guardedBatchInputPath X y inputFor S t) :=
  ObjectiveTrajectory.ciInf_nonneg _
    (fun t => batchCEObjective_nonneg X y (guardedBatchInputPath X y inputFor S t))

theorem guardedBatchInputPath_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k) (hbudget : 0 ≤ S.res.budget) :
    ∀ t, 0 ≤ (guardedBatchInputPath X y inputFor S t).res.budget := by
  intro t
  induction t with
  | zero => exact hbudget
  | succ t ih => exact guardedBatchTrainStep_budget_nonneg X y inputFor _ ih

/-- A single local actual-margin law produces all finite/infinite sample CE
margin budgets for every direct guarded-input policy. -/
theorem guardedBatchInputPath_margin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k)
    (margin : Fin B → TrainState n a r c k → ℝ)
    (hmargin : ∀ b (T : TrainState n a r c k), 0 ≤ margin b T)
    (hbound : ∀ (T : TrainState n a r c k),
      0 ≤ (inputFor T).opCost ∧ (inputFor T).opCost ≤ T.res.budget →
        ∀ b, batchSampleCE X y b (guardedBatchTrainStep X y inputFor T) ≤
          batchSampleCE X y b T - margin b T)
    (hcost : ∀ t, 0 ≤ (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ∧
      (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ≤
        (guardedBatchInputPath X y inputFor S t).res.budget)
    (b : Fin B) :
    (∀ T, ∑ t ∈ Finset.range T,
        margin b (guardedBatchInputPath X y inputFor S t) ≤ batchSampleCE X y b S) ∧
      Summable (fun t => margin b (guardedBatchInputPath X y inputFor S t)) ∧
      Tendsto (fun t => margin b (guardedBatchInputPath X y inputFor S t)) atTop (𝓝 0) ∧
      ∑' t, margin b (guardedBatchInputPath X y inputFor S t) ≤ batchSampleCE X y b S := by
  have hle (t : ℕ) : margin b (guardedBatchInputPath X y inputFor S t) ≤
      batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) -
        batchSampleCE X y b (guardedBatchInputPath X y inputFor S (t + 1)) := by
    have h := hbound (guardedBatchInputPath X y inputFor S t) (hcost t) b
    rw [guardedBatchInputPath_succ]
    linarith
  have hfinite (T : ℕ) : ∑ t ∈ Finset.range T,
      margin b (guardedBatchInputPath X y inputFor S t) ≤ batchSampleCE X y b S := by
    calc
      ∑ t ∈ Finset.range T, margin b (guardedBatchInputPath X y inputFor S t) ≤
        batchSampleCE X y b (guardedBatchInputPath X y inputFor S 0) -
          batchSampleCE X y b (guardedBatchInputPath X y inputFor S T) :=
        ObjectiveTrajectory.sum_drop_le_initial_sub _ _ T (fun t => hle t)
      _ ≤ batchSampleCE X y b (guardedBatchInputPath X y inputFor S 0) :=
        sub_le_self _ (batchSampleCE_nonneg X y b (guardedBatchInputPath X y inputFor S T))
      _ = batchSampleCE X y b S := rfl
  have hsummable : Summable
      (fun t => margin b (guardedBatchInputPath X y inputFor S t)) :=
    summable_of_sum_range_le (fun t => hmargin b _) hfinite
  exact ⟨hfinite, hsummable, hsummable.tendsto_atTop_zero,
    hsummable.tsum_le_of_sum_range_le hfinite⟩

/-- The averaged counterpart of a generic local sample-margin law.  The
only batch denominator is on the averaged current margin. -/
theorem guardedBatchInputPath_meanMargin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (inputFor : TrainState n a r c k → TrainingInput n c)
    (S : TrainState n a r c k)
    (margin : Fin B → TrainState n a r c k → ℝ)
    (hmargin : ∀ b (T : TrainState n a r c k), 0 ≤ margin b T)
    (hbound : ∀ (T : TrainState n a r c k),
      0 ≤ (inputFor T).opCost ∧ (inputFor T).opCost ≤ T.res.budget →
        ∀ b, batchSampleCE X y b (guardedBatchTrainStep X y inputFor T) ≤
          batchSampleCE X y b T - margin b T)
    (hcost : ∀ t, 0 ≤ (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ∧
      (inputFor (guardedBatchInputPath X y inputFor S t)).opCost ≤
        (guardedBatchInputPath X y inputFor S t).res.budget) :
    (∀ T, ∑ t ∈ Finset.range T,
        ((∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ≤
          batchCEObjective X y S) ∧
      Summable (fun t => (∑ b,
        margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ∧
      Tendsto (fun t => (∑ b,
        margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ))
        atTop (𝓝 0) ∧
      ∑' t, (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) ≤
        batchCEObjective X y S := by
  have hsucc (t : ℕ) : batchCEObjective X y
        (guardedBatchInputPath X y inputFor S (t + 1)) ≤
      batchCEObjective X y (guardedBatchInputPath X y inputFor S t) -
        (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) := by
    have hsum : (∑ b, batchSampleCE X y b
          (guardedBatchInputPath X y inputFor S (t + 1))) ≤
        ∑ b, (batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) -
          margin b (guardedBatchInputPath X y inputFor S t)) := by
      exact Finset.sum_le_sum (fun b _hb => by
        simpa only [guardedBatchInputPath_succ] using
          hbound (guardedBatchInputPath X y inputFor S t) (hcost t) b)
    have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg B)
    unfold batchCEObjective batchLoss
    unfold Hagi.Probability.FiniteFamilyConfidence.empiricalMean
    calc
      (∑ b, batchSampleCE X y b (guardedBatchInputPath X y inputFor S (t + 1))) /
          (B : ℝ) ≤
        (∑ b, (batchSampleCE X y b (guardedBatchInputPath X y inputFor S t) -
          margin b (guardedBatchInputPath X y inputFor S t))) / (B : ℝ) := hdiv
      _ = (∑ b, batchSampleCE X y b (guardedBatchInputPath X y inputFor S t)) /
          (B : ℝ) -
        (∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) := by
        rw [Finset.sum_sub_distrib, sub_div]
  have hle (t : ℕ) : (∑ b,
        margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ) ≤
      batchCEObjective X y (guardedBatchInputPath X y inputFor S t) -
        batchCEObjective X y (guardedBatchInputPath X y inputFor S (t + 1)) := by
    have h := hsucc t
    linarith [hsucc t]
  have hfinite (T : ℕ) : ∑ t ∈ Finset.range T,
      ((∑ b, margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ≤
        batchCEObjective X y S := by
    calc
      ∑ t ∈ Finset.range T, ((∑ b,
          margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) ≤
        batchCEObjective X y (guardedBatchInputPath X y inputFor S 0) -
          batchCEObjective X y (guardedBatchInputPath X y inputFor S T) :=
        ObjectiveTrajectory.sum_drop_le_initial_sub _ _ T (fun t => hle t)
      _ ≤ batchCEObjective X y (guardedBatchInputPath X y inputFor S 0) :=
        sub_le_self _ (batchCEObjective_nonneg X y (guardedBatchInputPath X y inputFor S T))
      _ = batchCEObjective X y S := rfl
  have hsummable : Summable (fun t => (∑ b,
      margin b (guardedBatchInputPath X y inputFor S t)) / (B : ℝ)) :=
    summable_of_sum_range_le (fun t => div_nonneg
      (Finset.sum_nonneg (fun b _hb => hmargin b _)) (Nat.cast_nonneg B)) hfinite
  exact ⟨hfinite, hsummable, hsummable.tendsto_atTop_zero,
    hsummable.tsum_le_of_sum_range_le hfinite⟩

noncomputable def directionBatchState (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : ℕ → TrainState n a r c k :=
  guardedBatchInputPath X y
    (fun S => batchDirectionTrainInput X y D S opCost opRisk write) S

@[simp] theorem directionBatchState_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    directionBatchState X y D S opCost opRisk write 0 = S := rfl

@[simp] theorem directionBatchState_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    directionBatchState X y D S opCost opRisk write (t + 1) =
      batchDirectionTrainStep X y D
        (directionBatchState X y D S opCost opRisk write t) opCost opRisk write := rfl

/-- Actual sample CE and its current local guaranteed margin along the path. -/
noncomputable def directionBatchSampleCE (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) : ℝ :=
  batchSampleCE X y b (directionBatchState X y D S opCost opRisk write t)

noncomputable def directionBatchMargin (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) : ℝ :=
  batchDirectionMargin X
    (coreParameters (directionBatchState X y D S opCost opRisk write t)) y
      (D (directionBatchState X y D S opCost opRisk write t)) b

noncomputable def directionBatchObjective (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  batchCEObjective X y (directionBatchState X y D S opCost opRisk write t)

noncomputable def directionBatchMeanMargin (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  (∑ b, directionBatchMargin X y D S opCost opRisk write b t) / (B : ℝ)

theorem directionBatchMargin_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) :
    0 ≤ directionBatchMargin X y D S opCost opRisk write b t :=
  batchDirectionMargin_nonneg _ _ _ _ _

theorem directionBatchSampleCE_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) :
    0 ≤ directionBatchSampleCE X y D S opCost opRisk write b t :=
  batchSampleCE_nonneg _ _ _ _

theorem directionBatchObjective_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    0 ≤ directionBatchObjective X y D S opCost opRisk write t :=
  batchCEObjective_nonneg _ _ _

theorem directionBatchMeanMargin_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    0 ≤ directionBatchMeanMargin X y D S opCost opRisk write t :=
  div_nonneg (Finset.sum_nonneg fun b _hb =>
    directionBatchMargin_nonneg X y D S opCost opRisk write b t)
      (Nat.cast_nonneg B)

theorem directionBatchSampleCE_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) :
    directionBatchSampleCE X y D S opCost opRisk write b (t + 1) ≤
      directionBatchSampleCE X y D S opCost opRisk write b t := by
  exact batchSampleCE_batchDirectionTrainStep_le X y D
    (directionBatchState X y D S opCost opRisk write t) opCost opRisk write b

theorem directionBatchObjective_succ_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    directionBatchObjective X y D S opCost opRisk write (t + 1) ≤
      directionBatchObjective X y D S opCost opRisk write t := by
  exact batchCEObjective_batchDirectionTrainStep_le X y D
    (directionBatchState X y D S opCost opRisk write t) opCost opRisk write

theorem directionBatchSampleCE_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    Antitone (directionBatchSampleCE X y D S opCost opRisk write b) :=
  antitone_nat_of_succ_le (directionBatchSampleCE_succ_le
    X y D S opCost opRisk write b)

theorem directionBatchObjective_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Antitone (directionBatchObjective X y D S opCost opRisk write) :=
  antitone_nat_of_succ_le (directionBatchObjective_succ_le
    X y D S opCost opRisk write)

theorem directionBatchSampleCE_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    Tendsto (directionBatchSampleCE X y D S opCost opRisk write b) atTop
      (𝓝 (⨅ t, directionBatchSampleCE X y D S opCost opRisk write b t)) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (directionBatchSampleCE_antitone X y D S opCost opRisk write b)
    (directionBatchSampleCE_nonneg X y D S opCost opRisk write b)

theorem directionBatchObjective_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (directionBatchObjective X y D S opCost opRisk write) atTop
      (𝓝 (⨅ t, directionBatchObjective X y D S opCost opRisk write t)) :=
  ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (directionBatchObjective_antitone X y D S opCost opRisk write)
    (directionBatchObjective_nonneg X y D S opCost opRisk write)

theorem directionBatchSampleCE_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    0 ≤ ⨅ t, directionBatchSampleCE X y D S opCost opRisk write b t :=
  ObjectiveTrajectory.ciInf_nonneg _
    (directionBatchSampleCE_nonneg X y D S opCost opRisk write b)

theorem directionBatchObjective_ciInf_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    0 ≤ ⨅ t, directionBatchObjective X y D S opCost opRisk write t :=
  ObjectiveTrajectory.ciInf_nonneg _
    (directionBatchObjective_nonneg X y D S opCost opRisk write)

theorem directionBatchState_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hbudget : 0 ≤ S.res.budget) :
    ∀ t, 0 ≤ (directionBatchState X y D S opCost opRisk write t).res.budget := by
  intro t
  induction t with
  | zero => exact hbudget
  | succ t ih =>
      exact batchDirectionTrainStep_budget_nonneg X y D
        (directionBatchState X y D S opCost opRisk write t)
          opCost opRisk write ih

theorem directionBatchSampleCE_succ_le_margin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) (t : ℕ) :
    directionBatchSampleCE X y D S opCost opRisk write b (t + 1) ≤
      directionBatchSampleCE X y D S opCost opRisk write b t -
        directionBatchMargin X y D S opCost opRisk write b t := by
  exact batchSampleCE_batchDirectionTrainStep_le_margin X y D
    (directionBatchState X y D S opCost opRisk write t) opCost opRisk write
      (hcost t) b

theorem directionBatchObjective_succ_le_margin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (t : ℕ) :
    directionBatchObjective X y D S opCost opRisk write (t + 1) ≤
      directionBatchObjective X y D S opCost opRisk write t -
        directionBatchMeanMargin X y D S opCost opRisk write t := by
  exact batchCEObjective_batchDirectionTrainStep_le_margin_sum X y D
    (directionBatchState X y D S opCost opRisk write t) opCost opRisk write
      (hcost t)

theorem directionBatchMargin_sum_le_initial
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) (T : ℕ) :
    ∑ t ∈ Finset.range T, directionBatchMargin X y D S opCost opRisk write b t ≤
      batchSampleCE X y b S := by
  apply (guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost b).1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMeanMargin_sum_le_initial
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, directionBatchMeanMargin X y D S opCost opRisk write t ≤
      batchCEObjective X y S := by
  apply (guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost).1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMargin_summable
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) :
    Summable (directionBatchMargin X y D S opCost opRisk write b) := by
  apply (guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost b).2.1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMeanMargin_summable
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget) :
    Summable (directionBatchMeanMargin X y D S opCost opRisk write) := by
  apply (guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost).2.1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMargin_tendsto_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) :
    Tendsto (directionBatchMargin X y D S opCost opRisk write b) atTop (𝓝 0) := by
  apply (guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost b).2.2.1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMeanMargin_tendsto_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget) :
    Tendsto (directionBatchMeanMargin X y D S opCost opRisk write) atTop (𝓝 0) := by
  apply (guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost).2.2.1
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMargin_tsum_le_initial
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) :
    ∑' t, directionBatchMargin X y D S opCost opRisk write b t ≤ batchSampleCE X y b S := by
  apply (guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost b).2.2.2
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

theorem directionBatchMeanMargin_tsum_le_initial
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchState X y D S opCost opRisk write t).res.budget) :
    ∑' t, directionBatchMeanMargin X y D S opCost opRisk write t ≤ batchCEObjective X y S := by
  apply (guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionTrainInput X y D T opCost opRisk write)
    S _ (fun b T => batchDirectionMargin_nonneg X (coreParameters T) y (D T) b)
    ?_ hcost).2.2.2
  intro T hT
  simpa only [batchDirectionTrainStep] using
    batchSampleCE_batchDirectionTrainStep_le_margin
      X y D T opCost opRisk write hT

end Hagi.Contracts.BatchCETrajectory

namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- The stronger half-window policy is the same generic actual guarded path. -/
noncomputable def directionBatchHalfState (X : Fin B → Matrix V (Fin n) ℝ)
    (y : Fin B → V) (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : ℕ → TrainState n a r c k :=
  guardedBatchInputPath X y
    (fun S => batchDirectionHalfTrainInput X y D S opCost opRisk write) S

@[simp] theorem directionBatchHalfState_zero
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    directionBatchHalfState X y D S opCost opRisk write 0 = S := rfl

@[simp] theorem directionBatchHalfState_succ
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) :
    directionBatchHalfState X y D S opCost opRisk write (t + 1) =
      batchDirectionHalfTrainStep X y D
        (directionBatchHalfState X y D S opCost opRisk write t)
          opCost opRisk write := rfl

/-- Each full quadratic margin evaluated at the actual current half-path
state, direction and backbone parameters. -/
noncomputable def directionBatchHalfQuadraticMargin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) : ℝ :=
  batchDirectionQuadraticMargin X
    (coreParameters (directionBatchHalfState X y D S opCost opRisk write t))
    y (D (directionBatchHalfState X y D S opCost opRisk write t))
    (batchDirectionHalfEta X
      (coreParameters (directionBatchHalfState X y D S opCost opRisk write t))
      y (D (directionBatchHalfState X y D S opCost opRisk write t))) b

/-- One arithmetic mean of those current quadratic margins. -/
noncomputable def directionBatchHalfMeanQuadraticMargin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (t : ℕ) : ℝ :=
  (∑ b, directionBatchHalfQuadraticMargin
    X y D S opCost opRisk write b t) / (B : ℝ)

theorem directionBatchHalfQuadraticMargin_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) (t : ℕ) :
    0 ≤ directionBatchHalfQuadraticMargin X y D S opCost opRisk write b t :=
  (batchDirectionHalfMargin_nonneg _ _ _ _ _).trans
    (batchDirectionHalfMargin_le_quadraticMargin _ _ _ _ _)

/-- Actual legal half-window execution supplies exactly the local law expected
by the generic sample-margin budget. No positivity/certified-budget is added. -/
theorem directionBatchHalfQuadraticMargin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y D S opCost opRisk write t).res.budget)
    (b : Fin B) :
    (∀ T, ∑ t ∈ Finset.range T,
        directionBatchHalfQuadraticMargin X y D S opCost opRisk write b t ≤
          batchSampleCE X y b S) ∧
      Summable (directionBatchHalfQuadraticMargin X y D S opCost opRisk write b) ∧
      Tendsto (directionBatchHalfQuadraticMargin
        X y D S opCost opRisk write b) atTop (𝓝 0) ∧
      ∑' t, directionBatchHalfQuadraticMargin X y D S opCost opRisk write b t ≤
        batchSampleCE X y b S := by
  apply guardedBatchInputPath_margin_budget X y
    (fun T => batchDirectionHalfTrainInput X y D T opCost opRisk write)
    S _ (fun b T => (batchDirectionHalfMargin_nonneg
      X (coreParameters T) y (D T) b).trans
        (batchDirectionHalfMargin_le_quadraticMargin
          X (coreParameters T) y (D T) b)) ?_ hcost b
  intro T hT
  simpa only [batchDirectionHalfTrainStep] using
    batchSampleCE_batchDirectionHalfTrainStep_le_quadraticMargin
      X y D T opCost opRisk write hT

theorem directionBatchHalfMeanQuadraticMargin_budget
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y D S opCost opRisk write t).res.budget) :
    (∀ T, ∑ t ∈ Finset.range T,
        directionBatchHalfMeanQuadraticMargin X y D S opCost opRisk write t ≤
          batchCEObjective X y S) ∧
      Summable (directionBatchHalfMeanQuadraticMargin X y D S opCost opRisk write) ∧
      Tendsto (directionBatchHalfMeanQuadraticMargin
        X y D S opCost opRisk write) atTop (𝓝 0) ∧
      ∑' t, directionBatchHalfMeanQuadraticMargin
        X y D S opCost opRisk write t ≤ batchCEObjective X y S := by
  apply guardedBatchInputPath_meanMargin_budget X y
    (fun T => batchDirectionHalfTrainInput X y D T opCost opRisk write)
    S _ (fun b T => (batchDirectionHalfMargin_nonneg
      X (coreParameters T) y (D T) b).trans
        (batchDirectionHalfMargin_le_quadraticMargin
          X (coreParameters T) y (D T) b)) ?_ hcost
  intro T hT
  simpa only [batchDirectionHalfTrainStep] using
    batchSampleCE_batchDirectionHalfTrainStep_le_quadraticMargin
      X y D T opCost opRisk write hT

theorem directionBatchHalfSampleCE_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    Antitone (fun t => batchSampleCE X y b
      (directionBatchHalfState X y D S opCost opRisk write t)) :=
  guardedBatchInputPath_sampleCE_antitone X y
    (fun T => batchDirectionHalfTrainInput X y D T opCost opRisk write) S b

theorem directionBatchHalfObjective_antitone
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Antitone (fun t => batchCEObjective X y
      (directionBatchHalfState X y D S opCost opRisk write t)) :=
  guardedBatchInputPath_objective_antitone X y
    (fun T => batchDirectionHalfTrainInput X y D T opCost opRisk write) S

theorem directionBatchHalfSampleCE_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    Tendsto (fun t => batchSampleCE X y b
      (directionBatchHalfState X y D S opCost opRisk write t)) atTop
        (𝓝 (⨅ t, batchSampleCE X y b
          (directionBatchHalfState X y D S opCost opRisk write t))) :=
  guardedBatchInputPath_sampleCE_tendsto_ciInf X y
    (fun T => batchDirectionHalfTrainInput X y D T opCost opRisk write) S b

theorem directionBatchHalfObjective_tendsto_ciInf
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (D : TrainState n a r c k → EuclideanSpace ℝ (Fin n))
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    Tendsto (fun t => batchCEObjective X y
      (directionBatchHalfState X y D S opCost opRisk write t)) atTop
        (𝓝 (⨅ t, batchCEObjective X y
          (directionBatchHalfState X y D S opCost opRisk write t))) :=
  guardedBatchInputPath_objective_tendsto_ciInf X y
    (fun T => batchDirectionHalfTrainInput X y D T opCost opRisk write) S

end Hagi.Contracts.BatchCETrajectory
