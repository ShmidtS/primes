import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Contracts.BatchCEBudgetGuard
import Hagi.Math.Foundations.Telescope
import Hagi.Unified.ParetoExecution
import Hagi.State.TrainState
import Hagi.State.Transition
import Hagi.Contracts.CEStepCertificate
import Hagi.Contracts.BatchCEStepCore
import Hagi.Model.BatchCEDescent

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

namespace Hagi.Contracts.BatchCETrajectory
end Hagi.Contracts.BatchCETrajectory

/-!
# BatchCETrajectoryGuarded

Generic scaled guarded batch CE trajectories: mean and per-sample non-regression, progress counts, budgets, and stabilization.
-/

set_option relaxedAutoImplicit false


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


end Hagi.Contracts.BatchCETrajectory

/-!
# BatchCETrajectoryCanonical

Canonical batch-controller guarded trajectory family `batchCEPath*`: non-regression, ledgers, and eventual constancy.
-/

set_option relaxedAutoImplicit false


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


end Hagi.Contracts.BatchCETrajectory

/-!
# BatchCETrajectoryMinNorm

Minimum-norm guarded trajectory family `minimumNormBatchCEPath*`.
-/

set_option relaxedAutoImplicit false


namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Hagi.Unified.ParetoExecution Hagi.Unified.FixedBiasBinaryProgress
open Hagi.Unified.GuardedRobustTrajectory Hagi.Unified.GuardedRobustSelection
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

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
alias minimumNormBatchCEProblem_value_le_zero :=
  Hagi.Contracts.BudgetedBatchCE.minimumNormBatchParetoProblem_value_nonpos

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


end Hagi.Contracts.BatchCETrajectory
