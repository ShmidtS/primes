import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Unified.GuardedRobustTrajectory
import Hagi.Contracts.BatchCETrajectoryFixedBatch

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
