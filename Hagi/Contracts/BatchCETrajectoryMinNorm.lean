import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Unified.GuardedRobustTrajectory
import Hagi.Contracts.BatchCETrajectoryCanonical

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
