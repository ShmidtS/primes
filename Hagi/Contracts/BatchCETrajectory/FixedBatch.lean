import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Contracts.BatchCEBudgetGuard
import Hagi.Math.Foundations.Telescope
import Hagi.Unified.ParetoExecution
import Hagi.State.TrainState
import Hagi.State.Transition
import Hagi.Contracts.CEStepCertificate
import Hagi.Contracts.BatchCEStepCore
import Hagi.Contracts.BatchCETrajectory.Direction


/-!
# BatchCETrajectoryEvaluated

Evaluated finite MGDA trajectories: floor-kept two-step witness through the actual computed minimum-norm step.
-/

set_option relaxedAutoImplicit false


namespace Hagi.Contracts.BatchCETrajectory

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Contracts.BudgetedBatchCE
open Filter Topology

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}


/-- Every nonempty finite prefix of the actual path contains a point whose
minimum-norm squared norm is bounded by the corresponding finite average.
This is a best-index statement, not a claim about the last iterate. -/
theorem directionBatchMinNormSq_exists_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : ∀ t, 0 ≤ opCost ∧
      opCost ≤ (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t).res.budget)
    (T : ℕ) (hT : 0 < T) :
    ∃ t ∈ Finset.range T, ‖batchGradientMinimizer X
      (coreParameters (directionBatchHalfState X y
        (fun T => -batchGradientMinimizer X (coreParameters T) y)
        S opCost opRisk write t)) y‖ ^ 2 ≤
      ((B : ℝ) * batchFeatureRangeCoefficient X) * batchCEObjective X y S /
        (2 * (T : ℝ)) := by
  by_cases hB : B = 0
  · subst B
    refine ⟨0, Finset.mem_range.mpr hT, ?_⟩
    simp
  have hBpos : 0 < (B : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hB
  by_cases hC : batchFeatureRangeCoefficient X = 0
  · have hsq : ∀ t, ‖batchGradientMinimizer X
        (coreParameters (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t)) y‖ ^ 2 = 0 := by
      intro t
      have hzero : batchGradientMinimizer X
          (coreParameters (directionBatchHalfState X y
            (fun T => -batchGradientMinimizer X (coreParameters T) y)
            S opCost opRisk write t)) y = 0 := by
        by_contra hn
        have hp := batchFeatureRangeCoefficient_pos_of_minimizer_ne_zero X
          (coreParameters (directionBatchHalfState X y
            (fun T => -batchGradientMinimizer X (coreParameters T) y)
            S opCost opRisk write t)) y hn
        exact (ne_of_gt hp) hC
      simp [hzero]
    refine ⟨0, Finset.mem_range.mpr hT, ?_⟩
    rw [hsq 0]
    simp [hC]
  have hCpos := lt_of_le_of_ne
    (batchFeatureRangeCoefficient_nonneg X) (Ne.symm hC)
  have hκ : 0 < (B : ℝ) * batchFeatureRangeCoefficient X := mul_pos hBpos hCpos
  have hbudget : ∀ T, ∑ t ∈ Finset.range T,
      2 * ‖batchGradientMinimizer X
        (coreParameters (directionBatchHalfState X y
          (fun T => -batchGradientMinimizer X (coreParameters T) y)
          S opCost opRisk write t)) y‖ ^ 2 /
        ((B : ℝ) * batchFeatureRangeCoefficient X) ≤ batchCEObjective X y S := by
    simpa only [directionBatchMinNormSquaredBudget] using
      (directionBatchMinNormSquaredBudget_budget X y S
        opCost opRisk write hcost).1
  exact ObjectiveTrajectory.exists_le_of_sum_two_mul_div_le hκ hbudget hT

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

/-! ## Evaluated finite MGDA trajectories

This section uses the existing guarded path certificate: every input
is computed from the current successor, and quality is computed -CE rather
than stored telemetry.  A zero opCost in the recurring witness is only a
logical ledger choice, not a claim that MGDA is computationally free.
-/
open Hagi.Unified.HonestTransition Hagi.Unified.CertifiedLoop
  Hagi.Unified.LinkedQVec

/-- Every visited state on the current-state guarded minimum-norm path keeps
its computed five-task CE floors.  Feasibility and a nonzero minimizer at each
of the first `T` states also produce strict mean-CE descent when `T ≥ 1`. -/
theorem evaluatedBatchMinimumNormPath_floor_kept_and_objective_lt
    (X : Fin 5 → Matrix V (Fin n) ℝ) (y : Fin 5 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (floor : QualityVector) (riskLim : ℝ) (T : ℕ)
    (hcost : ∀ t : Fin T, 0 ≤ opCost ∧ opCost ≤
      (guardedBatchInputPath X y
        (fun S => batchMinimumNormTrainInput X y S opCost opRisk write)
        S t.val).res.budget)
    (hω : ∀ t : Fin T, batchGradientMinimizer X
      (coreParameters (guardedBatchInputPath X y
        (fun S => batchMinimumNormTrainInput X y S opCost opRisk write)
        S t.val)) y ≠ 0)
    (hrisk : 0 ≤ opRisk) (hriskLim : opRisk ≤ riskLim)
    (hfloor : FloorKept (batchCEMeasured X y) S floor)
    (hbudget : 0 ≤ S.res.budget) :
    (∀ t ≤ T, FloorKept (batchCEMeasured X y)
      (guardedBatchInputPath X y
        (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S t)
      floor) ∧
    (1 ≤ T → batchCEObjective X y
      (guardedBatchInputPath X y
        (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S T) <
      batchCEObjective X y S) := by
  let f : ℕ → TrainState n a r c k := guardedBatchInputPath X y
    (fun S => batchMinimumNormTrainInput X y S opCost opRisk write) S
  have hfloor_path : ∀ t, FloorKept (batchCEMeasured X y) (f t) floor := by
    intro t
    induction t with
    | zero => exact hfloor
    | succ t ih =>
        exact floor_kept_batchMinimumNormTrainStep
          X y (f t) opCost opRisk write floor ih
  let certs : ∀ t : Fin T,
      StepCert (batchCEObjective X y) (batchCEMeasured X y) floor riskLim
        (f t.val) (f (t.val + 1)) (f t.val).res.budget (f (t.val + 1)).res.budget :=
    fun t => evaluatedBatchMinimumNormCert X y (f t.val) opCost opRisk write
      floor riskLim (hcost t) (hω t) hrisk hriskLim (hfloor_path t.val)
  have hall := certified_loop_all (batchCEObjective X y) (batchCEMeasured X y)
    floor riskLim f (fun t => (f t).res.budget)
    (fun t => batchCEObjective X y (f t) - batchCEObjective X y (f (t + 1)))
    (fun _ => opCost) T hfloor hbudget certs (fun _ => rfl) (fun _ => rfl)
  refine ⟨hall, ?_⟩
  intro hT
  exact (certified_loop_strict (batchCEObjective X y) (batchCEMeasured X y)
    floor riskLim f (fun t => (f t).res.budget)
    (fun t => batchCEObjective X y (f t) - batchCEObjective X y (f (t + 1)))
    T hfloor hbudget certs (fun _ => rfl) hT).1

/-- Repeated identity features and zero targets have a nonzero minimizer at
every parameter: its sole residual gradient has positive sigmoid coordinate. -/
theorem batchGradientMinimizer_repeatedIdentity_ne_zero
    (θ : EuclideanSpace ℝ (Fin 2)) :
    batchGradientMinimizer
      (fun _ : Fin 5 => (1 : Matrix (Fin 2) (Fin 2) ℝ)) θ
      (fun _ : Fin 5 => (0 : Fin 2)) ≠ 0 := by
  have hmem := batchGradientMinimizer_mem
    (fun _ : Fin 5 => (1 : Matrix (Fin 2) (Fin 2) ℝ)) θ
    (fun _ : Fin 5 => (0 : Fin 2))
  have hrange : Set.range (fun b : Fin 5 =>
      batchResidualGradient (1 : Matrix (Fin 2) (Fin 2) ℝ) θ 0) =
      {batchResidualGradient (1 : Matrix (Fin 2) (Fin 2) ℝ) θ 0} := by
    apply Set.range_eq_singleton
    intro b
    rfl
  rw [hrange, convexHull_singleton] at hmem
  rw [hmem]
  intro h
  have hcoord := congrArg
    (fun z : EuclideanSpace ℝ (Fin 2) => z.ofLp 1) h
  have hp : 0 < Hagi.Prelude.softDef
      (ceLogits (1 : Matrix (Fin 2) (Fin 2) ℝ) θ) 1 :=
    Hagi.Prelude.softDef_pos _ _
  norm_num [batchResidualGradient_ofLp, residualTranspose, ceResidual,
    Fin.sum_univ_two, Matrix.one_apply] at hcoord
  linarith

/-- A genuine two-update existential instance of the evaluated finite path.
Logical zero opCost permits affordability from the existing ledger invariant;
it does not measure or claim free physical computation. -/
theorem evaluatedBatchMinimumNorm_twoStep_witness :
    ∃ (X : Fin 5 → Matrix (Fin 2) (Fin 2) ℝ) (y : Fin 5 → Fin 2)
      (floor : QualityVector),
      let f : ℕ → TrainState 2 0 0 0 0 := guardedBatchInputPath X y
        (fun S => batchMinimumNormTrainInput X y S 0 (1 / 4) none)
        identityInitialState
      f 0 = identityInitialState ∧
      (∀ t, f (t + 1) =
        batchMinimumNormTrainStep X y (f t) 0 (1 / 4) none) ∧
      batchCEObjective X y (f 2) < batchCEObjective X y (f 0) ∧
      ∀ t ≤ 2, FloorKept (batchCEMeasured X y) (f t) floor := by
  let X : Fin 5 → Matrix (Fin 2) (Fin 2) ℝ := fun _ => 1
  let y : Fin 5 → Fin 2 := fun _ => 0
  let floor : QualityVector := fun i => -batchSampleCE X y i identityInitialState
  let f : ℕ → TrainState 2 0 0 0 0 := guardedBatchInputPath X y
    (fun S => batchMinimumNormTrainInput X y S 0 (1 / 4) none)
    identityInitialState
  have hfloor : FloorKept (batchCEMeasured X y) identityInitialState floor := by
    intro i
    exact le_rfl
  have hbudget : 0 ≤ identityInitialState.res.budget := by
    norm_num [identityInitialState]
  have hbudget_path : ∀ t, 0 ≤ (f t).res.budget :=
    guardedBatchInputPath_budget_nonneg X y
      (fun S => batchMinimumNormTrainInput X y S 0 (1 / 4) none)
      identityInitialState hbudget
  have hcost : ∀ t : Fin 2, 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (f t.val).res.budget :=
    fun t => ⟨le_rfl, hbudget_path t.val⟩
  have main := evaluatedBatchMinimumNormPath_floor_kept_and_objective_lt X y
    identityInitialState 0 (1 / 4) none floor (1 / 2) 2 hcost
    (fun t => batchGradientMinimizer_repeatedIdentity_ne_zero
      (coreParameters (f t.val))) (by norm_num) (by norm_num)
    hfloor hbudget
  refine ⟨X, y, floor, ?_⟩
  exact ⟨rfl, fun _ => rfl, main.2 (by norm_num), main.1⟩
end Hagi.Contracts.BatchCETrajectory

/-!
# BatchCETrajectoryFixedBatch

Repeated common-direction batch CE transitions on one fixed finite batch, with telemetered loss, antitonicity, and convergence to the real infimum.
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
  have h0 : fixedBatchObjective X y S opCost opRisk write 0
      = batchCEObjective X y S := rfl
  rw [Hagi.Contracts.ObjectiveTrajectory.sum_range_drop_eq, h0]

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
# BatchCETrajectoryFixtures

Concrete identity and sameZero fixtures with computed positive initial drops.
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
