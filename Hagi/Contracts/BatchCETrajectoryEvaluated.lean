import Hagi.Contracts.BatchCEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.CEHeldout
import Hagi.Unified.GuardedRobustTrajectory
import Hagi.Contracts.BatchCETrajectoryHalfMinNorm

/-!
# BatchCETrajectoryEvaluated

Evaluated finite MGDA trajectories: floor-kept two-step witness through the actual computed minimum-norm step. Split from `BatchCETrajectory` (C256).
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

This section uses the existing guarded path and C189 certificate: every input
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
  have hp : 0 < Hagi.Energy.smax
      (ceLogits (1 : Matrix (Fin 2) (Fin 2) ℝ) θ) 1 :=
    Hagi.Energy.smax_pos _ _
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
