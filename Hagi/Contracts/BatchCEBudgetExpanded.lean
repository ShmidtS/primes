import Hagi.Contracts.CEStepCertificate
import Hagi.Model.BatchCEDescent
import Hagi.Model.CEExpansion
import Hagi.Model.CEHeldout
import Hagi.Unified.ParetoExecution
import Hagi.Contracts.BatchCEBudgetAsym

/-!
# BatchCEBudgetExpanded

Expanded-state half-step descent and the computed five-task batch evaluation through the actual MGDA step. Split from `BatchCEStepCertificate` (C255).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.BudgetedBatchCE

open Hagi.State Hagi.Model Hagi.Model.BatchCEDescent Hagi.Contracts.CEStep
open Hagi.Contracts.BatchCEStep Hagi.Model.CEExpansion

variable {V : Type} [Fintype V]
variable {B n a r c k : ℕ}

/-- One new backbone coordinate and two new optimizer moments are the
incremental persistent state coefficients, not a byte or RAM measurement. -/
def expandedStateCoefficients : ℕ := 3

/-- Construct the genuinely one-coordinate-wider state.  All dependent-width
fields are freshly constructed; independent state and old prefixes are kept. -/
noncomputable def expandedTrainState {n a r c k : ℕ}
    (S : TrainState n a r c k) : TrainState (n + 1) a r c k where
  model := {
    weights := (expandedParameters (coreParameters S) 0).ofLp
    adapters := S.model.adapters
    version := S.model.version + 1 }
  opt := {
    m := Fin.snoc S.opt.m 0
    v := Fin.snoc S.opt.v 0
    schedStep := S.opt.schedStep }
  mem := S.mem
  res := S.res
  saf := S.saf
  qual := S.qual

/-- The actual expanded state has zero in the new readout coordinate. -/
theorem coreParameters_expandedTrainState {n a r c k : ℕ}
    (S : TrainState n a r c k) :
    coreParameters (expandedTrainState S) =
      expandedParameters (coreParameters S) 0 := rfl

/-- Entry into the widened state preserves each supplied sample's actual CE,
even when the appended latent feature is nonzero. -/
theorem batchSampleCE_expandedTrainState
    (X : Fin B → Matrix V (Fin n) ℝ) (Z : Fin B → V → ℝ)
    (y : Fin B → V) (S : TrainState n a r c k) (b : Fin B) :
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
      (expandedTrainState S) = batchSampleCE X y b S := by
  change Hagi.ceOneHot (y b) (ceLogits (expandedFeatures (X b) (Z b))
    (coreParameters (expandedTrainState S))) =
    Hagi.ceOneHot (y b) (ceLogits (X b) (coreParameters S))
  rw [coreParameters_expandedTrainState]
  exact ceOneHot_expandedParameters_zero (X b) (coreParameters S) (Z b) (y b)

/-- Construct one wider zero-initialized state, then run the existing guarded
half-window training step at a supplied direction in the enlarged space. -/
noncomputable def expandedHalfTrainStep
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState (n + 1) a r c k :=
  batchDirectionHalfTrainStep (fun b => expandedFeatures (X b) (Z b)) y
    (fun _ => D) (expandedTrainState S)
    (expandedFeatureEvaluationCount B V + trainingCost) opRisk write

/-- Growth into the zero-initialized wider state composes with ordinary guarded
training to give actual samplewise nonregression against the original model. -/
theorem batchSampleCE_expandedHalfTrainStep_le
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (b : Fin B) :
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) ≤
      batchSampleCE X y b S := by
  have h := batchSampleCE_batchDirectionHalfTrainStep_le
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write b
  calc
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) ≤
      batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedTrainState S) := by
        simpa only [expandedHalfTrainStep] using h
    _ = batchSampleCE X y b S :=
      batchSampleCE_expandedTrainState X Z y S b

/-- The legal enlarged half-step dominates the certified minimum quadratic
residual and transports its bound to the original model's CE. -/
theorem batchSampleCE_expandedHalfTrainStep_le_minQuadraticMargin
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) (y b) D < 0) (b : Fin B) :
  let _ : Nonempty (Fin B) := hcert.1
  batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) ≤
      batchSampleCE X y b S -
        batchDirectionMinQuadraticMargin
          (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D
          (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
            (coreParameters (expandedTrainState S)) y D) := by
  let _ : Nonempty (Fin B) := hcert.1
  have hcombined : 0 ≤ (expandedFeatureEvaluationCount B V : ℝ) + trainingCost :=
    add_nonneg (by positivity) hcost.1
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤
      (expandedTrainState S).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have hper := batchSampleCE_batchDirectionHalfTrainStep_le_quadraticMargin
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write ⟨hcombined, hbudget⟩ b
  have hmin :
      batchDirectionMinQuadraticMargin
        (fun b => expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) y D
        (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D) ≤
      batchDirectionQuadraticMargin
        (fun b => expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) y D
        (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D) b :=
    ciInf_le (Finite.bddBelow_range _) b
  calc
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) ≤
      batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedTrainState S) - _ := by
        simpa only [expandedHalfTrainStep] using hper
    _ ≤ batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedTrainState S) -
        batchDirectionMinQuadraticMargin
          (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D
          (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
            (coreParameters (expandedTrainState S)) y D) := by
      linarith [hmin]
    _ = batchSampleCE X y b S -
        batchDirectionMinQuadraticMargin
          (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D
          (batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
            (coreParameters (expandedTrainState S)) y D) := by
      rw [batchSampleCE_expandedTrainState X Z y S b]

/-- An affordable, fully certified enlarged step strictly improves every
sample's actual CE relative to the original narrow model. -/
theorem batchSampleCE_expandedHalfTrainStep_lt
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) (y b) D < 0) (b : Fin B) :
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) <
      batchSampleCE X y b S := by
  let _ : Nonempty (Fin B) := hcert.1
  have hcombined : 0 ≤ (expandedFeatureEvaluationCount B V : ℝ) + trainingCost :=
    add_nonneg (by positivity) hcost.1
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤
      (expandedTrainState S).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have hactive := batchDirectionHalfTrainStep_of_active
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write ⟨hcombined, hbudget⟩ hcert
  calc
    batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedHalfTrainStep X y Z D S trainingCost opRisk write) =
      Hagi.ceOneHot (y b) (ceLogits (expandedFeatures (X b) (Z b))
        (batchDirectionHalfNextParameters
          (fun b => expandedFeatures (X b) (Z b))
          (coreParameters (expandedTrainState S)) y D)) := by
      unfold batchSampleCE expandedHalfTrainStep
      rw [hactive, coreParameters_trainStep_batchDirectionHalfTrainInput]
    _ < batchSampleCE (fun b => expandedFeatures (X b) (Z b)) y b
        (expandedTrainState S) :=
      ceOneHot_batchDirectionHalfNextParameters_lt
        (fun b => expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) y D (hcert.2) b
    _ = batchSampleCE X y b S :=
      batchSampleCE_expandedTrainState X Z y S b

/-- The accepted step can actually learn the appended readout coordinate; its
last coefficient is the old zero plus the half-window times its direction. -/
theorem coreParameters_expandedHalfTrainStep_last
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) (y b) D < 0) :
    (coreParameters (expandedHalfTrainStep X y Z D S trainingCost opRisk write)).ofLp
        (Fin.last n) =
      batchDirectionHalfEta (fun b => expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) y D * D.ofLp (Fin.last n) := by
  have hcombined : 0 ≤ (expandedFeatureEvaluationCount B V : ℝ) + trainingCost :=
    add_nonneg (by positivity) hcost.1
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤
      (expandedTrainState S).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have hactive := batchDirectionHalfTrainStep_of_active
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write ⟨hcombined, hbudget⟩ hcert
  unfold expandedHalfTrainStep
  rw [hactive, coreParameters_trainStep_batchDirectionHalfTrainInput]
  simp [batchDirectionHalfNextParameters, alongNext]
  change (Fin.snoc (α := fun _ : Fin (n + 1) => ℝ)
    (coreParameters S).ofLp 0) (Fin.last n) = 0
  simp

/-- An affordable combined operation-cell cost leaves nonnegative budget
after expansion and the guarded training step, including fallback branches. -/
theorem expandedHalfTrainStep_budget_nonneg
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget) :
    0 ≤ (expandedHalfTrainStep X y Z D S trainingCost opRisk write).res.budget := by
  have hbudget : 0 ≤ S.res.budget :=
    le_trans (add_nonneg (by positivity) hcost.1) hcost.2
  have h := batchDirectionHalfTrainStep_budget_nonneg
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write (by simpa only [expandedTrainState] using hbudget)
  simpa only [expandedHalfTrainStep] using h

/-- Under the complete certificate, accepted enlarged training has exact
declared cost accounting from the original state's accumulated flops. -/
theorem expandedHalfTrainStep_flops_of_active
    (X : Fin B → Matrix V (Fin n) ℝ) (y : Fin B → V)
    (Z : Fin B → V → ℝ) (D : EuclideanSpace ℝ (Fin (n + 1)))
    (S : TrainState n a r c k) (trainingCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ trainingCost ∧
      (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤ S.res.budget)
    (hcert : Nonempty (Fin B) ∧ ∀ b,
      dirAction (expandedFeatures (X b) (Z b))
        (coreParameters (expandedTrainState S)) (y b) D < 0) :
    (expandedHalfTrainStep X y Z D S trainingCost opRisk write).res.flops =
      S.res.flops + ((expandedFeatureEvaluationCount B V : ℝ) + trainingCost) := by
  have hcombined : 0 ≤ (expandedFeatureEvaluationCount B V : ℝ) + trainingCost :=
    add_nonneg (by positivity) hcost.1
  have hbudget : (expandedFeatureEvaluationCount B V : ℝ) + trainingCost ≤
      (expandedTrainState S).res.budget := by
    simpa only [expandedTrainState] using hcost.2
  have h := batchDirectionHalfTrainStep_flops_of_active
    (fun b => expandedFeatures (X b) (Z b)) y (fun _ => D)
    (expandedTrainState S) (expandedFeatureEvaluationCount B V + trainingCost)
    opRisk write ⟨hcombined, hbudget⟩ hcert
  simpa only [expandedHalfTrainStep, expandedTrainState] using h

/-! ## Computed five-task batch evaluation through the actual MGDA step

`batchCEMeasured` is a mathematical, parameter-computed evaluation of named
supervised tasks.  It does not read stored `TrainState.qual`, make those five
sample indices into external task categories, or assert fresh-data confidence.
The negative-CE orientation matches `FloorKept`: higher evaluation is better.
-/
open Hagi.Unified.HonestTransition Hagi.Unified.CertifiedLoop
  Hagi.Unified.LinkedQVec

/-- Actual per-task CE, negated for the higher-is-better quality-floor API. -/
noncomputable def batchCEMeasured (X : Fin 5 → Matrix V (Fin n) ℝ)
    (y : Fin 5 → V) : MeasuredState (TrainState n a r c k) where
  evaluate := fun S i => -batchSampleCE X y i S

/-- Any supplied-batch computed quality floor survives the existing guarded
minimum-norm transition, including a rejected update that returns `S`. -/
theorem floor_kept_batchMinimumNormTrainStep
    (X : Fin 5 → Matrix V (Fin n) ℝ) (y : Fin 5 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (floor : QualityVector)
    (hfloor : FloorKept (batchCEMeasured X y) S floor) :
    FloorKept (batchCEMeasured X y)
      (batchMinimumNormTrainStep X y S opCost opRisk write) floor := by
  intro i
  have hle := batchSampleCE_batchMinimumNormTrainStep_le
    X y S opCost opRisk write i
  exact (hfloor i).trans (neg_le_neg hle)

/-- Strict mean-CE descent on the admitted nonzero-minimizer MGDA successor,
using the exact old-minus-new objective gap rather than an assigned effect. -/
noncomputable def batchMinimumNormMinimalCert
    (X : Fin 5 → Matrix V (Fin n) ℝ) (y : Fin 5 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hω : batchGradientMinimizer X (coreParameters S) y ≠ 0) :
    CertStep (batchCEObjective X y) S
      (batchMinimumNormTrainStep X y S opCost opRisk write) where
  drop := batchCEObjective X y S -
    batchCEObjective X y (batchMinimumNormTrainStep X y S opCost opRisk write)
  drop_pos := sub_pos.mpr (batchCEObjective_batchMinimumNormTrainStep_lt
    X y S opCost opRisk write hcost hω)
  actual := by
    have hlt := batchCEObjective_batchMinimumNormTrainStep_lt
      X y S opCost opRisk write hcost hω
    linarith

/-- A full certificate for the actually executed nonzero-minimizer update:
strict supplied-batch mean-CE descent and preservation of all five computed
per-task evaluation floors.  Costs and risk are logical inputs, not runtime
measurements; this says nothing about external quality or generalization. -/
noncomputable def evaluatedBatchMinimumNormCert
    (X : Fin 5 → Matrix V (Fin n) ℝ) (y : Fin 5 → V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (floor : QualityVector) (riskLim : ℝ)
    (hcost : 0 ≤ opCost ∧ opCost ≤ S.res.budget)
    (hω : batchGradientMinimizer X (coreParameters S) y ≠ 0)
    (hrisk : 0 ≤ opRisk) (hriskLim : opRisk ≤ riskLim)
    (hfloor : FloorKept (batchCEMeasured X y) S floor) :
    StepCert (batchCEObjective X y) (batchCEMeasured X y) floor riskLim S
      (batchMinimumNormTrainStep X y S opCost opRisk write) S.res.budget
      (batchMinimumNormTrainStep X y S opCost opRisk write).res.budget where
  riskSpend := opRisk
  budgetSpend := opCost
  trans :=
    { objectiveDrop :=
        (batchMinimumNormMinimalCert X y S opCost opRisk write hcost hω).drop
      objectiveDrop_pos :=
        (batchMinimumNormMinimalCert X y S opCost opRisk write hcost hω).drop_pos
      actualDescent :=
        (batchMinimumNormMinimalCert X y S opCost opRisk write hcost hω).actual
      riskBound := hriskLim
      budgetBound := batchMinimumNormTrainStep_budget_nonneg
        X y S opCost opRisk write (le_trans hcost.1 hcost.2) }
  hriskSpend_nn := hrisk
  hbudgetSpend_nn := hcost.1
  hdec := by
    rw [batchMinimumNormTrainStep_of_active X y S opCost opRisk write hcost]
    exact le_of_eq (trainStep_budget S
      (batchMinimumNormTrainInput X y S opCost opRisk write))
  quality := floor_kept_batchMinimumNormTrainStep
    X y S opCost opRisk write floor hfloor

end Hagi.Contracts.BudgetedBatchCE
