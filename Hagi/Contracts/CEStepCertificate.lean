import Hagi.Contracts.StepCertificate
import Hagi.Model.CEDescent
import Hagi.Probability.FiniteFamilyConfidence

/-!
# Categorical-CE execution through the canonical training transition

This additive bridge executes the existing `State.trainStep` on the exact
residual-transpose gradient and safe step from `Model.CEDescent`.  Its
objective is the actual categorical cross-entropy of the state's backbone
weights; its descent certificate is the existing strict safe-step theorem.
The supplied cost, risk, and optional write retain their original semantics.
They are logical inputs, not physical measurements made by this module.
No claim is made that categorical CE equals the external quality telemetry.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.CEStep

open Hagi.State Hagi.Model
open Hagi.Unified.HonestTransition Hagi.Unified.CertifiedLoop

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- The state's actual backbone weights on the Euclidean CE carrier. -/
noncomputable def coreParameters (S : TrainState n a r c k) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 S.model.weights

/-- Categorical CE of the actual backbone weights, with target before state. -/
noncomputable def coreCEObjective (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) : ℝ :=
  Hagi.ceOneHot t (ceLogits X (coreParameters S))

/-- The ordinary training input computed from the current CE parameters.
`opCost`, `opRisk`, and `write` are supplied externally to the transition. -/
noncomputable def ceTrainInput (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainingInput n c where
  grad := residualTranspose X (coreParameters S) t
  eta := safeStepSize X (coreParameters S) t
  opCost := opCost
  opRisk := opRisk
  write := write

/-- Execution of the unmodified canonical training transition. -/
noncomputable def ceTrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  trainStep S (ceTrainInput X t S opCost opRisk write)

/-- The executed subtraction by the residual transpose is exactly the CE
addition in its negative direction. -/
theorem coreParameters_ceTrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    coreParameters (ceTrainStep X t S opCost opRisk write) =
      ceNextParameters X (coreParameters S) t
        (safeStepSize X (coreParameters S) t) := by
  apply PiLp.ext
  intro i
  change S.model.weights i -
      safeStepSize X (coreParameters S) t * residualTranspose X (coreParameters S) t i =
    S.model.weights i + safeStepSize X (coreParameters S) t *
      (ceDirection X (coreParameters S) t).ofLp i
  rw [ceDirection_ofLp]
  ring

/-- The generic parameter step does not alter adapter coordinates. -/
theorem adapters_ceTrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (ceTrainStep X t S opCost opRisk write).model.adapters = S.model.adapters :=
  rfl

/-- External quality telemetry is stored unchanged, not asserted to improve. -/
theorem qual_ceTrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (ceTrainStep X t S opCost opRisk write).qual = S.qual :=
  rfl

/-- Positive computed range makes the executed learning rate positive. -/
theorem ceTrainInput_eta_pos (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hr : 0 < ceStepRange X (coreParameters S) t) :
    0 < (ceTrainInput X t S opCost opRisk write).eta :=
  safeStepSize_pos_of_range_pos X (coreParameters S) t hr

/-- Strict actual CE descent of the executed state, not a supplied decrease. -/
theorem coreCEObjective_ceTrainStep_lt [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hr : 0 < ceStepRange X (coreParameters S) t) :
    coreCEObjective X t (ceTrainStep X t S opCost opRisk write) <
      coreCEObjective X t S := by
  rw [coreCEObjective, coreCEObjective, coreParameters_ceTrainStep]
  exact ceOneHot_safeStep_lt X (coreParameters S) t hr

/-- Minimal certificate whose drop is exactly old CE minus new CE. -/
noncomputable def ceTrainStepMinimalCert [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hr : 0 < ceStepRange X (coreParameters S) t) :
    CertStep (coreCEObjective X t) S (ceTrainStep X t S opCost opRisk write) where
  drop := coreCEObjective X t S -
    coreCEObjective X t (ceTrainStep X t S opCost opRisk write)
  drop_pos := sub_pos.mpr (coreCEObjective_ceTrainStep_lt X t S opCost opRisk write hr)
  actual := by
    have hlt := coreCEObjective_ceTrainStep_lt X t S opCost opRisk write hr
    linarith

/-- Full canonical certificate for the real CE objective.  Only the external
stored `qual` is preserved for the floor: CE descent does not imply a quality
change.  Optimizer moments, resource counters, and optional memory writes can
still change according to `trainStep`. -/
noncomputable def ceTrainStepCert [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (floor : QualityVector) (riskLim : ℝ)
    (hr : 0 < ceStepRange X (coreParameters S) t)
    (hrisk : 0 ≤ opRisk) (hcost : 0 ≤ opCost)
    (hriskLim : opRisk ≤ riskLim) (hfloor : FloorHeld S floor)
    (hbudget : opCost ≤ S.res.budget) :
    StepCert (coreCEObjective X t) trainMeasured floor riskLim S
      (ceTrainStep X t S opCost opRisk write) S.res.budget
      (ceTrainStep X t S opCost opRisk write).res.budget where
  riskSpend := opRisk
  budgetSpend := opCost
  trans :=
    { objectiveDrop := (ceTrainStepMinimalCert X t S opCost opRisk write hr).drop
      objectiveDrop_pos :=
        (ceTrainStepMinimalCert X t S opCost opRisk write hr).drop_pos
      actualDescent := (ceTrainStepMinimalCert X t S opCost opRisk write hr).actual
      riskBound := hriskLim
      budgetBound := by
        rw [ceTrainStep, trainStep_budget, ceTrainInput]
        exact sub_nonneg.mpr hbudget }
  hriskSpend_nn := hrisk
  hbudgetSpend_nn := hcost
  hdec := le_of_eq (trainStep_budget S (ceTrainInput X t S opCost opRisk write))
  quality := by
    intro i
    change floor i ≤ (ceTrainStep X t S opCost opRisk write).qual i
    rw [qual_ceTrainStep]
    exact hfloor i

/-- Raw empirical mean of CE on the supplied labels and actual current weights.
This is an observation bound to parameters and data, not a separate measured
score or a statistical-confidence/generalization assertion.  At `m = 0`, Lean's
algebra makes the empty expression zero; that says nothing about confidence or
generalization. -/
noncomputable def batchCEObservation {m : ℕ} (X : Matrix V (Fin n) ℝ)
    (S : TrainState n a r c k) (y : Fin m → V) : ℝ :=
  Hagi.Probability.FiniteFamilyConfidence.empiricalMean
    (fun _i t => Hagi.ceOneHot t (ceLogits X (coreParameters S))) y

/-- Zero-weight two-class state for a concrete nondegenerate step.  The zero
adapter rank and zero stored quality are honest witnesses, not architecture or
benchmark claims.  Budget `2`, preexisting counters `11`, `7`, `5`, and the
later cost/risk inputs are hypothetical ledger values, not hardware samples. -/
noncomputable def identityInitialState : TrainState 2 0 0 0 0 where
  model := { weights := fun _ => 0, adapters := fun _ => 0, version := 0 }
  opt := { m := fun _ => 0, v := fun _ => 0, schedStep := 0 }
  mem := { ram := 0, lowRank := 0, consolidated := 0 }
  res := { budget := 2, flops := 11, gpuMem := 7, latency := 5 }
  saf := { risk := 0, riskLim := 1, protectedChannels := ∅ }
  qual := fun _ => 0

/-- The executed identity-features step with supplied logical cost `1/2`,
risk `1/4`, and no memory write. -/
noncomputable def identityCEStep : TrainState 2 0 0 0 0 :=
  ceTrainStep (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityInitialState
    (1 / 2) (1 / 4) none

/-- The concrete initial range is the existing computed value `2`. -/
theorem identity_range_pos :
    0 < ceStepRange (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0 := by
  change 0 < ceStepRange (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
  rw [identityTwoClass_range_test]
  norm_num

/-- Actual executed parameters: safe eta is `1/2`, direction is `(1/2,-1/2)`,
and no replacement state with preselected weights is constructed. -/
theorem coreParameters_identityCEStep :
    coreParameters identityCEStep =
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (1 : ℝ) / 4 else -1 / 4) := by
  rw [identityCEStep, coreParameters_ceTrainStep]
  have hzero : coreParameters identityInitialState = 0 := rfl
  rw [hzero, identityTwoClass_safeStepSize_test]
  apply PiLp.ext
  intro i
  fin_cases i <;>
    norm_num [ceNextParameters, ceDirection, residualTranspose, ceResidual,
      ceLogits, Hagi.Energy.smax, Hagi.Prelude.softDef, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- Strict CE descent for the concrete executed state. -/
theorem coreCEObjective_identityCEStep_lt :
    coreCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityCEStep <
      coreCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityInitialState :=
  coreCEObjective_ceTrainStep_lt _ _ _ _ _ _ identity_range_pos

/-- A complete concrete canonical certificate.  Nonzero cost/risk and budget
are finite hypothetical inputs, not physical resource measurements. -/
noncomputable def identityStepCert :
    StepCert (coreCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ) 0)
      trainMeasured (fun _ => 0) (1 / 2) identityInitialState identityCEStep
      identityInitialState.res.budget identityCEStep.res.budget :=
  ceTrainStepCert (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityInitialState
    (1 / 2) (1 / 4) none (fun _ => 0) (1 / 2) identity_range_pos
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; change (0 : ℝ) ≤ 0; exact le_rfl)
    (by change (1 / 2 : ℝ) ≤ 2; norm_num)

/-- At zero weights, two identical supplied labels give raw mean CE `log 2`.
The labels are an explicit witness sample, not fresh or held-out data. -/
theorem batchCEObservation_identityInitial_eq :
    batchCEObservation (1 : Matrix (Fin 2) (Fin 2) ℝ) identityInitialState
      (fun _ : Fin 2 => (0 : Fin 2)) = Real.log 2 := by
  norm_num [batchCEObservation,
    Hagi.Probability.FiniteFamilyConfidence.empiricalMean, coreParameters,
    identityInitialState, ceLogits, Hagi.ceOneHot, Hagi.Core.lse, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

/-- The same two-label raw observation strictly decreases after the executed
parameter update, so the batch check uses the parametric bridge as well. -/
theorem batchCEObservation_identityCEStep_lt :
    batchCEObservation (1 : Matrix (Fin 2) (Fin 2) ℝ) identityCEStep
      (fun _ : Fin 2 => (0 : Fin 2)) <
    batchCEObservation (1 : Matrix (Fin 2) (Fin 2) ℝ) identityInitialState
      (fun _ : Fin 2 => (0 : Fin 2)) := by
  have hlt := coreCEObjective_identityCEStep_lt
  unfold batchCEObservation Hagi.Probability.FiniteFamilyConfidence.empiricalMean
  simp only [Fin.sum_univ_two]
  norm_num [coreCEObjective] at hlt ⊢
  linarith

end Hagi.Contracts.CEStep
