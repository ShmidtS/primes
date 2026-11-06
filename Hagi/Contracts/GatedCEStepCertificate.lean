import Hagi.Contracts.CEStepCertificate
import Hagi.Model.GatedCESafeStep

/-!
# Gated categorical-CE execution through the canonical training transition

This additive adapter executes the existing `TrainState.trainStep` with the
actual gated residual-transpose gradient and explicit nonlinear safe step.
Its objective is the one-target categorical cross-entropy of the current
backbone weights through `gatedForward`.  The strict descent theorem uses the
proved safe-step majorizer, whose drop is only a lower bound on the actual
objective decrease.

The supplied cost, risk, and optional write remain logical transition inputs.
Stored `qual` and adapter coordinates are preserved; categorical CE is not the
stored quality telemetry.  This module asserts no batch, generalization,
physical-resource, or repeated-training/trajectory guarantee.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Contracts.GatedCEStep

open Hagi.State Hagi.Model
open Hagi.Model.GatedCEGradient Hagi.Model.GatedCEDescent
open Hagi.Model.GatedCESafeStep
open Hagi.Contracts.CEStep
open Hagi.Unified.HonestTransition Hagi.Unified.CertifiedLoop

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- Actual gated categorical CE of the state's current backbone weights for
one supplied target. -/
noncomputable def gatedCEObjective (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) : ℝ :=
  Hagi.ceOneHot t (gatedForward X (coreParameters S))

/-- The ordinary training input computed from the current gated CE parameters.
`opCost`, `opRisk`, and `write` are supplied externally to the transition. -/
noncomputable def gatedCETrainInput (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainingInput n c where
  grad := gatedResidualTranspose X (coreParameters S) t
  eta := gatedSafeStepSize X (coreParameters S) t
  opCost := opCost
  opRisk := opRisk
  write := write

/-- Execution of the unmodified canonical training transition. -/
noncomputable def gatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  trainStep S (gatedCETrainInput X t S opCost opRisk write)

/-- Canonical subtraction by the gated residual transpose is exactly addition
of the explicit safe step in the negative gated direction. -/
theorem coreParameters_gatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    coreParameters (gatedCETrainStep X t S opCost opRisk write) =
      gatedNextParameters X (coreParameters S) t
        (gatedSafeStepSize X (coreParameters S) t) := by
  apply PiLp.ext
  intro i
  change S.model.weights i -
      gatedSafeStepSize X (coreParameters S) t *
        gatedResidualTranspose X (coreParameters S) t i =
    S.model.weights i + gatedSafeStepSize X (coreParameters S) t *
      (gatedDirection X (coreParameters S) t).ofLp i
  rw [gatedDirection_ofLp]
  ring

/-- The canonical parameter step preserves all adapter coordinates. -/
theorem adapters_gatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (gatedCETrainStep X t S opCost opRisk write).model.adapters =
      S.model.adapters :=
  rfl

/-- Stored external quality telemetry is unchanged, not equated with CE. -/
theorem qual_gatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (gatedCETrainStep X t S opCost opRisk write).qual = S.qual :=
  rfl

/-- Positive alignment makes the canonical input's safe learning rate positive. -/
theorem gatedCETrainInput_eta_pos (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hA : 0 < gatedAlignment X (coreParameters S) t) :
    0 < (gatedCETrainInput X t S opCost opRisk write).eta :=
  gatedSafeStepSize_pos_of_alignment_pos X (coreParameters S) t hA

/-- Strict actual gated one-target CE descent of the executed state. -/
theorem gatedCEObjective_gatedCETrainStep_lt [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hA : 0 < gatedAlignment X (coreParameters S) t) :
    gatedCEObjective X t (gatedCETrainStep X t S opCost opRisk write) <
      gatedCEObjective X t S := by
  rw [gatedCEObjective, gatedCEObjective, coreParameters_gatedCETrainStep]
  exact gated_ceOneHot_safeStep_lt X (coreParameters S) t hA

/-- The model majorizer drop lower-bounds the exact actual CE decrease; the
certificate below does not identify these two generally different quantities. -/
theorem gatedSafeDrop_le_gatedCETrainStep_drop [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    gatedSafeDrop X (coreParameters S) t ≤
      gatedCEObjective X t S -
        gatedCEObjective X t (gatedCETrainStep X t S opCost opRisk write) := by
  have hbound := gated_ceOneHot_safeStep_le_drop X (coreParameters S) t
  rw [gatedCEObjective, gatedCEObjective, coreParameters_gatedCETrainStep]
  linarith

/-- Minimal canonical certificate whose drop is exactly old actual gated CE
minus new actual gated CE. -/
noncomputable def gatedCETrainStepMinimalCert [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hA : 0 < gatedAlignment X (coreParameters S) t) :
    CertStep (gatedCEObjective X t) S
      (gatedCETrainStep X t S opCost opRisk write) where
  drop := gatedCEObjective X t S -
    gatedCEObjective X t (gatedCETrainStep X t S opCost opRisk write)
  drop_pos := sub_pos.mpr
    (gatedCEObjective_gatedCETrainStep_lt X t S opCost opRisk write hA)
  actual := by
    have hlt := gatedCEObjective_gatedCETrainStep_lt X t S opCost opRisk write hA
    linarith

/-- Full existing canonical certificate for actual gated one-target CE.  Its
quality floor concerns only preserved stored telemetry.  Optimizer moments,
resource counters, and optional memory writes can still change according to
`trainStep`; the supplied ledger values are not physical measurements. -/
noncomputable def gatedCETrainStepCert [Nonempty V]
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (floor : QualityVector) (riskLim : ℝ)
    (hA : 0 < gatedAlignment X (coreParameters S) t)
    (hrisk : 0 ≤ opRisk) (hcost : 0 ≤ opCost)
    (hriskLim : opRisk ≤ riskLim) (hfloor : FloorHeld S floor)
    (hbudget : opCost ≤ S.res.budget) :
    StepCert (gatedCEObjective X t) trainMeasured floor riskLim S
      (gatedCETrainStep X t S opCost opRisk write) S.res.budget
      (gatedCETrainStep X t S opCost opRisk write).res.budget where
  riskSpend := opRisk
  budgetSpend := opCost
  trans :=
    { objectiveDrop :=
        (gatedCETrainStepMinimalCert X t S opCost opRisk write hA).drop
      objectiveDrop_pos :=
        (gatedCETrainStepMinimalCert X t S opCost opRisk write hA).drop_pos
      actualDescent :=
        (gatedCETrainStepMinimalCert X t S opCost opRisk write hA).actual
      riskBound := hriskLim
      budgetBound := by
        rw [gatedCETrainStep, trainStep_budget, gatedCETrainInput]
        exact sub_nonneg.mpr hbudget }
  hriskSpend_nn := hrisk
  hbudgetSpend_nn := hcost
  hdec := le_of_eq
    (trainStep_budget S (gatedCETrainInput X t S opCost opRisk write))
  quality := by
    intro i
    change floor i ≤ (gatedCETrainStep X t S opCost opRisk write).qual i
    rw [qual_gatedCETrainStep]
    exact hfloor i

/-- The identity-features alignment at zero initial weights, computed from the
actual state parameters. -/
theorem identity_gatedAlignment :
    gatedAlignment (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0 = 1 / 2 := by
  change gatedAlignment (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 2
  exact identityTwoClass_gatedAlignment_test

/-- Positive identity alignment supplies the strict-descent hypothesis. -/
theorem identity_gatedAlignment_pos :
    0 < gatedAlignment (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0 := by
  rw [identity_gatedAlignment]
  norm_num

/-- The identity-features safe-step curvature is `1`. -/
theorem identity_gatedCurvature :
    gatedCurvature (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0 = 1 := by
  change gatedCurvature (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1
  exact identityTwoClass_gatedCurvature_test

/-- The actual canonical input uses safe step `1/4`. -/
theorem identity_gatedSafeStepSize :
    gatedSafeStepSize (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0 = 1 / 4 := by
  change gatedSafeStepSize (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 4
  exact identityTwoClass_gatedSafeStepSize_test

/-- The model majorizer drop is `1/16`, not an assertion that the exact actual
CE decrease equals this lower bound. -/
theorem identity_gatedSafeDrop :
    gatedSafeDrop (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (coreParameters identityInitialState) 0 = 1 / 16 := by
  change gatedSafeDrop (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 / 16
  exact identityTwoClass_gatedSafeDrop_test

/-- Concrete nondegenerate execution through `trainStep`, with supplied logical
cost `1/2`, risk `1/4`, and no memory write. -/
noncomputable def identityGatedCEStep : TrainState 2 0 0 0 0 :=
  gatedCETrainStep (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityInitialState
    (1 / 2) (1 / 4) none

/-- The actual canonical transition produces weights `(1/8,-1/8)`. -/
theorem coreParameters_identityGatedCEStep :
    coreParameters identityGatedCEStep =
      WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (1 : ℝ) / 8 else -1 / 8) := by
  rw [identityGatedCEStep, coreParameters_gatedCETrainStep]
  have hzero : coreParameters identityInitialState = 0 := rfl
  rw [hzero, identityTwoClass_gatedSafeStepSize_test]
  apply PiLp.ext
  intro i
  fin_cases i <;>
    norm_num [gatedNextParameters, gatedDirection, gatedResidualTranspose,
      gatedForward, Hagi.Prelude.softDef, Fin.sum_univ_two]

/-- Strict actual one-target CE descent for the concrete executed state. -/
theorem gatedCEObjective_identityGatedCEStep_lt :
    gatedCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityGatedCEStep <
      gatedCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityInitialState :=
  gatedCEObjective_gatedCETrainStep_lt _ _ _ _ _ _ identity_gatedAlignment_pos

/-- A complete concrete canonical certificate.  Nonzero cost/risk and budget
are finite hypothetical inputs, not physical resource measurements. -/
noncomputable def identityGatedStepCert :
    StepCert (gatedCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ) 0)
      trainMeasured (fun _ => 0) (1 / 2) identityInitialState identityGatedCEStep
      identityInitialState.res.budget identityGatedCEStep.res.budget :=
  gatedCETrainStepCert (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityInitialState
    (1 / 2) (1 / 4) none (fun _ => 0) (1 / 2) identity_gatedAlignment_pos
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; change (0 : ℝ) ≤ 0; exact le_rfl)
    (by change (1 / 2 : ℝ) ≤ 2; norm_num)

end Hagi.Contracts.GatedCEStep
