import Hagi.Contracts.CEStepCertificate
import Hagi.Contracts.ObjectiveTrajectory
import Hagi.Model.GatedCESafeStep
import Hagi.Model.CEHeldout
import Hagi.Unified.GuardedRobustTrajectory

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

/-!
# Budget-gated two-action control of canonical gated CE

The new transition executes the existing canonical `gatedCETrainStep` only
when `0 ≤ opCost ∧ opCost ≤ S.res.budget`; otherwise it is the identity on the
full `TrainState`. The old transition is unchanged. Actual one-target gated
CE cannot increase in either branch, using the existing safe-step certificate
without a positive-alignment premise. A nonnegative declared budget remains
nonnegative, and stored quality telemetry is preserved.

The `Fin 2` controller has the identity stay action and the budget-gated
update action. Its value is negative actual gated CE. `memory = a.val` and
`operations = 2 * a.val` are logical action-index model units, not resource
counters in `TrainState` or physical measurements. Safety is actual CE
non-regression for every full training state.

The value estimate is the true value with the constant pessimistic bias
`-1 / 2`. Its pointwise absolute error is exactly `1 / 2`, hence it satisfies
the feasible-successor error interface of
`Hagi.Unified.GuardedRobustSelection.guardedRobustNext`. This is exact
deterministic arithmetic, not an IID, probabilistic, or calibration guarantee.
No trajectory, physical-resource, or generalization claim is made here.
-/

namespace Hagi.Contracts.BudgetedGatedCE

open Hagi.State Hagi.Model
open Hagi.Model.GatedCESafeStep
open Hagi.Contracts.GatedCEStep Hagi.Contracts.CEStep
open Hagi.Unified.ParetoExecution

variable {V : Type} [Fintype V]
variable {n a r c k : ℕ}

/-- Execute the existing canonical gated CE step exactly when its supplied
nonnegative logical cost fits the current declared budget; otherwise stay. -/
noncomputable def budgetedGatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) : TrainState n a r c k :=
  if 0 ≤ opCost ∧ opCost ≤ S.res.budget then
    gatedCETrainStep X t S opCost opRisk write
  else
    S

/-- In the active budget branch the new step is exactly the old canonical
transition, including its full optimizer, memory, resource, and risk updates. -/
theorem budgetedGatedCETrainStep_of_active (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (h : 0 ≤ opCost ∧ opCost ≤ S.res.budget) :
    budgetedGatedCETrainStep X t S opCost opRisk write =
      gatedCETrainStep X t S opCost opRisk write := by
  exact ite_eq_left h

/-- A negative or over-budget cost makes the guarded transition the identity
on the entire state. -/
theorem budgetedGatedCETrainStep_of_inactive (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (h : ¬ (0 ≤ opCost ∧ opCost ≤ S.res.budget)) :
    budgetedGatedCETrainStep X t S opCost opRisk write = S := by
  exact ite_eq_right h

/-- Actual gated one-target CE never increases, for every supplied cost,
risk, and optional write. No positive-alignment hypothesis is needed. -/
theorem gatedCEObjective_budgetedGatedCETrainStep_le
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    gatedCEObjective X t (budgetedGatedCETrainStep X t S opCost opRisk write) ≤
      gatedCEObjective X t S := by
  letI : Nonempty V := ⟨t⟩
  by_cases h : 0 ≤ opCost ∧ opCost ≤ S.res.budget
  · rw [budgetedGatedCETrainStep_of_active X t S opCost opRisk write h]
    have hdrop := gatedSafeDrop_le_gatedCETrainStep_drop
      X t S opCost opRisk write
    have hnonneg := gatedSafeDrop_nonneg X (coreParameters S) t
    linarith
  · rw [budgetedGatedCETrainStep_of_inactive X t S opCost opRisk write h]

/-- The guarded transition preserves a nonnegative declared budget. -/
theorem budgetedGatedCETrainStep_budget_nonneg
    (X : Matrix V (Fin n) ℝ) (t : V) (S : TrainState n a r c k)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (hbudget : 0 ≤ S.res.budget) :
    0 ≤ (budgetedGatedCETrainStep X t S opCost opRisk write).res.budget := by
  by_cases h : 0 ≤ opCost ∧ opCost ≤ S.res.budget
  · rw [budgetedGatedCETrainStep_of_active X t S opCost opRisk write h,
      gatedCETrainStep, trainStep_budget, gatedCETrainInput]
    exact sub_nonneg.mpr h.2
  · rw [budgetedGatedCETrainStep_of_inactive X t S opCost opRisk write h]
    exact hbudget

/-- The guarded transition preserves the stored quality telemetry; this is
not an identification of that telemetry with the actual CE objective. -/
theorem qual_budgetedGatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    (budgetedGatedCETrainStep X t S opCost opRisk write).qual = S.qual := by
  by_cases h : 0 ≤ opCost ∧ opCost ≤ S.res.budget
  · rw [budgetedGatedCETrainStep_of_active X t S opCost opRisk write h]
    exact qual_gatedCETrainStep X t S opCost opRisk write
  · rw [budgetedGatedCETrainStep_of_inactive X t S opCost opRisk write h]

/-- For nonnegative supplied cost, the declared FLOP ledger is nondecreasing.
This concerns only `res.flops`, not physical hardware work. -/
theorem flops_le_budgetedGatedCETrainStep (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (hcost : 0 ≤ opCost) :
    S.res.flops ≤
      (budgetedGatedCETrainStep X t S opCost opRisk write).res.flops := by
  by_cases h : 0 ≤ opCost ∧ opCost ≤ S.res.budget
  · rw [budgetedGatedCETrainStep_of_active X t S opCost opRisk write h,
      gatedCETrainStep, trainStep_flops, gatedCETrainInput]
    exact le_add_of_nonneg_right hcost
  · rw [budgetedGatedCETrainStep_of_inactive X t S opCost opRisk write h]

/-- The two controller successors: action zero stays, action one executes the
new budget-gated canonical transition. -/
noncomputable def gatedCEStepFun (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (action : Fin 2) (S : TrainState n a r c k) : TrainState n a r c k :=
  if action = 1 then budgetedGatedCETrainStep X t S opCost opRisk write else S

/-- Canonical full-state two-action gated CE controller. -/
noncomputable def gatedCEProblem (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    ControllerProblem (Fin 2) (TrainState n a r c k) where
  value := fun S => -gatedCEObjective X t S
  step := gatedCEStepFun X t opCost opRisk write
  memory := fun action => action.val
  operations := fun action => 2 * action.val
  safe := fun action => ∀ S : TrainState n a r c k,
    gatedCEObjective X t (gatedCEStepFun X t opCost opRisk write action S) ≤
      gatedCEObjective X t S

/-- The two finite actions are decided by their proved CE non-regression. -/
noncomputable instance gatedCEProblemSafeDecidable
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) :
    DecidablePred (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write).safe :=
  fun action =>
    if h : action = 0 then
      isTrue (by
        subst action
        intro S
        simp [gatedCEStepFun])
    else
      isTrue (by
        have ha_one : action = 1 := by
          have hval : action.val = 0 ∨ action.val = 1 := by omega
          rcases hval with hzero | hone
          · exact False.elim (h (Fin.ext hzero))
          · exact Fin.ext hone
        subst action
        intro S
        simpa [gatedCEStepFun] using
          (gatedCEObjective_budgetedGatedCETrainStep_le
            X t S opCost opRisk write))

@[simp] theorem gatedCEProblem_step_zero (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (gatedCEProblem X t opCost opRisk write).step 0 S = S := by
  simp [gatedCEProblem, gatedCEStepFun]

@[simp] theorem gatedCEProblem_step_one (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (gatedCEProblem X t opCost opRisk write).step 1 S =
      budgetedGatedCETrainStep X t S opCost opRisk write := by
  simp [gatedCEProblem, gatedCEStepFun]

/-- The identity stay action is feasible under every pair of logical caps. -/
theorem gatedCE_stay_feasible (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) M C := by
  apply mem_feasible.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro S
    rw [show gatedCEStepFun X t opCost opRisk write 0 S = S by
      simp [gatedCEStepFun]]
  · simp [gatedCEProblem]
  · simp [gatedCEProblem]

/-- Action one is feasible exactly when its declared memory and operation
model-unit costs fit: `1 ≤ M` and `2 ≤ C`. -/
theorem gatedCE_one_feasible_iff (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ)) (M C : ℕ) :
    (1 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) M C ↔
      1 ≤ M ∧ 2 ≤ C := by
  constructor
  · intro h
    have hresources := (mem_feasible.mp h).2
    simp only [gatedCEProblem] at hresources
    omega
  · rintro ⟨hM, hC⟩
    apply mem_feasible.mpr
    refine ⟨?_, ?_, ?_⟩
    · intro S
      rw [show gatedCEStepFun X t opCost opRisk write 1 S =
        budgetedGatedCETrainStep X t S opCost opRisk write by
          simp [gatedCEStepFun]]
      exact gatedCEObjective_budgetedGatedCETrainStep_le
        X t S opCost opRisk write
    · simpa [gatedCEProblem] using hM
    · simpa [gatedCEProblem] using hC

/-- Deterministic pessimistic value estimate: true controller value minus the
constant bias `1 / 2`. -/
noncomputable def gatedCEValueEstimate (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) : ℝ :=
  (gatedCEProblem X t opCost opRisk write).value S - 1 / 2

/-- The absolute pointwise value-estimate error is exactly `1 / 2`. -/
theorem gatedCEValueEstimate_error (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    |(gatedCEProblem X t opCost opRisk write).value S -
      gatedCEValueEstimate X t opCost opRisk write S| = 1 / 2 := by
  unfold gatedCEValueEstimate
  norm_num

/-- Exact feasible-successor error bound in the interface consumed by
`Hagi.Unified.GuardedRobustSelection.guardedRobustNext`; feasibility is explicit
and no probability is involved. -/
theorem gatedCEValueEstimate_error_le (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) (M C : ℕ) (action : Fin 2)
    (_ha : action ∈ feasible (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) M C) :
    |(gatedCEProblem X t opCost opRisk write).value
        ((gatedCEProblem X t opCost opRisk write).step action S) -
      gatedCEValueEstimate X t opCost opRisk write
        ((gatedCEProblem X t opCost opRisk write).step action S)| ≤ 1 / 2 :=
  le_of_eq (gatedCEValueEstimate_error X t opCost opRisk write _)

open Hagi.Unified.FixedBiasBinaryProgress
open Hagi.Unified.GuardedRobustTrajectory
open Hagi.Unified.GuardedRobustSelection
open Filter Topology

/-- The actual one-target gated CE is nonnegative on every ordinary state. -/
theorem gatedCEObjective_nonneg (X : Matrix V (Fin n) ℝ) (t : V)
    (S : TrainState n a r c k) : 0 ≤ gatedCEObjective X t S := by
  let _ : Nonempty V := ⟨t⟩
  exact Hagi.Model.CEHeldout.ceOneHot_nonneg t _

/-- Nonnegative CE gives the controller's value an intrinsic upper bound zero. -/
theorem gatedCEProblem_value_le_zero (X : Matrix V (Fin n) ℝ) (t : V)
    (opCost opRisk : ℝ) (write : Option (Σ _ : ℕ, Fin c → ℝ))
    (S : TrainState n a r c k) :
    (gatedCEProblem X t opCost opRisk write).value S ≤ 0 := by
  exact neg_nonpos.mpr (gatedCEObjective_nonneg X t S)

/-- Unlike the stored quality telemetry, the actual one-target CE is monotone
nonincreasing along the guarded path. -/
theorem gatedCEPath_antitone
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    Antitone (fun i => gatedCEObjective X t
      (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 i)) := by
  apply antitone_nat_of_succ_le
  intro i
  have hstep := scaledBiasBinaryPath_quality_step
    (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) δ hδ M C h0 S0
    (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) i
  simpa only [gatedCEProblem, neg_neg] using neg_le_neg hstep

/-- Actual gated CE converges to its conditional infimum; that infimum need
not be zero, and no full-state/parameter identification is asserted here. -/
theorem gatedCEPath_tendsto_ciInf
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    Tendsto (fun i => gatedCEObjective X t
      (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 i)) atTop
      (𝓝 (⨅ i, gatedCEObjective X t
        (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
          X t opCost opRisk write) δ M C h0 S0 i))) :=
  Hagi.Contracts.ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg _
    (gatedCEPath_antitone X t opCost opRisk write δ hδ M C h0 S0)
    (fun _ => gatedCEObjective_nonneg X t _)

/-- The finite positive-gain count at the gated controller needs no separately
supplied upper quality bound: its value gap is exactly the initial CE. -/
theorem gatedCEProgressCount_le_div
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (T : ℕ) :
    (scaledBiasBinaryProgressCount
      (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 T : ℝ) ≤
      gatedCEObjective X t S0 / δ := by
  have hcount := scaledBiasBinaryProgressCount_le_div
    (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) δ hδ M C h0 S0
    (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) 0
    (fun _ => gatedCEProblem_value_le_zero X t opCost opRisk write _) T
  rw [scaledBiasBinaryPath_zero] at hcount
  simpa only [gatedCEProblem, zero_sub, neg_neg] using hcount

/-- The gated positive-threshold trajectory eventually has stationary full
successors; this is not a claim of global optimality or zero CE. -/
theorem gatedCEPath_eventually_succ_eq
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, ∀ i ≥ N,
      scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 (i + 1) =
      scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 i :=
  scaledBiasBinaryPath_eventually_succ_eq
    (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) δ hδ M C h0 S0
    (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) 0
    (fun _ => gatedCEProblem_value_le_zero X t opCost opRisk write _)

/-- The gated path is eventually equal to one of its own finite-time states. -/
theorem gatedCEPath_eventually_eq
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, ∀ i ≥ N,
      scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 i =
      scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 N :=
  scaledBiasBinaryPath_eventually_eq
    (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) δ hδ M C h0 S0
    (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) 0
    (fun _ => gatedCEProblem_value_le_zero X t opCost opRisk write _)

/-- Under any supplied full-state topology, the gated trajectory converges to
an eventual path state. This does not identify that state as a minimizer. -/
theorem gatedCEPath_tendsto_eventual_state
    [TopologicalSpace (TrainState n a r c k)]
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) :
    ∃ N, Filter.Tendsto
      (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0) Filter.atTop
      (𝓝 (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a)
        (r := r) (k := k) X t opCost opRisk write) δ M C h0 S0 N)) :=
  scaledBiasBinaryPath_tendsto_eventual_value
    (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
      X t opCost opRisk write) δ hδ M C h0 S0
    (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) 0
    (fun _ => gatedCEProblem_value_le_zero X t opCost opRisk write _)

/-- A nonnegative initial declared budget stays nonnegative on every gated
path state, including inactive steps and identity transitions. -/
theorem gatedCEPath_budget_nonneg
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (hbudget : 0 ≤ S0.res.budget) (T : ℕ) :
    0 ≤ (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r)
      (k := k) X t opCost opRisk write) δ M C h0 S0 T).res.budget := by
  induction T with
  | zero => exact hbudget
  | succ T ih =>
      rw [scaledBiasBinaryPath_succ]
      obtain ⟨action, ha, hstep⟩ := guardedRobustNext_exists
        (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
          X t opCost opRisk write)
        (scaledBiasBinaryValueEstimate
          (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
            X t opCost opRisk write) δ) (δ / 2)
        (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r)
          (k := k) X t opCost opRisk write) δ M C h0 S0 T) M C (0 : Fin 2) h0
      rw [hstep]
      have hcases : action.val = 0 ∨ action.val = 1 := by omega
      rcases hcases with hzero | hone
      · have ha0 : action = 0 := Fin.ext hzero
        subst action
        rw [gatedCEProblem_step_zero]
        exact ih
      · have ha1 : action = 1 := Fin.ext hone
        subst action
        rw [gatedCEProblem_step_one]
        exact budgetedGatedCETrainStep_budget_nonneg X t _ opCost opRisk write ih

/-- At a positive actual gated value gain, the budgeted canonical transition
really executes; hence that step contributes `opCost` and every other step
contributes zero to the declared `res.flops` counter. -/
theorem gatedCEPath_flops_succ
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (i : ℕ) :
    (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 (i + 1)).res.flops =
      (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 i).res.flops +
      if 0 < scaledBiasBinaryGain (gatedCEProblem (n := n) (a := a) (r := r)
        (k := k) X t opCost opRisk write) δ M C h0 S0 i then opCost else 0 := by
  classical
  by_cases hpos : 0 < scaledBiasBinaryGain
      (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 i
  · have hsucc := scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
      (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ hδ M C h0 S0
      (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) i hpos
    rw [gatedCEProblem_step_one] at hsucc
    have hactive : 0 ≤ opCost ∧ opCost ≤
        (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r)
          (k := k) X t opCost opRisk write) δ M C h0 S0 i).res.budget := by
      by_contra hinactive
      have hzero : scaledBiasBinaryGain
          (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
            X t opCost opRisk write) δ M C h0 S0 i = 0 := by
        rw [scaledBiasBinaryGain_eq_sub, hsucc,
          budgetedGatedCETrainStep_of_inactive X t _ opCost opRisk write hinactive,
          sub_self]
      linarith
    rw [hsucc, budgetedGatedCETrainStep_of_active X t _ opCost opRisk write hactive,
      gatedCETrainStep, trainStep_flops, gatedCETrainInput, ite_eq_left hpos]
  · have hnoup : ¬ estimatedUpgrade
        (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
          X t opCost opRisk write)
        (scaledBiasBinaryValueEstimate
          (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
            X t opCost opRisk write) δ) (δ / 2)
        (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r)
          (k := k) X t opCost opRisk write) δ M C h0 S0 i)
        M C (0 : Fin 2) := by
      intro hup
      exact hpos (scaledBiasBinaryGain_pos_of_upgrade
        (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
          X t opCost opRisk write) δ hδ M C h0 S0
        (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) i hup)
    rw [scaledBiasBinaryPath_succ,
      guardedRobustNext_of_no_upgrade
        (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
          X t opCost opRisk write)
        (scaledBiasBinaryValueEstimate
          (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
            X t opCost opRisk write) δ) (δ / 2) _ M C (0 : Fin 2) h0 hnoup]
    rw [gatedCEProblem_step_zero, ite_eq_right hpos, add_zero]

/-- Exact finite telescope for the declared gated FLOP counter. -/
theorem gatedCEPath_flops_eq
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (T : ℕ) :
    (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 T).res.flops =
      S0.res.flops + opCost * (scaledBiasBinaryProgressCount
        (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
          X t opCost opRisk write) δ M C h0 S0 T : ℝ) := by
  apply scaledBiasBinaryTrainPath_flops_eq
    (gatedCEProblem X t opCost opRisk write) δ hδ M C h0 S0
    (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) opCost ?_ T
  intro i hpos
  have h := gatedCEPath_flops_succ X t opCost opRisk write δ hδ M C h0 S0 i
  rw [scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
    (gatedCEProblem X t opCost opRisk write) δ hδ M C h0 S0
    (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) i hpos,
    ite_eq_left hpos] at h
  exact h

/-- With nonnegative supplied cost, the finite declared ledger increment is at
most `(opCost / δ) * initialCE`. This still does not count estimator evaluations. -/
theorem gatedCEPath_flops_le
    (X : Matrix V (Fin n) ℝ) (t : V) (opCost opRisk : ℝ)
    (write : Option (Σ _ : ℕ, Fin c → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (gatedCEProblem (n := n) (a := a)
      (r := r) (k := k) X t opCost opRisk write) M C)
    (S0 : TrainState n a r c k) (T : ℕ) (hcost : 0 ≤ opCost) :
    (scaledBiasBinaryPath (gatedCEProblem (n := n) (a := a) (r := r) (k := k)
        X t opCost opRisk write) δ M C h0 S0 T).res.flops ≤
      S0.res.flops + (opCost / δ) * gatedCEObjective X t S0 := by
  have h_value : (gatedCEProblem X t opCost opRisk write).value S0 =
      -gatedCEObjective X t S0 := rfl
  have hbound := scaledBiasBinaryTrainPath_flops_le_of_value_nonpos
    (gatedCEProblem X t opCost opRisk write) δ hδ M C h0 S0
    (fun S => gatedCEProblem_step_zero X t opCost opRisk write S)
    opCost hcost (fun S => gatedCEProblem_value_le_zero X t opCost opRisk write S)
    (by
      intro i hpos
      have h := gatedCEPath_flops_succ X t opCost opRisk write δ hδ M C h0 S0 i
      rw [scaledBiasBinaryPath_succ_eq_step_one_of_gain_pos
        (gatedCEProblem X t opCost opRisk write) δ hδ M C h0 S0
        (fun S => gatedCEProblem_step_zero X t opCost opRisk write S) i hpos,
        ite_eq_left hpos] at h
      exact h) T
  rw [h_value, neg_neg] at hbound
  exact hbound

/-- A concrete first path with threshold `1/16`, exact biased estimate and
unit caps one and two. Its only control parameters remain the canonical input. -/
noncomputable def identityScaledGatedCEPath : ℕ → TrainState 2 0 0 0 0 :=
  scaledBiasBinaryPath
    (gatedCEProblem (n := 2) (a := 0) (r := 0) (c := 0) (k := 0)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 (1 / 2) (1 / 4) none)
    (1 / 16) 1 2
    (gatedCE_stay_feasible (1 : Matrix (Fin 2) (Fin 2) ℝ) 0
      (1 / 2) (1 / 4) none 1 2) identityInitialState

/-- The first genuinely selected threshold upgrade executes the real canonical
`identityGatedCEStep`, not an identity or a resource-field replacement. -/
theorem identityScaledGatedCEPath_one :
    identityScaledGatedCEPath 1 = identityGatedCEStep := by
  let p : ControllerProblem (Fin 2) (TrainState 2 0 0 0 0) :=
    gatedCEProblem (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 (1 / 2) (1 / 4) none
  let h0 : (0 : Fin 2) ∈ feasible p 1 2 := by
    dsimp only [p]
    exact gatedCE_stay_feasible (1 : Matrix (Fin 2) (Fin 2) ℝ) 0
      (1 / 2) (1 / 4) none 1 2
  have h1 : (1 : Fin 2) ∈ feasible p 1 2 := by
    dsimp only [p]
    exact (gatedCE_one_feasible_iff _ _ _ _ _ _ _).mpr (by norm_num)
  have hactive : 0 ≤ (1 / 2 : ℝ) ∧
      (1 / 2) ≤ identityInitialState.res.budget := by
    constructor
    · norm_num
    · change (1 / 2 : ℝ) ≤ 2
      norm_num
  have hstep : p.step (1 : Fin 2) identityInitialState = identityGatedCEStep := by
    change budgetedGatedCETrainStep (1 : Matrix (Fin 2) (Fin 2) ℝ)
      0 identityInitialState (1 / 2) (1 / 4) none = identityGatedCEStep
    rw [budgetedGatedCETrainStep_of_active _ _ _ _ _ _ hactive]
    rfl
  have hstay : ∀ S : TrainState 2 0 0 0 0, p.step (0 : Fin 2) S = S := by
    intro S
    dsimp only [p]
    exact gatedCEProblem_step_zero _ _ _ _ _ _
  have hdrop := gatedSafeDrop_le_gatedCETrainStep_drop
    (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityInitialState (1 / 2) (1 / 4) none
  rw [identity_gatedSafeDrop] at hdrop
  change (1 / 16 : ℝ) ≤ gatedCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ)
      0 identityInitialState -
    gatedCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 identityGatedCEStep at hdrop
  have hup : estimatedUpgrade p
      (scaledBiasBinaryValueEstimate p (1 / 16)) (1 / 16 / 2)
      (scaledBiasBinaryPath p (1 / 16) 1 2 h0 identityInitialState 0) 1 2 0 := by
    refine ⟨1, h1, ?_⟩
    change (-gatedCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ) 0
        (p.step 0 (scaledBiasBinaryPath p (1 / 16) 1 2 h0 identityInitialState 0)) -
        (1 / 16 : ℝ) / 2) + 2 * ((1 / 16 : ℝ) / 2) ≤
      -gatedCEObjective (1 : Matrix (Fin 2) (Fin 2) ℝ) 0
        (p.step 1 (scaledBiasBinaryPath p (1 / 16) 1 2 h0 identityInitialState 0)) -
        (1 / 16 : ℝ) / 2
    rw [scaledBiasBinaryPath_zero, hstay, hstep]
    linarith
  have hnext := scaledBiasBinaryPath_succ_eq_step_one_of_upgrade p
    (1 / 16) (by norm_num) 1 2 h0 identityInitialState hstay 0 hup
  rw [scaledBiasBinaryPath_zero] at hnext
  unfold identityScaledGatedCEPath
  exact hnext.trans hstep

end Hagi.Contracts.BudgetedGatedCE
