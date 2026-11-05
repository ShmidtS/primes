import Mathlib
import Hagi.State.Transition
import Hagi.Unified.CertifiedLoop

/-!
# StepCertificate — мост TrainState → универсальный StepCert (Gate 3, §5.1)

TrainState получает канонический измеритель качества
(MeasuredState через evaluate — качество из фактического состояния)
и конструктор сертифицированного шага: спуск выводится из
trainStep_energy_descent (НЕ назначается), риск/бюджет — из
точной бухгалтерии trainStep. Траекторная композиция наследуется
универсальной certified_loop (§5.2: без дублирования).
-/

namespace Hagi.Contracts

open Hagi.State Hagi.Unified.CertifiedLoop Hagi.Unified.HonestTransition
open Hagi.Unified.LinkedQVec

variable {n a r c k : ℕ}

/-- Канонический измеритель TrainState: качество = evaluate
(из фактического состояния, §4.2). -/
noncomputable def trainMeasured : MeasuredState (TrainState n a r c k) where
  evaluate := Hagi.State.evaluate

/-- Фактический спуск — ТОЧНОЕ равенство из тождества энергии
(выводится, не постулируется). -/
theorem trainStep_actualDescent (S : TrainState n a r c k)
    (u : TrainingInput n c) :
    energy (trainStep S u)
      = energy S - (2 * u.eta * (∑ i, S.model.weights i * u.grad i)
        - u.eta ^ 2 * (∑ i, u.grad i ^ 2)) := by
  rw [trainStep_energy_identity]; ring

/-- Минимальное ядро `CertStep` TrainState: точный drop
вычислен из энергии перехода и положителен при исходном
sufficient-step condition; никакой постулированной
smoothness-посылки. -/
noncomputable def trainStepMinimalCert (S : TrainState n a r c k)
    (u : TrainingInput n c) (heta : 0 < u.eta)
    (hcond : 2 * (∑ i, S.model.weights i * u.grad i)
      > u.eta * (∑ i, u.grad i ^ 2)) :
    CertStep energy S (trainStep S u) where
  drop := 2 * u.eta * (∑ i, S.model.weights i * u.grad i)
    - u.eta ^ 2 * (∑ i, u.grad i ^ 2)
  drop_pos := by
    have hdescent := trainStep_energy_descent S u heta hcond
    rw [trainStep_energy_identity] at hdescent
    linarith
  actual := le_of_eq (trainStep_actualDescent S u)

noncomputable def trainStepCert (S : TrainState n a r c k)
    (u : TrainingInput n c) (floor : QualityVector) (riskLim : ℝ)
    (heta : 0 < u.eta)
    (hcond : 2 * (∑ i, S.model.weights i * u.grad i)
      > u.eta * (∑ i, u.grad i ^ 2))
    (hrisk : 0 ≤ u.opRisk)
    (hcost : 0 ≤ u.opCost)
    (hriskLim : u.opRisk ≤ riskLim)
    (hfloor : FloorHeld S floor)
    (hbudget : u.opCost ≤ S.res.budget) :
    StepCert energy trainMeasured floor riskLim
      S (trainStep S u) S.res.budget (trainStep S u).res.budget
      where
  riskSpend := u.opRisk
  budgetSpend := u.opCost
  trans := ⟨2 * u.eta * (∑ i, S.model.weights i * u.grad i)
      - u.eta ^ 2 * (∑ i, u.grad i ^ 2), by
      -- строгость дропа — из тождества энергии и достаточного условия
      have hdescent := trainStep_energy_descent S u heta hcond
      rw [trainStep_energy_identity] at hdescent
      -- energy' < energy  ⇔  дроп > 0
      have : 0 < 2 * u.eta * (∑ i, S.model.weights i * u.grad i)
          - u.eta ^ 2 * (∑ i, u.grad i ^ 2) := by
        have hE : energy (trainStep S u) - energy S
            = -(2 * u.eta * (∑ i, S.model.weights i * u.grad i)
              - u.eta ^ 2 * (∑ i, u.grad i ^ 2)) := by
          rw [trainStep_energy_identity]; ring
        linarith
      exact this,
    le_of_eq (trainStep_actualDescent S u),
    hriskLim,
    by
      show (0:ℝ) ≤ (trainStep S u).res.budget
      rw [trainStep_budget]
      linarith⟩
  hriskSpend_nn := hrisk
  hbudgetSpend_nn := hcost
  hdec := le_of_eq (trainStep_budget S u)
  quality := by
    intro i
    -- качество — телеметр; параметрический шаг его НЕ меняет (rfl)
    have hq : evaluate (trainStep S u) i = evaluate S i := rfl
    have hf := hfloor i
    show floor i ≤ evaluate (trainStep S u) i
    rw [hq]
    exact hf

end Hagi.Contracts
