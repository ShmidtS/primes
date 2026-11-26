/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.State.TrainState
import Hagi.Cert.Core

set_option linter.style.header false

/-!
# Views — тонкие представления носителей состояния

Обзор носителей состояния:

* `Hagi.State.TrainState` — каноническое состояние по спеке §4
  (шесть подсостояний; Hagi/State/TrainState.lean);
* `Hagi.System.GrowthState` — машинный носитель
  (Hagi/System/GrowthState.lean) с уже готовым разбиением на
  сущности `GrowthStateViews` (образец паттерна);
* `Hagi.Unified.FunctionalState` — функциональный носитель
  Unified-мира;
* `Hagi.Unified.MachineProto` (MeasureProto) — протокол измерений;
* NC-мир (`Hagi/Unified/NCStepCert.lean`) — собственный шаговый
  носитель.

Каноны не меняются; файл даёт модульный доступ к ним по паттерну
VIEW (как `GrowthStateViews`): `TrainState` как
`Hagi.Cert.SystemMetrics` (объектив = energy, риск = riskOf,
бюджет = budgetOf, TaskId = Unit).
-/

set_option relaxedAutoImplicit false

namespace Hagi.State

variable {n a r c k : ℕ}

/-- View: канонический `TrainState` как метрики сертификационного
ядра. Objective — энергия (сопровождающая цель, математически
однозначная); риск и бюджет — из подсостояний Safety/Resource;
тэг задачи — тривиальный (Unit). -/
def toSystemMetrics :
    Hagi.Cert.SystemMetrics (TrainState n a r c k) Unit where
  objective := fun St => energy St
  risk := fun St => riskOf St
  budget := fun St => budgetOf St
  task := fun _ => ()

/-- Спецификация view: objective читает ровно energy канона. -/
theorem toSystemMetrics_objective
    (St : TrainState n a r c k) :
    toSystemMetrics.objective St = energy St := rfl

/-- Спецификация view: risk читает ровно riskOf канона. -/
theorem toSystemMetrics_risk
    (St : TrainState n a r c k) :
    toSystemMetrics.risk St = riskOf St := rfl

/-- Спецификация view: budget читает ровно budgetOf канона. -/
theorem toSystemMetrics_budget
    (St : TrainState n a r c k) :
    toSystemMetrics.budget St = budgetOf St := rfl

end Hagi.State
