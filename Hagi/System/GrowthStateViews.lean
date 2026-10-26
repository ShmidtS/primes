import Hagi.System.GrowthState

/-!
# GrowthStateViews — разбиение состояния на 5 сущностей (P2.9)

Канонический `GrowthState` (17 полей) канонически разлагается
на пять сущностей плана рефакторинга P2.9:

* **ModelPart** — состояние модели (weights/params/experts/
  weightDim);
* **MetricsPart** — метрики (capability/verifier/runtimeError/
  gap/energy);
* **MemoryPart** — память (dataField);
* **OptimizerPart** — оптимизатор (stepDir/grad/sp/effects);
* **ResourcePart** — ресурсный баланс (budget/protectedRisk).

Каждая сущность — структура-представление с проекциями
`toParts`/`ofParts`; раунд-трип сохраняет состояние
(`GrowthState_parts_roundtrip`). Канон не меняется —
views дают модульный доступ без слома 2900+ деклараций.
-/

namespace Hagi.System

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Сущность 1: состояние модели. -/
structure ModelPart (X : Type*) [NormedAddCommGroup X] where
  weightDim : ℕ
  weights : Fin weightDim → ℝ
  params : X
  experts : ℕ

/-- Сущность 2: метрики качества. -/
structure MetricsPart where
  energy : ℝ
  gap : ℝ
  capability : ℝ
  verifier : ℝ
  runtimeError : ℝ

/-- Сущность 3: память. -/
structure MemoryPart where
  dataField : ℝ

/-- Сущность 4: оптимизатор. -/
structure OptimizerPart (X : Type*) [NormedAddCommGroup X] where
  stepDir : X
  grad : X
  sp : StageParams
  effects : StageEffects

/-- Сущность 5: ресурсный баланс. -/
structure ResourcePart where
  budget : ℝ
  protectedRisk : ℝ

/-- Разложение состояния на пять сущностей. -/
def toParts (S : GrowthState X) :
    ModelPart X × MetricsPart × MemoryPart × OptimizerPart X × ResourcePart where
  1 := ⟨S.weightDim, S.weights, S.params, S.experts⟩
  2.1 := ⟨S.energy, S.gap, S.capability, S.verifier, S.runtimeError⟩
  2.2.1 := ⟨S.dataField⟩
  2.2.2.1 := ⟨S.stepDir, S.grad, S.sp, S.effects⟩
  2.2.2.2 := ⟨S.budget, S.protectedRisk⟩

/-- Сборка состояния из пяти сущностей. -/
def ofParts (p : ModelPart X × MetricsPart × MemoryPart × OptimizerPart X × ResourcePart) :
    GrowthState X where
  weightDim := p.1.weightDim
  weights := p.1.weights
  params := p.1.params
  experts := p.1.experts
  energy := p.2.1.energy
  protectedRisk := p.2.2.2.2.protectedRisk
  budget := p.2.2.2.2.budget
  gap := p.2.1.gap
  dataField := p.2.2.1.dataField
  capability := p.2.1.capability
  verifier := p.2.1.verifier
  runtimeError := p.2.1.runtimeError
  stepDir := p.2.2.2.1.stepDir
  grad := p.2.2.2.1.grad
  sp := p.2.2.2.1.sp
  effects := p.2.2.2.1.effects

/-- РАУНД-ТРИП: разложение-сборка сохраняет состояние
(корректность разбиения P2.9). -/
theorem GrowthState_parts_roundtrip (S : GrowthState X) :
    ofParts (toParts S) = S := by
  rfl

/-- Проекция раунд-трипа: разложение инъективно. -/
theorem toParts_injective (S S' : GrowthState X)
    (h : toParts S = toParts S') : S = S' := by
  have : ofParts (toParts S) = ofParts (toParts S') := by rw [h]
  rwa [GrowthState_parts_roundtrip, GrowthState_parts_roundtrip] at this

end Hagi.System
