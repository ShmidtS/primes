import Mathlib
import Hagi.Foundations.GrowthBand
import Hagi.System.GrowthState

/-!
# MeasuredEffects — переход реального шага (аудит v10 P0-2/P0-3)

Критика аудита v10: `StageInput` получает `StageEffects`
готовыми числами, а `advance` лишь ПЕРЕНОСИТ их в следующее
состояние; имена `costGrow` возвращают РИСК, а не FLOPs.
Здесь закладывается исправленная схема:

  (S, batch, optimizer) → (S', ИЗМЕРЕННЫЕ эффекты, сертификат)

с раздельными типами величин: `StageRisk` (надежностная
цена), `ComputeCost` (FLOPs/ресурсы), `StageGain`
(прирост способности/энергии). Эффекты шага РАВНЫ выходу
измерителя (теорема trainStep_measured — «никакого
телепортирования эффектов»), бюджетный баланс считается по
ИЗМЕРЕННОЙ стоимости, а полоса роста выводится через
Hagi.Foundations.GrowthBand.growth_band_step из измеренного прироста.
-/

namespace Hagi.Model.MeasFx

/-- Надежностная цена стадий (НЕ FLOPs!). -/
structure StageRisk where
  grow : ℝ
  merge : ℝ
  joint : ℝ
  compress : ℝ

/-- Вычислительная стоимость стадий (FLOPs/ресурсы). -/
structure ComputeCost where
  grow : ℝ
  merge : ℝ
  joint : ℝ
  compress : ℝ

/-- Прирост шага: способность и энергия. -/
structure StageGain where
  capability : ℝ
  energy : ℝ

/-- Полный измеренный эффект шага. -/
structure MeasuredEffects where
  gain : StageGain
  risk : StageRisk
  cost : ComputeCost

/-- Состояние обучаемой системы (минимум для бухгалтерии). -/
structure MS where
  capability : ℝ
  budget : ℝ

/-- Итого риск измеренного шага. -/
def totalRisk (e : MeasuredEffects) : ℝ :=
  e.risk.grow + e.risk.merge + e.risk.joint + e.risk.compress

/-- Итого вычислительная стоимость измеренного шага. -/
def totalCost (e : MeasuredEffects) : ℝ :=
  e.cost.grow + e.cost.merge + e.cost.joint + e.cost.compress

variable (measure : MS → ℕ → MeasuredEffects)

/-- ОБУЧАЮЩИЙ ШАГ (v10 схема): состояние обновляется ТОЛЬКО
через измеренные эффекты данного измерителя; effects =
measure S batch по определению — никакие числа не
передаются извне мимо измерителя. -/
def trainStep : MS → ℕ → MS × MeasuredEffects
  | S, batch =>
    let e := measure S batch
    ({ capability := S.capability + e.gain.capability,
       budget := S.budget - totalCost e }, e)

/-- НЕТ ТЕЛЕПОРТИРОВАНИЯ: эффекты шага — в точности выход
измерителя (rfl-теорема, контракт схемы v10). -/
theorem trainStep_measured (S : MS) (batch : ℕ) :
    (trainStep measure S batch).2 = measure S batch := rfl

/-- БУХГАЛТЕРИЯ ПО ИЗМЕРЕННОМУ: бюджет после шага + измеренная
стоимость = бюджет до шага (баланс считается от measure,
не от переданных чисел). -/
theorem trainStep_budget_balance (S : MS) (batch : ℕ) :
    (trainStep measure S batch).1.budget
      + totalCost (measure S batch) = S.budget := by
  simp only [trainStep, totalCost]
  ring

/-- ПОЛОСА РОСТА ИЗ ИЗМЕРЕНИЯ: если измеренный прирост
способности лежит в полосе [αmin, αmax]·C, то capability
шага зажат двухсторонней полосой (реюз growth_band_step). -/
theorem trainStep_capability_band (S : MS) (batch : ℕ)
    (αmin αmax : ℝ)
    (hC : 0 ≤ S.capability) (hαmin : 0 ≤ αmin)
    (hband : αmin ≤ αmax)
    (hlo : αmin * S.capability
      ≤ (measure S batch).gain.capability)
    (hhi : (measure S batch).gain.capability
      ≤ αmax * S.capability) :
    (1 + αmin) * S.capability
      ≤ (trainStep measure S batch).1.capability
      ∧ (trainStep measure S batch).1.capability
        ≤ (1 + αmax) * S.capability := by
  have hstep : (trainStep measure S batch).1.capability
      = S.capability + (measure S batch).gain.capability :=
    rfl
  exact Hagi.Foundations.GrowthBand.growth_band_step S.capability
    (trainStep measure S batch).1.capability
    (measure S batch).gain.capability αmin αmax
    hC hαmin hband hstep hlo hhi

/-! ### Мосты унификации (аудит v11 P1: StageEffects ↔
типизированный MeasuredEffects — одна каноническая
типизированная структура, плоский StageEffects получает
типизированную проекцию без потери полей). -/

open Hagi.System

/-- Типизированная проекция плоского StageEffects. -/
def ofStageEffects (e : StageEffects) : MeasuredEffects where
  gain := ⟨e.growGain, e.growEnergy⟩
  risk := ⟨e.growRisk, e.mergeRisk, e.jointRisk, e.compressRisk⟩
  cost := ⟨e.growCost, e.mergeCost, e.jointCost, e.compressCost⟩

/-- Типизированные поля восстанавливаются из ofStageEffects
без искажения (репроекция компонент). -/
theorem ofStageEffects_roundtrip (e : StageEffects) :
    (ofStageEffects e).gain.capability = e.growGain
      ∧ (ofStageEffects e).risk.grow = e.growRisk
      ∧ (ofStageEffects e).risk.merge = e.mergeRisk
      ∧ (ofStageEffects e).risk.joint = e.jointRisk
      ∧ (ofStageEffects e).risk.compress = e.compressRisk
      ∧ (ofStageEffects e).cost.grow = e.growCost
      ∧ (ofStageEffects e).cost.merge = e.mergeCost
      ∧ (ofStageEffects e).cost.joint = e.jointCost
      ∧ (ofStageEffects e).cost.compress = e.compressCost := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- totalCost типизированной проекции = явная сумма полей
стоимости StageEffects (бухгалтерия согласована). -/
theorem totalCost_ofStageEffects (e : StageEffects) :
    totalCost (ofStageEffects e)
      = e.growCost + e.mergeCost + e.jointCost + e.compressCost :=
  rfl

/-- totalRisk типизированной проекции = явная сумма полей
риска StageEffects. -/
theorem totalRisk_ofStageEffects (e : StageEffects) :
    totalRisk (ofStageEffects e)
      = e.growRisk + e.mergeRisk + e.jointRisk + e.compressRisk :=
  rfl

end Hagi.Model.MeasFx

