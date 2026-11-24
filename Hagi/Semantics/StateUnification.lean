/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hagi.State.Transition
import Hagi.State.CanonicalTrainState
import Hagi.Model.StageSemantics
import Hagi.Semantics.Split
set_option linter.style.header false

/-!
# StateUnification — единое состояние: связка трёх носителей (A17 stage 1)

Внешний аудит cb541cc (addendum A17, stage 1): качество должно
измеряться ЧЕРЕЗ семантику модели (params → forward → loss → metrics
одной цепочкой), а `StageSemantics`/`Transition` — привязаны к
каноническому носителю `CanonicalTrainState`.  Этот модуль — связка
(tie/invariant theorems, NOT a migration): ни одно утверждение
существующих модулей не меняется.

Слоёвое размещение: модуль обязан видеть `Hagi.Model.StageSemantics`
(layer 4) и `Hagi.Semantics.Split` (layer 5), поэтому живёт в
`Hagi/Semantics/` (layer 5), а не в `Hagi/State/` (layer 3, куда
LayerLint импорт верхних слоёв запрещает) — отклонение от буквы
задания зафиксировано в survey/plan/receipt .

## Главные элементы

* `coherentGrowth` + `growth_coherent_advance_iff` — ИНВАРИАНТ
  weights/params для `GrowthState`: `advance` сохраняет когерентность
  РОВНО тогда, когда направление спуска лежит в ядре проекции `f`
  (честная формализация разрыва: audit "no invariant tying them").
* `repairGrowth` + `growth_repair_coherent` — явное каноническое
  восстановление когерентности после `advance` (repair-условие).
* `qualityThroughModel` — ЕДИНЫЙ семантический путь
  params → forward (`ModelSpec.head`) → loss (`combineObjective`,
) → метрика (сумма по датасету).
* `measuredQuality` + `measureQuality_through_model` — мост,
  закрывающий external-measurement gap `Transition.measureQuality`:
  значение качества становится ФУНКЦИЕЙ новых params через
  семантику модели, дефинициально подхватывая обновление `trainStep`.
* `canonicalTrainStep`/`toGrowthState` + rfl-леммы — привязка
  `CanonicalTrainState` к `Transition.trainStep` и к ledger-полям
  `GrowthState` (проекции канонических шагов).

## Пины (что остаётся внешним — честно)

- Реальный forward глубоких сетей: `ModelSpec.head` — поле-гипотеза
  (конкретные головы живут в своих модулях, ledger).
- `advance`'s energy/gap/capability — измеренные ВХОДЫ `u.eff`
  (запрет §5 назначать их из params сохраняется).
- Проекция `f` — гипотеза (закон линейности на аффинных
  обновлениях), не теорема о конкретной f.
- `QualityVector`-каналы без `ModelSpec` — прежний внешний телеметр;
  канал-специфичные датасеты (разные ds на канал) — позже (YAGNI).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Semantics

open Hagi.Model Hagi.State Hagi.System

/-! ## (a) Когерентность `GrowthState`: weights = f params

`GrowthState` несёт ДВА параметрических поля — `params : X` и
`weights : Fin weightDim → ℝ` — без инварианта (аудит A17).
Связку задаёт проекция `f` с законом аффинной линейности. -/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Когерентность состояния: сжатые weights — в точности проекция f
параметров (инвариант, которого нет в `GrowthState` по построению). -/
def coherentGrowth (S : GrowthState X) (f : X → (Fin S.weightDim → ℝ)) : Prop :=
  f S.params = S.weights

/-- ТЕОРЕМА РАЗРЫВА:
`advance` сохраняет когерентность РОВНО тогда, когда направление
спуска лежит в ядре проекции f.  Доказательство существенно
использует закон аффинной линейности f и активность шага (0 < eta).
Направление вне ядра ЧЕСТНО ЛОМАЕТ инвариант — это условие ремонта,
а не постулат сохранения. -/
theorem growth_coherent_advance_iff (S : GrowthState X) (u : StageInput X)
    (f : X → (Fin S.weightDim → ℝ))
    (hf : ∀ (p d : X) (η : ℝ), f (p - η • d) = f p - (fun i => η * f d i))
    (h : coherentGrowth S f) :
    coherentGrowth (advance S u) f ↔ f u.stepDir = 0 := by
  constructor
  · intro hc
    have h1 : f (S.params - u.sp.eta • u.stepDir) = S.weights := hc
    rw [hf S.params u.stepDir u.sp.eta] at h1
    rw [← h] at h1
    have hz : (fun i => u.sp.eta * f u.stepDir i) = 0 := sub_eq_self.mp h1
    funext i
    have hi := congrFun hz i
    rcases mul_eq_zero.mp hi with h0 | h1'
    · exact absurd h0 (ne_of_gt u.h_eta_pos)
    · exact h1'
  · intro hd
    change f (S.params - u.sp.eta • u.stepDir) = S.weights
    rw [hf S.params u.stepDir u.sp.eta]
    funext i
    have hzi : f u.stepDir i = 0 := by simpa using congrFun hd i
    rw [Pi.sub_apply, hzi, mul_zero, sub_zero, ← congrFun h i]

/-- Каноническое восстановление: weights := f params (params, ledger
и все остальные поля не трогаются — repair ровно одного разрыва). -/
def repairGrowth (S : GrowthState X) (f : X → (Fin S.weightDim → ℝ)) :
    GrowthState X where
  weightDim := S.weightDim
  weights := f S.params
  params := S.params
  experts := S.experts
  energy := S.energy
  protectedRisk := S.protectedRisk
  budget := S.budget
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := S.effects

/-- Ремонт восстанавливает когерентность по построению. -/
theorem growth_repair_coherent (S : GrowthState X)
    (f : X → (Fin S.weightDim → ℝ)) :
    coherentGrowth (repairGrowth S f) f := rfl

/-- Ремонт после advance когерентен всегда: явное repair-условие
разрыва из `growth_coherent_advance_iff`. -/
theorem growth_repair_advance_coherent (S : GrowthState X) (u : StageInput X)
    (f : X → (Fin S.weightDim → ℝ)) :
    coherentGrowth (repairGrowth (advance S u) f) f := rfl

/-- Ремонт идемпотентен и не меняет когерентное состояние (weights
уже равны f params — repair неподвижен на когерентных состояниях). -/
theorem growth_repair_fixes_coherent (S : GrowthState X)
    (f : X → (Fin S.weightDim → ℝ)) (h : coherentGrowth S f) :
    repairGrowth S f = S := by
  revert f
  cases S with
  | mk wd w p ex en pr b g df cap ver re sd gr sp ef =>
    intro f h
    simp only [repairGrowth] at h ⊢
    rw [h]

/-! ## (b) Качество ЧЕРЕЗ семантику модели (params → forward → loss)

Единый семантический путь: `combineObjective` на каждой
точке датасета, суммированный.  Это и есть стрелка аудита
params → forward → loss → metrics ОДНОЙ цепочкой. -/

variable {Θ X' V : Type}

/-- Метрика качества ЧЕРЕЗ семантику модели: сумма объединённой
цели `combineObjective m o θ x y` (= objective-лосс на forward
`m.head θ x`) по датасету ds.  Единственный датасет — один лосс на
все каналы (пин: канал-специфичные датасеты — позже, YAGNI). -/
def qualityThroughModel (m : ModelSpec Θ X' V) (o : ObjectiveSpec V)
    (θ : Θ) (ds : List (X' × (V → ℝ))) : ℝ :=
  (ds.map (fun p => combineObjective m o θ p.1 p.2)).sum

/-- Семантическая метрика неотрицательна: floor-закон объективной
стороны переносится на сумму (`combineObjective_nonneg`). -/
theorem qualityThroughModel_nonneg (m : ModelSpec Θ X' V) (o : ObjectiveSpec V)
    (θ : Θ) (ds : List (X' × (V → ℝ))) :
    0 ≤ qualityThroughModel m o θ ds := by
  refine List.sum_nonneg (fun a ha => ?_)
  obtain ⟨p, _, hp⟩ := List.mem_map.mp ha
  rw [← hp]
  exact combineObjective_nonneg m o θ p.1 p.2

variable {n a e q r c k : ℕ}

/-- Измеренное качество TrainState ЧЕРЕЗ модель: каждый канал
quality-телеметра — семантическая метрика на ТЕКУЩИХ весах.
Закрывает external-measurement gap: значение качества теперь
ФУНКЦИЯ params (weights) через forward → loss, а не произвольный
внешний вектор. -/
def measuredQuality (m : ModelSpec (Fin n → ℝ) X' V) (o : ObjectiveSpec V)
    (S : TrainState n a r c k) (ds : List (X' × (V → ℝ))) :
    QualityVector :=
  fun _ => qualityThroughModel m o S.model.weights ds

/-- МОСТ (закрытие external-measurement gap): единственный способ
записать качество — `Transition.measureQuality`; если измерение
идёт через модель, то после параметрического шага `trainStep`
телеметр равен семантической метрике на НОВЫХ параметрах
`w − η·g` — дефинициально (rfl), т.е. связь не может потеряться.
Старое качество остаётся прежним (`trainStep_quality_unchanged`) —
обновление телеметра — только явное измерение. -/
theorem measureQuality_through_model (m : ModelSpec (Fin n → ℝ) X' V)
    (o : ObjectiveSpec V) (S : TrainState n a r c k) (u : TrainingInput n c)
    (ds : List (X' × (V → ℝ))) :
    (Hagi.State.measureQuality (trainStep S u)
        (measuredQuality m o (trainStep S u) ds)).qual
      = fun _ => qualityThroughModel m o
          (fun i => S.model.weights i - u.eta * u.grad i) ds := rfl

/-- Все каналы измеряются на ОДНОМ семантическом пути: каждый канал
`measuredQuality` равен `qualityThroughModel` на текущих весах
(стрелка аудита params → forward → loss → metrics, одна цепочка). -/
theorem all_channels_measure_same_path (m : ModelSpec (Fin n → ℝ) X' V)
    (o : ObjectiveSpec V) (S : TrainState n a r c k)
    (ds : List (X' × (V → ℝ))) (i : Fin 5) :
    measuredQuality m o S ds i = qualityThroughModel m o S.model.weights ds :=
  rfl

/-! ## (c) Привязка CanonicalTrainState к Transition и
StageSemantics -/

/-- Канонический шаг: `trainStep` на core носителе, router/quant/
trust и Hold-семантика `CanonicalTrainState` не трогаются. -/
noncomputable def canonicalTrainStep (cs : CanonicalTrainState n a e q r c k)
    (u : TrainingInput n c) : CanonicalTrainState n a e q r c k :=
  { cs with core := trainStep cs.core u }

/-- Проекция канонического шага — обычный `trainStep` (адаптер
точен: canonical-обёртка ничего не теряет и не добавляет). -/
theorem canonicalTrainStep_core (cs : CanonicalTrainState n a e q r c k)
    (u : TrainingInput n c) :
    (canonicalTrainStep cs u).core = trainStep cs.core u := rfl

/-- Hold откатывает каноническое состояние целиком и после шага
(full rollback сохраняется связкой). -/
theorem canonicalTrainStep_hold (cs : CanonicalTrainState n a e q r c k) :
    Hagi.State.applyStep cs Outcome.hold = cs :=
  hold_rollback_total cs

/-- Канонический параметрический шаг НЕ меняет quality-телеметр:
измерение качества — только событие `measureQuality` (запрет §5
перенесён на канонический носитель). -/
theorem canonicalTrainStep_quality_external
    (cs : CanonicalTrainState n a e q r c k) (u : TrainingInput n c) :
    (canonicalTrainStep cs u).core.qual = cs.core.qual :=
  trainStep_quality_unchanged cs.core u

/-- Объединяющий мост (a17 stage 1 главная цепочка): канонический
шаг + явное измерение через модель дают качество, равное
семантической метрике на обновлённых параметрах.  Полная цепь:
CanonicalTrainState → trainStep (params) → forward → loss → metric. -/
theorem canonical_step_measure_through_model (m : ModelSpec (Fin n → ℝ) X' V)
    (o : ObjectiveSpec V) (cs : CanonicalTrainState n a e q r c k)
    (u : TrainingInput n c) (ds : List (X' × (V → ℝ))) :
    (Hagi.State.measureQuality (canonicalTrainStep cs u).core
        (measuredQuality m o (canonicalTrainStep cs u).core ds)).qual
      = fun _ => qualityThroughModel m o
          (fun i => cs.core.model.weights i - u.eta * u.grad i) ds := rfl

/-- Проекция канонического состояния в ledger-поля GrowthState:
weights/params (через вложение emb), energy/budget/risk — из core.
Остальные поля GrowthState — нули/входы цикла: адаптер переносит
ИМЕННО то, что ведут оба носителя, не изобретая семантику
(честный объём, . -/
def toGrowthState (emb : (Fin n → ℝ) → X) (cs : CanonicalTrainState n a e q r c k)
    (sp : StageParams) (eff : StageEffects) : GrowthState X where
  weightDim := n
  weights := cs.core.model.weights
  params := emb cs.core.model.weights
  experts := 0
  energy := energy cs.core
  protectedRisk := cs.core.saf.risk
  budget := cs.core.res.budget
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := sp
  effects := eff

/-- Канонический шаг проецируется в ТОЧНЫЙ бюджетный закон ledger'а
GrowthState (списание opCost, как у `trainStep_budget`). -/
theorem toGrowthState_canonicalTrainStep_budget
    (emb : (Fin n → ℝ) → X) (cs : CanonicalTrainState n a e q r c k)
    (u : TrainingInput n c) (sp : StageParams) (eff : StageEffects) :
    (toGrowthState emb (canonicalTrainStep cs u) sp eff).budget
      = cs.core.res.budget - u.opCost := rfl

/-- Канонический шаг проецируется в ТОЧНЫЙ рисковый закон ledger'а
GrowthState (начисление opRisk, как у `trainStep_risk`). -/
theorem toGrowthState_canonicalTrainStep_risk
    (emb : (Fin n → ℝ) → X) (cs : CanonicalTrainState n a e q r c k)
    (u : TrainingInput n c) (sp : StageParams) (eff : StageEffects) :
    (toGrowthState emb (canonicalTrainStep cs u) sp eff).protectedRisk
      = cs.core.saf.risk + u.opRisk := rfl

end Hagi.Semantics
