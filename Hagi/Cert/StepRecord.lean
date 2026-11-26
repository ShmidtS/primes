/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Cert.Telescope
import Mathlib.Tactic

set_option linter.style.header false
set_option relaxedAutoImplicit false

/-!
# StepRecord — единая запись журнала одного шага

Единая запись журнала одного шага: drop-ядро (единственный закон —
спад) + телеметрические скаляры (budgetSpend / riskSpend / delta —
данные без законов; законы остаются в cert-носителях). Телескоп —
один инстанс `AdditiveLedger`.

Модуль — лист (не импортирует cert-структуры); мосты `toRecord` для
ядра живут в `Hagi.Cert.Core`/`StepGen`.
-/

namespace Hagi.Cert

variable {S : Type*}

/-- Запись журнала одного сертифицированного шага: сертифицированная
нижняя граница спада с законом спада + телеметрия трат как данные
(законы проверяют носители). -/
structure StepRecord (obj : S → ℝ) (s s' : S) where
  /-- Сертифицированная нижняя граница спада objective. -/
  drop : ℝ
  drop_pos : 0 < drop
  /-- Obj-chain: реальный спуск из исполнения (единственный закон записи). -/
  descent : obj s' ≤ obj s - drop
  /-- Телеметрия: заявленная трата вычислительного бюджета (данные). -/
  budgetSpend : ℝ
  /-- Телеметрия: заявленная трата рискового бюджета (данные). -/
  riskSpend : ℝ
  /-- Телеметрия: заявленная трата δ-бюджета ложного коммита (данные). -/
  delta : ℝ

/-- Drop-only конструктор: телеметрия обнулена (для носителей без
бюджетного/рискового/δ-канала). -/
def StepRecord.core {obj : S → ℝ} {s s' : S} (drop : ℝ) (hpos : 0 < drop)
    (hdesc : obj s' ≤ obj s - drop) : StepRecord obj s s' where
  drop := drop
  drop_pos := hpos
  descent := hdesc
  budgetSpend := 0
  riskSpend := 0
  delta := 0

/-! ## Телескоп -/

/-- `StepRecord` списывает certified drop из objective (≤-закон). -/
instance stepRecord_objective (obj : S → ℝ) :
    AdditiveLedger S obj (StepRecord obj) where
  spend c := c.drop
  step_descend c := c.descent

/-- Телескоп журнала: терминальный objective ≤ начального минус сумма
записанных drop'ов — специализация `additive_ledger_telescope`. -/
theorem stepRecord_telescope {obj : S → ℝ}
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, StepRecord obj (t j) (t (j + 1))) :
    obj (t n) ≤ obj (t 0)
      - ∑ j ∈ Finset.range n, (steps j).drop :=
  additive_ledger_telescope n t steps

end Hagi.Cert
