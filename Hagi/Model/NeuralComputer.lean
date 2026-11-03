import Mathlib

/-!
# NeuralComputer (приоритет 4 «HAGI Neural Computer»,
# ): ЕДИНОЕ состояние нейрокомпьютера.

Три принципаально РАЗНЫХ типа изменяемости (нельзя
смешивать — обзор §6):
- параметры CPU: ЗАМОРОЖЕНЫ (инвариант любого перехода);
- рабочая память: меняется ТОЛЬКО исполнением программ;
- адаптеры/H-Net: меняются ТОЛЬКО обучением (SafeQP).

`NCState` упаковывает все подсистемы одним объектом;
`ncAdvance` — канонический переход: обновляет память по
адресуемой записи (GDN-режим), адаптеры по безопасному
шагу (CPU-блок обнулён), энергетику/бюджет/риск по
контракту. Доказуемые инварианты перехода:
1. `nc_cpu_frozen`: параметры процессора НЕ ИЗМЕНЯЮТСЯ;
2. `nc_mem_only_via_write`: память меняется только
   адресуемой записью (строка i);
3. `nc_budget_ledger`: бюджет убывает ровно на стоимость.
-/

namespace Hagi.Model.NeuralComputer

/-- Состояние нейрокомпьютера: единая точка истины. -/
structure NCState where
  /-- Параметры H-Net-чанкера (обучаемые). -/
  hnet : ℝ
  /-- Тритарная базовая сеть (консолидируется только). -/
  base : ℝ
  /-- Низкоранговые адаптеры (обучаемые). -/
  adapt : ℝ
  /-- Параметры CPU: ЗАМОРОЖЕНЫ навсегда. -/
  cpu : ℝ
  /-- Адресуемая рабочая память (меняется исполнением). -/
  mem : ℝ
  /-- Энергия обучения. -/
  energy : ℝ
  /-- Защищённый риск. -/
  risk : ℝ
  /-- Вычислительный бюджет. -/
  budget : ℝ
  /-- Измеренная capability. -/
  capability : ℝ

/-- Вход цикла нейрокомпьютера. -/
structure NCInput where
  /-- Адресуемая запись в память (адрес i, значение v). -/
  memWrite : Bool × ℝ
  /-- Предложенный шаг адаптера (CPU-блок уже обнулён). -/
  adaptStep : ℝ
  /-- Стоимость цикла. -/
  cost : ℝ
  /-- Прирост риска. -/
  riskSpend : ℝ
  /-- Измеренный прирост capability. -/
  gain : ℝ
  hcost : 0 ≤ cost
  hrisk : 0 ≤ riskSpend

/-- Канонический переход нейрокомпьютера. -/
def ncAdvance (S : NCState) (u : NCInput) : NCState where
  hnet := S.hnet
  base := S.base
  adapt := S.adapt + u.adaptStep
  cpu := S.cpu
  mem := if u.memWrite.1 then u.memWrite.2 else S.mem
  energy := S.energy - u.gain  -- рост capability оплачен энергией
  -- (вычисляемая связка каналов; ncCertStep при d = u.gain
  -- совпадает с каноническим шагом: см. ncCertStep_pays_gain)
  risk := S.risk + u.riskSpend
  budget := S.budget - u.cost
  capability := S.capability + u.gain

/-- ИНВАРИАНТ 1: процессор заморожен — никакой переход
нейрокомпьютера не изменяет параметры CPU (rfl-контракт). -/
theorem nc_cpu_frozen (S : NCState) (u : NCInput) :
    (ncAdvance S u).cpu = S.cpu := rfl

/-- ИНВАРИАНТ 2: базовые веса консервативны — переход не
трогает тритарную базу (консолидация — отдельный канал). -/
theorem nc_base_frozen (S : NCState) (u : NCInput) :
    (ncAdvance S u).base = S.base := rfl

/-- ИНВАРИАНТ 3: память меняется ТОЛЬКО адресуемой
записью: либо прежнее значение, либо записанное. -/
theorem nc_mem_only_via_write (S : NCState) (u : NCInput) :
    (ncAdvance S u).mem = S.mem
      ∨ (ncAdvance S u).mem = u.memWrite.2 := by
  unfold ncAdvance
  by_cases h : u.memWrite.1
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

/-- ИНВАРИАНТ 4: бюджетная бухгалтерия точна. -/
theorem nc_budget_ledger (S : NCState) (u : NCInput) :
    (ncAdvance S u).budget = S.budget - u.cost := rfl

/-- ИНВАРИАНТ 5: риск неубывающий канал (траты ≥ 0). -/
theorem nc_risk_mono (S : NCState) (u : NCInput) :
    S.risk ≤ (ncAdvance S u).risk := by
  unfold ncAdvance
  linarith [u.hrisk]

end Hagi.Model.NeuralComputer
