import Mathlib


/-!
# TrainState — единая модель состояния обучаемой системы (Gate 2, спека §4)

Одно каноническое состояние: шесть подсостояний (§4.1), раздельные
функции objective/capability/quality/risk/cost/budget/energy (§4.3),
качество — функция состояния (§4.2).
-/

namespace Hagi.State

/-! ### Подсостояния (§4.1) -/

/-- Параметры модели: основная сеть, адаптеры, архитектурная версия. -/
structure ModelState (n a : ℕ) where
  /-- Основные параметры (веса). -/
  weights : Fin n → ℝ
  /-- Параметры адаптеров (низкоранговая дельта). -/
  adapters : Fin a → ℝ
  /-- Архитектурная версия состояния (монотонный счётчик). -/
  version : ℕ

/-- Состояние оптимизатора: моменты и расписание. -/
structure OptimizerState (n : ℕ) where
  /-- Первый момент (momentum/Adam m). -/
  m : Fin n → ℝ
  /-- Второй момент (Adam v). -/
  v : Fin n → ℝ
  /-- Номер шага расписания. -/
  schedStep : ℕ

/-- Память: адресуемая RAM-матрица и низкоранговые блоки. -/
structure MemoryState (r c k : ℕ) where
  /-- Адресуемая память (строки — адреса). -/
  ram : Matrix (Fin r) (Fin c) ℝ
  /-- Низкоранговые блоки (консолидированные): k строк. -/
  lowRank : Matrix (Fin k) (Fin c) ℝ
  /-- Состояние консолидации: число консолидированных записей. -/
  consolidated : ℕ

/-- Ресурсы: бюджет, FLOPs, память GPU, задержка. -/
structure ResourceState where
  /-- Оставшийся вычислительный бюджет. -/
  budget : ℝ
  /-- Израсходованные FLOPs. -/
  flops : ℝ
  /-- Занятая память GPU. -/
  gpuMem : ℝ
  /-- Измеренная задержка последней операции. -/
  latency : ℝ

/-- Безопасность: риск, лимиты, защищённые метрики. -/
structure SafetyState where
  /-- Накопленный риск. -/
  risk : ℝ
  /-- Риск-лимит траектории. -/
  riskLim : ℝ
  /-- Защищённые каналы качества (индексы в QualityVector). -/
  protectedChannels : Finset (Fin 5)

/-- Качество: пять каналов с однозначной семантикой:
0 = математические задачи, 1 = retrieval, 2 = программирование,
3 = сохранение знаний, 4 = обобщение. -/
abbrev QualityVector := Fin 5 → ℝ

/-- Каналы качества (документация семантики индексов). -/
def qMath : Fin 5 := 0
def qRetrieval : Fin 5 := 1
def qCode : Fin 5 := 2
def qRetention : Fin 5 := 3
def qGeneralization : Fin 5 := 4

/-- Полное состояние обучаемой системы (§4.1). -/
structure TrainState (n a r c k : ℕ) where
  /-- Параметры модели. -/
  model : ModelState n a
  /-- Оптимизатор. -/
  opt : OptimizerState n
  /-- Память. -/
  mem : MemoryState r c k
  /-- Ресурсы. -/
  res : ResourceState
  /-- Безопасность. -/
  saf : SafetyState
  /-- Качество (оценки каналов) — ВНЕШНИЙ ИЗМЕРЕННЫЙ телеметр:
  входит в состояние (§4.1), но НЕ может задаваться переходом
  произольно — изменение качества связывается с переходом только
  сертификатом уровня Transition (Gate 3, §5). -/
  qual : QualityVector

/-! ### Раздельные функции состояния (§4.3) -/

section Functions
variable {n a r c k : ℕ} (S : TrainState n a r c k)

/-- Энергия состояния (поддерживающая цель): сумма квадратов
параметров — математически однозначная, НЕ совпадает по определению
ни с качеством, ни с бюджетом. -/
def energy (S : TrainState n a r c k) : ℝ :=
  ∑ i, S.model.weights i ^ 2 + ∑ i, S.model.adapters i ^ 2

/-- Capability: число консолидированных записей (измеримо из
состояния памяти). -/
def capability (S : TrainState n a r c k) : ℕ := S.mem.consolidated

/-- Риск состояния: накопленный risk из SafetyState. -/
def riskOf (S : TrainState n a r c k) : ℝ := S.saf.risk

/-- Бюджет состояния. -/
def budgetOf (S : TrainState n a r c k) : ℝ := S.res.budget

/-- Стоимость (израсходованные FLOPs). -/
def costOf (S : TrainState n a r c k) : ℝ := S.res.flops

/-- Качество: покомпонентный вектор из состояния (§4.2:
качество — ФУНКЦИЯ состояния, не независимая последовательность). -/
def evaluate (S : TrainState n a r c k) : QualityVector := S.qual

end Functions

/-! ### Floor-контракт (§4.2) -/

/-- Покомпонентное удержание floor на состоянии S. -/
def FloorHeld (S : TrainState n a r c k) (floor : QualityVector) :
    Prop := ∀ i, floor i ≤ evaluate S i

/-- Скалярный агрегат разрешён для маршрутизации, но НЕ заменяет
покомпонентный контроль (§4.2): определён отдельно. -/
noncomputable def qualityScalar (S : TrainState n a r c k) : ℝ :=
  ∑ i, evaluate S i

/-- Скалярная сумма floor'ов ≤ скаляр качества НЕ влечёт
покомпонентное удержание (§4.2): явный контрпример — floor с одним
нулевым каналом и качество, сконцентрированное в другом канале. -/
example : ¬ ∀ (S : TrainState 0 0 0 0 0) (floor : QualityVector),
    (∑ i, floor i ≤ qualityScalar S) → FloorHeld S floor := by
  intro h
  -- качество: всё в канале 0, остальные нули
  let md : ModelState 0 0 := ⟨fun _ => 0, fun _ => 0, 0⟩
  let op : OptimizerState 0 := ⟨fun _ => 0, fun _ => 0, 0⟩
  let mm : MemoryState 0 0 0 :=
    ⟨Matrix.of fun _ _ => 0, Matrix.of fun _ _ => 0, 0⟩
  let rs : ResourceState := ⟨0, 0, 0, 0⟩
  let sf : SafetyState := ⟨0, 0, ∅⟩
  let S : TrainState 0 0 0 0 0 :=
    ⟨md, op, mm, rs, sf, fun i => if i = 0 then 5 else 0⟩
  let floor : QualityVector := fun i => if i = 1 then 5 else 0
  have hsum : ∑ i, floor i ≤ qualityScalar S := by
    simp [floor, S, qualityScalar, evaluate]
  have hcontra := h S floor hsum
  have h1 : floor 1 ≤ evaluate S 1 := hcontra 1
  simp [floor, S, evaluate] at h1
  norm_num at h1

end Hagi.State
