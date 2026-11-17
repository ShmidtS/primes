import Hagi.State.TrainState
import Hagi.Cert.StepGen

/-!
# CanonicalTrainState — единое каноническое состояние обучения
с инвариантом полного откката (user audit 3.1, C363)

Контракт поверх Freeze-locked `Hagi.State.TrainState` (§4.1):

* `CanonicalTrainState` — канонический носитель: ВСЁ состояние
  целиком — веса, Adam-буферы оптимизатора (momentum/variance),
  память, budget/risk-ledger (через `core : TrainState`), плюс
  router/expert-гейты, параметры квантования и trust-ledger;
* `Outcome`/`applyStep` — семантика шага: `Progress s'` коммитит
  новое состояние, `Hold` откатывает ВСЁ состояние целиком;
* `hold_rollback_total` — инвариант полного откката: Hold
  возвращает состояние в точности (включая momentum/variance-буферы
  оптимизатора — частичный откат невыразим по построению);
* `fullObjective` — измеряемая цель НА ВСЁМ СОСТОЯНИИ: энергия весов
  PLUS норма буферов оптимизатора, так что сертифицированный Progress
  не может спрятать дрейф буферов за спуск весов;
* `FullStepCert` + `fullStepCert_toCertStepGen` — сертификат шага,
  связывающий ПОЛНОЕ состояние с общим ядром `Hagi.Cert.CertStepGen`
  (C345): один адаптер показывает, что ядро может вести это
  состояние.

Честный объём (honest scope): это ОПРЕДЕЛЕНИЕ КОНТРАКТА + инвариант,
НЕ миграция. Кандидаты на миграцию (последующие транши):
`Hagi.Model.EnergyReasoning.CRAMState` (C267), потребители
`Hagi.System.GrowthState`, файлы `Hagi.Model.*` — всё это остаётся
раздельным и не трогается здесь.
-/

set_option relaxedAutoImplicit false

namespace Hagi.State

/-! ### Канонический носитель -/

variable {n a e q r c k : ℕ}
variable {TaskId : Type*}

/-- ЕДИНОЕ каноническое состояние обучения (audit 3.1): полный
носитель — всё, что откатывается при Hold, целиком. Шесть подсостояний
§4.1 (веса, Adam-буферы, память, бюджет, риск, качество) — через
Freeze-locked `core : TrainState`; три поля аудита, которых в TrainState
нет: router/expert-гейты, параметры квантования, trust-ledger. -/
structure CanonicalTrainState (n a e q r c k : ℕ) where
  /-- Шесть подсостояний §4.1: веса, Adam m/v-буферы, память,
  budget/risk-ledger, качество. -/
  core : TrainState n a r c k
  /-- Router/expert-гейты (по экспертам). -/
  router : Fin e → ℝ
  /-- Параметры квантования. -/
  quant : Fin q → ℝ
  /-- Trust-ledger (накопленное доверие). -/
  trust : ℝ

/-! ### Семантика шага: Progress | Hold -/

/-- Исход шага: Progress с новым состоянием или Hold. -/
inductive Outcome (S : Type*) where
  /-- Коммит: новое состояние целиком. -/
  | progress : S → Outcome S
  /-- Откат: состояние сохраняется целиком. -/
  | hold : Outcome S

/-- Шаг обучения: Progress подставляет новое состояние ЦЕЛИКОМ,
Hold возвращает прежнее состояние ЦЕЛИКОМ. -/
def applyStep (s : S) (o : Outcome S) : S :=
  match o with
  | Outcome.progress s' => s'
  | Outcome.hold => s

/-- ИНВАРИАНТ ПОЛНОГО ОТКАТА (audit 3.1): при Hold откатывается ВСЁ
состояние целиком — включая momentum/variance-буферы оптимизатора,
router/quant/trust-ledger. Частичный откат невыразим: `applyStep` на
Hold возвращает носитель по определению, никакое подмножество полей
не обновляется. -/
theorem hold_rollback_total (s : S) : applyStep s Outcome.hold = s := rfl

/-! ### Полная измеряемая цель: буферы включены -/

/-- Норма буферов оптимизатора (momentum + variance, Adam m/v). -/
def bufferNorm (s : CanonicalTrainState n a e q r c k) : ℝ :=
  ∑ i, |s.core.opt.m i| + ∑ i, |s.core.opt.v i|

/-- ПОЛНАЯ измеряемая цель: энергия весов ПЛЮС норма буферов
оптимизатора. Сертифицированный спуск по `fullObjective` — спуск,
измеренный НА ВСЁМ состоянии: дрейф momentum/variance-буферов не
спрятать за спуск весов. -/
def fullObjective (s : CanonicalTrainState n a e q r c k) : ℝ :=
  energy s.core + bufferNorm s

/-! ### Сертификат полного шага -/

/-- Сертификат Progress-шага на ПОЛНОМ состоянии (premise-form,
паттерн C278/C279): положительный drop, спуск полной цели
(веса + буферы), точные бюджетный и риск-законы ledger'а. -/
structure FullStepCert (s s' : CanonicalTrainState n a e q r c k) where
  /-- Заявленный спуск полной цели. -/
  drop : ℝ
  /-- Спуск положителен. -/
  drop_pos : 0 < drop
  /-- Спуск НА ПОЛНОМ состоянии: веса И буферы включены. -/
  descent : fullObjective s' ≤ fullObjective s - drop
  /-- Бюджетная трата (вычислительный канал). -/
  budgetSpend : ℝ
  /-- Точный бюджетный закон ledger'а. -/
  budget_next : s'.core.res.budget = s.core.res.budget - budgetSpend
  /-- Остаточный бюджет неотрицателен. -/
  budget_nonneg : 0 ≤ s'.core.res.budget
  /-- Риск-трата (независимый канал). -/
  riskSpend : ℝ
  /-- Остаток риска (свободный, не 0-пиннинг C254). -/
  riskRem : ℝ
  /-- Риск-закон следующего состояния. -/
  risk_next : s'.core.saf.risk = riskRem
  /-- Точное расщепление риска в ledger'е. -/
  risk_split : s.core.saf.risk = riskSpend + riskRem
  /-- Остаток риска неотрицателен. -/
  risk_nonneg : 0 ≤ riskRem

/-- Сертифицированный Progress-шаг даёт спуск ПОЛНОЙ цели. -/
theorem fullStepCert_descent (s s' : CanonicalTrainState n a e q r c k)
    (hcert : FullStepCert s s') :
    fullObjective s' ≤ fullObjective s - hcert.drop :=
  hcert.descent

/-! ### Адаптер в общее ядро CertStepGen (C345) -/

/-- Метрики канонического состояния для общего ядра: objective —
ПОЛНАЯ цель (буферы включены), budget/risk — из ledger'а ядра
`core : TrainState`; тег задачи — константа потребителя. -/
noncomputable def trainMetrics (tag : TaskId) :
    Hagi.Cert.SystemMetrics (CanonicalTrainState n a e q r c k) TaskId where
  objective := fullObjective
  risk := fun s => s.core.saf.risk
  budget := fun s => s.core.res.budget
  task := fun _ => tag

/-- АДАПТЕР (TaskId-параметризован): сертифицированный Progress-шаг
на каноническом состоянии — шаг общего ядра `Hagi.Cert.CertStepGen`.
Один инстанс показывает, что ядро может вести это состояние;
delta-канал — нулевой уровень (посылки потребителя). -/
def fullStepCert_toCertStepGen {s s' : CanonicalTrainState n a e q r c k}
    (hcert : FullStepCert s s') (tag : TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (hfloors : Hagi.Cert.FloorsKept (trainMetrics (n := n) tag) obl s') :
    Hagi.Cert.CertStepGen (trainMetrics (n := n) tag) obl
      (fun _ => 0) s s' where
  drop := hcert.drop
  drop_pos := hcert.drop_pos
  descent := hcert.descent
  budgetSpend := hcert.budgetSpend
  budget_next := hcert.budget_next
  budget_nonneg := hcert.budget_nonneg
  riskSpend := hcert.riskSpend
  riskRem := hcert.riskRem
  risk_next := hcert.risk_next
  risk_split := hcert.risk_split
  risk_nonneg := hcert.risk_nonneg
  delta := 0
  delta_next := by simp
  delta_nonneg := by norm_num
  floorsKept := hfloors

end Hagi.State
