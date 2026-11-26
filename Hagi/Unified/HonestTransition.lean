import Mathlib.Tactic
import Hagi.Cert.Core
import Hagi.Cert.StepGen

/-!
# HonestTransition

Дефект старого `CertifiedTransition.progress`: оно
сертифицирует ПОЛОЖИТЕЛЬНОСТЬ ВЫЧИСЛЯЕМОГО ПОКАЗАТЕЛЯ
(verify.decrease), а не реальное улучшение модели.
Контрпример: E(S)=0, G_grow=1,
E_compress=100 — положительный сертификат при росте
энергии.

`HonestTransition` устраняет разрыв по построению:
спуск — не вычисляемый показатель, а ДОКАЗАННАЯ связь
`objective S' ≤ objective S - objectiveDrop` между
реальным исполнением и реальной функцией.

Ключевые гарантии:
1. `honest_actual_drop`: из сертификата следует точный
   реальный спуск (нельзя сертифицировать рост);
2. `honest_telescope`: два последовательных честных
   перехода кумулятивны (обструкция двухшаговости старой
   GrowthState-семантики здесь НЕВОЗМОЖНА по построению —
   эффекты не хранятся в состоянии);
3. `honest_two_steps_existent`: конкретный свидетель
   (квадратичная машина) двух продуктивных переходов.
-/

namespace Hagi.Unified.HonestTransition

/-! ## Словарь перегрузок: `HonestTransition`, `CertStep`
Канон-носитель честного перехода — этот файл. Одноимённый
`CertStep` здесь — адаптация ядра `Hagi.Cert.Core` к
Unified-слою; исходное определение искать в `Hagi.Cert.Core`.
-/

variable {S : Type*}

/-- Честный переход: спуск связан с objective-функцией
зависимым доказательством, не с показателем. -/
structure HonestTransition (obj : S → ℝ)
    (s s' : S) (riskSpend riskLim budgetSpend : ℝ)
    (budget' : ℝ) where
  /-- Реальное уменьшение (нижняя сертифицированная
  граница). -/
  objectiveDrop : ℝ
  objectiveDrop_pos : 0 < objectiveDrop
  /-- Главное: реальный спуск, выведенный из исполнения. -/
  actualDescent : obj s' ≤ obj s - objectiveDrop
  /-- Риск шага ограничен. -/
  riskBound : riskSpend ≤ riskLim
  /-- Бюджет шага ограничен, остаток неотрицателен. -/
  budgetBound : 0 ≤ budget'

/-- Сертификат ⇒ реальное строгое убывание
(заключение ссылается на поле сертификата:
положительный спуск-сертификат невозможен при росте). -/
theorem honest_actual_drop (obj : S → ℝ) (s s' : S)
    (rs rl bs b' : ℝ)
    (T : HonestTransition obj s s' rs rl bs b') :
    obj s' < obj s ∧ 0 < T.objectiveDrop := by
  exact ⟨by
    have h1 := T.actualDescent
    have h2 := T.objectiveDrop_pos
    linarith, T.objectiveDrop_pos⟩

/-- Телескоп: два честных перехода кумулятивны.
Сравни с corePremises_two_step_decrease_nonpos старой
семантики: здесь противоречие НЕВОЗМОЖНО, т.к. каждый
переход несёт собственное доказательство спуска. -/
theorem honest_telescope (obj : S → ℝ) (s0 s1 s2 : S)
    (rs1 rl1 bs1 b1 rs2 rl2 bs2 b2 : ℝ)
    (T1 : HonestTransition obj s0 s1 rs1 rl1 bs1 b1)
    (T2 : HonestTransition obj s1 s2 rs2 rl2 bs2 b2) :
    obj s2 ≤ obj s0 - (T1.objectiveDrop + T2.objectiveDrop) := by
  have h1 := T1.actualDescent
  have h2 := T2.actualDescent
  linarith

/-- Конкретный свидетель двух продуктивных честных
переходов: E(w)=w², траектория 2 → 1 → ½:
E: 4 → 1 → ¼, точные спуски 3 и ¾. -/
noncomputable def quadObj (w : ℝ) : ℝ := w * w

theorem honest_two_steps_existent :
    ∃ (d1 d2 : ℝ), 0 < d1 ∧ 0 < d2 ∧
      quadObj 1 ≤ quadObj 2 - d1 ∧
      quadObj (1 / 2) ≤ quadObj 1 - d2 := by
  refine ⟨3, 3 / 4, by norm_num, by norm_num, ?_, ?_⟩ <;> norm_num [quadObj]


/-! ### CertStep — минимальное ядро сертификата → единая запись StepRecord

Ядро {drop > 0, obj s' ≤ obj s − drop}
соединяется с единой записью журнала `Hagi.Cert.StepRecord` (drop-ядро + свободная
телеметрия budget/risk/δ) этого файла. Старое имя — deprecated-алиас; все
сертификаты HAGI обязаны давать мост в StepRecord (toRecord/toCertStep). -/

/-- ЕДИНАЯ запись журнала сертифицированного шага: drop-ядро + свободная
телеметрия budget/risk/δ. -/
@[deprecated Hagi.Cert.StepRecord (since := "2026-11-19")]
abbrev CertStep (obj : S → ℝ) (s s' : S) : Type :=
  Hagi.Cert.StepRecord obj s s'

/-- HonestTransition → StepRecord (риск/бюджет — в телеметрии
записи: spend-семантика границ остаётся в самом переходе). -/
def HonestTransition.toRecord {obj : S → ℝ} {s s' : S}
    {rs rl bs b' : ℝ} (T : HonestTransition obj s s' rs rl bs b') :
    Hagi.Cert.StepRecord obj s s' where
  drop := T.objectiveDrop
  drop_pos := T.objectiveDrop_pos
  descent := T.actualDescent
  budgetSpend := bs
  riskSpend := rs
  delta := 0

/-- HonestTransition → CertStep (риск/бюджет отбрасываются —
они не входят в ядро спуска). -/
def HonestTransition.toCertStep {obj : S → ℝ} {s s' : S}
    {rs rl bs b' : ℝ} (T : HonestTransition obj s s' rs rl bs b') :
    CertStep obj s s' := T.toRecord

/-! ### S3-адаптер: HonestTransition → каноническое ядро Hagi.Cert

Adapters-слой
(`Hagi/Cert/Adapters.lean`) намеренно импортирует только Cert.Core и
не может видеть HonestTransition; Unified-сторона имела мост лишь в
МИНИМАЛЬНОЕ ядро CertStep. Ниже — мост в ПОЛНОЕ каноническое ядро
`Hagi.Cert.CertStep` с бюджетным/рисковым учётом: реальные поля
перехода (objectiveDrop, actualDescent, траты rs/bs) pulled в ядро
через premise-form пучок метрик. -/

/-- С3-адаптер: честный переход + пучок системных метрик, чья
цель совпадает с целью перехода, бюджет убывает ровно на
budgetSpend перехода (остаток b' ≥ 0), а риск-уровень — это
remaining-risk, полностью списываемый тратой rs (остаток 0),
собираются в канонический `Hagi.Cert.CertStep`.

Посылки-моделирование (честно, явно):
* `hobj : M.objective = obj` — метрики измеряют ту же цель;
* `hbud : M.budget s = b' + bs`, `hbud' : M.budget s' = b'` —
  бюджет тратится ровно на bs, остаток b' неотрицателен
  (hT.budgetBound);
* `hrisk : M.risk s = rs`, `hrisk' : M.risk s' = 0` — риск-уровень
  интерпретируется как remaining-risk, списываемый полностью
  (выбор в пользу простоты; альтернативный ненулевой остаток
  требует лишь замены hrisk' на пару равенств). -/
def HonestTransition.toKernelCertStep {S TaskId : Type*}
    {obj : S → ℝ} {s s' : S} {rs rl bs b' : ℝ}
    (hT : HonestTransition obj s s' rs rl bs b')
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (hobj : M.objective = obj)
    (hbud : M.budget s = b' + bs) (hbud' : M.budget s' = b')
    (hrisk : M.risk s = rs) (hrisk' : M.risk s' = 0)
    (obl : Hagi.Cert.StepObligations TaskId)
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStep M obl s s' where
  drop := hT.objectiveDrop
  drop_pos := hT.objectiveDrop_pos
  descent := by rw [hobj]; exact hT.actualDescent
  budgetSpend := bs
  budget_next := by rw [hbud, hbud']; linarith [hT.budgetBound]
  budget_nonneg := by rw [hbud']; exact hT.budgetBound
  riskSpend := rs
  risk_next := by rw [hrisk, hrisk']; ring
  risk_nonneg := by rw [hrisk']
  floorsKept := hfloors

/-! ### Адаптер: HonestTransition → общее ядро CertStepGen

Переход в ЕДИНОЕ общее ядро
`Hagi.Cert.CertStepGen` (общий индекс задач, остаток риска —
ПОЛЕ, свёрнутый δ-бюджет). Вместо посылки
`hrisk' : M.risk s' = 0` (остаток риска запинен в ноль —
тратить риск мог только последний шаг траектории) — пара
`hrisk : M.risk s = rs + riskRem`, `hrisk' : M.risk s' = riskRem`
со СВОБОДНЫМ параметром `riskRem` (нулевой остаток — частный
случай `riskRem := 0`; неотрицательность остатка — явная посылка
`hrem`, в самом HonestTransition её нет). -/

/-- честный переход собирается в общее ядро `CertStepGen`:
остаток риска — свободный параметр (0-пиннинг снят),
δ-канал нулевой на тривиальном носителе `fun _ => 0`. -/
def HonestTransition.toCertStepGen {S TaskId : Type*}
    {obj : S → ℝ} {s s' : S} {rs rl bs b' riskRem : ℝ}
    (hT : HonestTransition obj s s' rs rl bs b')
    (M : Hagi.Cert.SystemMetrics S TaskId)
    (hobj : M.objective = obj)
    (hbud : M.budget s = b' + bs) (hbud' : M.budget s' = b')
    (hrisk : M.risk s = rs + riskRem) (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (obl : Hagi.Cert.StepObligations TaskId)
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStepGen M obl (fun _ => 0) s s' where
  drop := hT.objectiveDrop
  drop_pos := hT.objectiveDrop_pos
  descent := by rw [hobj]; exact hT.actualDescent
  budgetSpend := bs
  budget_next := by rw [hbud, hbud']; linarith [hT.budgetBound]
  budget_nonneg := by rw [hbud']; exact hT.budgetBound
  riskSpend := rs
  riskRem := riskRem
  risk_next := hrisk'
  risk_split := hrisk
  risk_nonneg := hrem
  delta := 0
  delta_next := by simp
  delta_nonneg := by norm_num
  floorsKept := hfloors

end Hagi.Unified.HonestTransition
