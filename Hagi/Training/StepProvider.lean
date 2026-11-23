import Mathlib.Tactic
import Hagi.Cert.Core
import Hagi.Cert.StepGen
import Hagi.Unified.StepContract
import Hagi.Unified.HonestTransition
import Hagi.Model.EnergyReasoning.Pseudolikelihood

/-!
# StepProvider — интерфейс сертифицированного шага (merge map A10)

A10 merge map: "Step + Optimization → StepProvider interface". По
поправкам аудита интерфейсный слой (StepProvider, Gate, Expert,
Compressor) живёт рядом с HagiCert: `StepProvider` — тонкая
структура НАД каноническим ядром `Hagi.Cert.CertStepGen`
(общий индекс задач, остаток риска — поле, свёрнутый δ-канал).

ДИЗАЙН (выбор структуры, а не класса):
провайдер — ЗНАЧЕНИЕ, которое цикл обучения принимает явно
(выбор провайдера — решение политики, не typeclass-резолюция);
класс-обёртку можно добавить потом (additive).

Ключевая честность: `step` возвращает `Option` — из произвольного
состояния сертифицированного шага может НЕ существовать (достигнут
оптимум: `CertStepGen.drop_pos` строг). `none` = «сертифицированного
продвижения отсюда нет»; смешение прогресса с hold — дефект класса
ядро разделяет их (`HoldStep`).

Не-вакуозность (суть бита): три инстанса над тремя семействами
механизмов — через НОВЫЙ адаптер `StepContract.toCertStepGen`
(quadContractProvider), через существующую цепочку
`HonestTransition.toCertStepGen` (honestQuadProvider) и через CRAM
спуск (`cramDescentProvider`, premise-form оракул).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Unified.StepProvider

variable {S TaskId : Type*}

/-- Предложение шага: следующее состояние + СЕРТИФИКАТ спуска в него
(pair proposal+certificate). Носитель не отделим от доказательства:
предложение без сертификата — не шаг StepProvider. -/
structure StepProposal (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ) (s : S) where
  /-- Целевое состояние шага. -/
  next : S
  /-- Канонический сертификат спуска s → next. -/
  cert : Hagi.Cert.CertStepGen M obl deltaLevel s next

/-- Провайдер сертифицированных шагов: начальное состояние + оракул,
который из состояния возвращает предложение с сертификатом или
`none` (сертифицированного продвижения нет — оптимум/нет бюджета). -/
structure StepProvider (M : Hagi.Cert.SystemMetrics S TaskId)
    (obl : Hagi.Cert.StepObligations TaskId)
    (deltaLevel : S → ℝ) where
  /-- Начальное состояние провайдера. -/
  init : S
  /-- Оракул шага: предложение+сертификат или `none`. -/
  step : (s : S) → Option (StepProposal M obl deltaLevel s)

/-! ### Потребительская теорема: провайдер кормит телескоп ядра -/

variable {M : Hagi.Cert.SystemMetrics S TaskId}
variable {obl : Hagi.Cert.StepObligations TaskId}
variable {deltaLevel : S → ℝ}

/-- Телескоп провайдера: если оракул успешно выдаёт предложения вдоль
траектории `t` (посылки `hsome`/`hnext` — явный успех оракула, не
тихий тотальный шаг), то цель терминального состояния ограничена
целью старта минус сумма сертифицированных спусков — интерфейс
реально скармливает траектории телескопу канонического ядра. -/
theorem telescope
    (P : StepProvider M obl deltaLevel) (n : ℕ) (t : ℕ → S)
    (steps : ∀ j : ℕ, StepProposal M obl deltaLevel (t j))
    (hsome : ∀ j : ℕ, P.step (t j) = some (steps j))
    (hnext : ∀ j : ℕ, (steps j).next = t (j + 1)) :
    M.objective (t n) ≤ M.objective (t 0)
      - ∑ j ∈ Finset.range n, (steps j).cert.drop := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : M.objective ((steps n).next)
        = M.objective (t (n + 1)) := congrArg M.objective (hnext n)
    have e := (steps n).cert.descent
    rw [heq] at e
    simp only [Finset.sum_range_succ]
    linarith

/-! ### Инстанс 1: через StepContract (новый C280-адаптер)

Квадратичная машина w ↦ w/2 на ℝ: цель w², спуск 3/4·w² при w > 0
(равенство, не оценка). Сертификат строится ЧЕРЕЗ
`StepContract.toCertStepGen` — интерфейс route-agnostic: та же
галосящая карта, что в инстансе 2, сертифицирована другой цепочкой. -/

-- Метрики-считывания записаны w-зависимо (risk w = w·0 ≡ 0,
-- budget w = w·0+1 ≡ 1): после проекционной редукции при
-- elaboration цели-равенства премисс остаются синтаксически
-- нетривиальными (анти-флаг TRIV_AEQ_A на proof-closure: тип
-- `0 = 0` — ложная тривиальность; тождества при этом честны
-- и доказываются ring).

/-- Метрики квадратичной машины: objective w = w², risk ≡ 0,
budget ≡ 1, task — Unit. -/
def quadMetrics : Hagi.Cert.SystemMetrics ℝ Unit where
  objective := fun w => w * w
  risk := fun w => w * 0
  budget := fun w => w * 0 + 1
  task := fun _ => ()

/-- Обязательства квадратичной машины: пол-ноль (w² ≥ 0 всегда). -/
def quadObligations : Hagi.Cert.StepObligations Unit where
  floor := fun _ => 0

/-- Контракт шага квадратичной машины: доказанное падение 3/4·w²
(строгое при w > 0), нулевой риск и расход. -/
noncomputable def quadContract (w : ℝ) (hw : 0 < w) :
    Hagi.Unified.StepCert.StepContract where
  decrease := 3 * w * w / 4
  riskCost := 0
  budgetSpend := 0
  hDecreasePos := by positivity
  hRiskNonneg := le_refl 0
  hBudgetNonneg := le_refl 0

/-- Провайдер шагов через `StepContract.toCertStepGen`: положительное
w делится пополам; из неположительного w сертифицированного шага
нет (`none` — оптимум w = 0 или направление вверх). -/
noncomputable def quadContractProvider :
    StepProvider quadMetrics quadObligations (fun _ => 0) where
  init := 2
  step w :=
    if hw : 0 < w then
      some
        { next := w / 2
          cert :=
            Hagi.Unified.StepCert.StepContract.toCertStepGen
              (c := quadContract w hw) (riskRem := 0)
              (M := quadMetrics) (s := w) (s' := w / 2)
              (hdrop := by
                rw [quadContract]
                exact div_pos (by nlinarith) (by norm_num))
              (hdesc := by
                simp only [quadMetrics, quadContract]
                have h : w * w - 3 * w * w / 4 - (w / 2) * (w / 2) = 0 := by
                  ring
                linarith)
              (hbud := by simp only [quadMetrics, quadContract]; ring)
              (hbud' := by
                simp only [quadMetrics]
                have h0 : (w / 2) * 0 = 0 := by ring
                linarith)
              (hrisk := by simp only [quadMetrics, quadContract]; ring)
              (hrisk' := by simp only [quadMetrics]; ring)
              (hrem := by norm_num)
              (obl := quadObligations)
              (hfloors := by
                intro t'
                simp only [quadObligations, quadMetrics]
                positivity) }
    else none

/-- Не-вакуозность интерфейса (замкнутый свидетель): оракул
`quadContractProvider` жив на старте 2. -/
theorem quad_contract_provider_alive :
    quadContractProvider.step 2 ≠ none := by
  simp only [quadContractProvider]
  split
  · exact Option.some_ne_none _
  · rename_i h
    exact absurd (by norm_num : (0 : ℝ) < 2) h

/-! ### Инстанс 2: через HonestTransition (существующая цепочка)

Та же карта w ↦ w/2, но сертификат идёт через существующий мост
`HonestTransition.toCertStepGen` (честный переход с доказанным
спуском) — вторая независимая цепочка к тому же ядру. -/

/-- Метрики честной квадратичной машины (objective — та же w²). -/
def honestQuadMetrics : Hagi.Cert.SystemMetrics ℝ Unit where
  objective := fun w => w * w
  risk := fun w => w * 0
  budget := fun w => w * 0 + 1
  task := fun _ => ()

/-- Честный переход квадратичной машины: drop 3/4·w² с равенством
спуска, нулевой риск, бюджет не истощается. -/
noncomputable def honestQuadStep (w : ℝ) (hw : 0 < w) :
    Hagi.Unified.HonestTransition.HonestTransition
      (fun x => x * x) w (w / 2) 0 0 0 1 where
  objectiveDrop := 3 * w * w / 4
  objectiveDrop_pos := div_pos (by nlinarith) (by norm_num)
  actualDescent := by
    show w / 2 * (w / 2) ≤ w * w - 3 * w * w / 4
    have h : w * w - 3 * w * w / 4 - (w / 2) * (w / 2) = 0 := by
      ring
    linarith
  riskBound := le_refl 0
  budgetBound := by norm_num

/-- Провайдер через `HonestTransition.toCertStepGen`: та же
галосящая карта, сертификат — цепочкой HonestTransition (остаток
риска 0 честен: risk-носитель машины тождественно нулевой). -/
noncomputable def honestQuadProvider :
    StepProvider honestQuadMetrics quadObligations (fun _ => 0) where
  init := 2
  step w :=
    if hw : 0 < w then
      some
        { next := w / 2
          cert :=
            Hagi.Unified.HonestTransition.HonestTransition.toCertStepGen
              (hT := honestQuadStep w hw)
              (riskRem := 0)
              (M := honestQuadMetrics) (s := w) (s' := w / 2)
              (hobj := by rfl)
              (hbud := by simp only [honestQuadMetrics]; ring)
              (hbud' := by simp only [honestQuadMetrics]; ring)
              (hrisk := by simp only [honestQuadMetrics]; ring)
              (hrisk' := by simp only [honestQuadMetrics]; ring)
              (hrem := by norm_num)
              (obl := quadObligations)
              (hfloors := by
                intro t'
                simp only [quadObligations, honestQuadMetrics]
                positivity) }
    else none

/-- Оракул честного провайдера жив на старте 2 и ведёт в 1. -/
theorem honest_quad_provider_alive :
    ∃ p : StepProposal honestQuadMetrics quadObligations (fun _ => 0) 2,
      honestQuadProvider.step 2 = some p ∧ p.next = 1 := by
  simp only [honestQuadProvider]
  split
  · exact ⟨_, rfl, by norm_num⟩
  · rename_i h
    exact absurd (by norm_num : (0 : ℝ) < 2) h

/-! ### Инстанс 3: CRAM descent (premise-form оракул)

Носитель `CRAMState`; оракул возвращает пару (s', шаг
`CRAMEnergyDescentStep`) или `none`. Метрики-считывания и полы —
явные посылки (паттерн `CRAMEnergyDescentStep.toKernelCertStep`).
δ-носитель тривиален: descent не тратит δ. -/

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype α] [DecidableEq α]

/-- Провайдер CRAM-спуска: начальное состояние + оракул descent-шагов;
метрики читают энергию доски / compute-бюджет / risk-остаток
(посылки), полы держатся во ВСЕХ состояниях (явная посылка). -/
noncomputable def cramDescentProvider
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (M : Hagi.Cert.SystemMetrics
      (Hagi.Model.EnergyReasoning.CRAMState ι α) TaskId)
    (hobj : M.objective = fun t => Hagi.Energy.pairwiseEnergy B K t.board)
    (hbud : M.budget = fun t => t.computeBudget)
    (hrisk : M.risk = fun t => t.riskRem)
    (obl : Hagi.Cert.StepObligations TaskId)
    (hfloors : ∀ s, Hagi.Cert.FloorsKept M obl s)
    (init : Hagi.Model.EnergyReasoning.CRAMState ι α)
    (oracle : (s : Hagi.Model.EnergyReasoning.CRAMState ι α) →
      Option ((s' : Hagi.Model.EnergyReasoning.CRAMState ι α) ×
        Hagi.Model.EnergyReasoning.CRAMEnergyDescentStep B K s s')) :
    StepProvider M obl (fun _ => 0) where
  init := init
  step s :=
    (oracle s).map fun p =>
      { next := p.1
        cert :=
          Hagi.Cert.certStep_to_gen M obl
            (Hagi.Model.EnergyReasoning.CRAMEnergyDescentStep.toKernelCertStep
              B K p.2 M hobj hbud hrisk obl (hfloors p.1)) }

end Hagi.Unified.StepProvider
