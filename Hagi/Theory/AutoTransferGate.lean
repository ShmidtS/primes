import Hagi.Theory.NegativeTransfer
import Hagi.Theory.AdapterBank


/-!
## AutoTransferGate — самонастраивающийся warm/cold transfer-гейт

Практическое применение границы —
переносить адаптер A в домен B warm-стартом ТОГДА И ТОЛЬКО ТОГДА,
когда измеряемый probe-критерий предсказывает пользу. Bench-механика
(`--mode adapter-transfer-auto`, bench_bridge.py): перед задачей B
probe A/B — 2 certified snap-GD-шага (rollback-семантика
probe не мутирует слот A) от warm-инициализации `θ` и от cold-инициализации
`0`; гейт выбирает arm с МЕНЬШИМ probe-objective (точные
рациональные числа, детерминированное сравнение — паттерн
`hybridSelect`). Затем выбранный arm проходит полный
certified-цикл.

Ключевые факты:

- `autoGate` — детерминированный селектор на измеренных probe-числах;
- `gate_char` — гейт совпадает с ТОЧНОЙ границей
  `2⟪θ, t⟫_ℝ > ‖θ‖²` при невырожденном шаге (`|1 − 2η| > 0`,
  `transfer_helps_budget`): probe A/B НЕ размывает границу;
- `gate_adversarial_cold` — adversarial-цель `t = −c • θ` (C572-синтетика)
  всегда даёт cold;
- `auto_transfer_gate_sound` (main) — дизъюнкция веток без ослабления
  (паттерн `hybrid_step_sound`): warm-ветка сохраняет ВСЕ гарантии
  `warm_transfer_sound` (forgetA = 0, dst = копия, certified-обучаемость
  с warm-init), cold-ветка — certified-гарантию нейтрального старта 0
  (`adapter_step_certified`; init-независимость: `θ` в statement
  cold-ветки не входит).
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.AutoTransferGate

open scoped InnerProductSpace
open Hagi.Theory.NegativeTransfer Hagi.Theory.AdapterGrowth
  Hagi.Theory.AdapterBank

/-! ## Детерминированный селектор на probe-измерениях -/

section Gate

variable {n : Type*} [Fintype n]

/-- Выбор transfer-ветки: warm (перенести адаптер A) или cold
(нейтральный старт 0). -/
inductive TransferChoice : Type
  | warm | cold

/-- Probe-objective: objective домена B после k certified-GD-шагов
от старта z (`gdRun` — чистые итерации функции: probe НЕ мутирует
состояние z, rollback-семантика — сравнение вычисляется на
копиях, слот A нетронут). -/
noncomputable def probeObj (η : ℝ) (k : ℕ)
    (t z : EuclideanSpace ℝ n) : ℝ :=
  quadObj t (gdRun k η t z)

/-- **autoGate (def)**: детерминированный warm/cold-селектор
на ДВУХ измеренных probe-числах (probe A/B): warm ⟺ probe-objective
от `θ` СТРОГО меньше probe-objective от `0`. Без порогов и оценок:
сравнение точных чисел (паттерн `hybridSelect` равенство =
граница → cold — перестраховочная ветка). -/
noncomputable def autoGate (η : ℝ) (k : ℕ)
    (t θ : EuclideanSpace ℝ n) : TransferChoice :=
  if probeObj η k t θ < probeObj η k t 0 then
    TransferChoice.warm
  else
    TransferChoice.cold

/-- **gate_char**: при невырожденном шаге (`|1 − 2η| > 0`)
probe-A/B-гейт совпадает с ТОЧНОЙ границей — переносить warm
⟺ удвоенное скалярное произведение больше квадрата нормы θ
(`transfer_helps_budget`: равный probe-бюджет НЕ размывает границу;
bench-аналог — квадратичность bench objective mh_mse: gap = 2·θᵀb − θᵀHθ). -/
theorem gate_char (η : ℝ) (hη : |1 - 2 * η| > 0) (k : ℕ)
    (t θ : EuclideanSpace ℝ n) :
    autoGate η k t θ = TransferChoice.warm ↔
      2 * ⟪θ, t⟫_ℝ > ‖θ‖ ^ 2 := by
  unfold autoGate probeObj
  split
  · next h =>
      constructor
      · intro _; exact (transfer_helps_budget k η hη θ t).mp h
      · intro _; trivial
  · next h =>
      constructor
      · intro hf; exact absurd hf (by simp)
      · intro hb
        exact absurd ((transfer_helps_budget k η hη θ t).mpr hb) h

/-- **gate_adversarial_cold**: adversarial-цель
`t = −c • θ` (c > 0, θ ≠ 0) — C572-синтетика bench-режима —
гейт ОБЯЗАН выбрать cold: скалярное произведение отрицательно,
границу `> ‖θ‖²` не выполнить. -/
theorem gate_adversarial_cold (η : ℝ) (hη : |1 - 2 * η| > 0)
    (k : ℕ) (θ : EuclideanSpace ℝ n) (c : ℝ)
    (hc : 0 < c) (hθ : θ ≠ 0) :
    autoGate η k (-c • θ) θ = TransferChoice.cold := by
  have hpos : 0 < ‖θ‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hθ)
  have h2 : 2 * ⟪θ, -c • θ⟫_ℝ = -2 * c * ‖θ‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hc2 : 0 < 2 * c * ‖θ‖ ^ 2 := by positivity
  have hnb : ¬ (2 * ⟪θ, -c • θ⟫_ℝ > ‖θ‖ ^ 2) := by
    rw [h2]; linarith
  unfold autoGate probeObj
  split
  · next h =>
      exact absurd ((transfer_helps_budget k η hη θ (-c • θ)).mp h) hnb
  · rfl

end Gate

/-! ## Дизъюнкция веток: выбранная ветка сохраняет гарантию -/

section Sound

variable {n ι r d : Type*} [Fintype n] [Fintype r] [Fintype d]
  [DecidableEq ι]

/-- **auto_transfer_gate_sound (main)**: выбор ветки по
ИЗМЕРЕННОМУ probe-критерию сохраняет гарантию ВЫБРАННОЙ ветки —
дизъюнкция без ослабления (паттерн `hybrid_step_sound`).

Warm-ветка: ВСЕ гарантии `warm_transfer_sound` — forgetA = 0
(слот src нетронут), dst-слот = копия src, certified-обучаемость
с warm-init (measured drop ⇒ COMMIT + строгий спуск).

Cold-ветка: certified-гарантия нейтрального старта 0 (
`adapter_step_certified`) — init-независимость: statement ветки
содержит только нулевой init, θ домена A в него НЕ входит (cold
не зависит от переноса по построению). -/
theorem auto_transfer_gate_sound (η : ℝ) (k : ℕ)
    (t θ : EuclideanSpace ℝ n) (hη : |1 - 2 * η| > 0)
    (bank : AdapterBankState ι r d) (src dst : ι)
    (obj : AdaptState r d → ℝ) (cand : AdaptState r d)
    (hdropW : obj cand < obj (bank src))
    (hdropC : obj cand < obj 0) :
    match autoGate η k t θ with
    | TransferChoice.warm =>
        warmTransfer bank src dst src = bank src ∧
          warmTransfer bank src dst dst = bank src ∧
          adapterStep obj (bank src) cand = cand ∧
          obj (adapterStep obj (bank src) cand) < obj (bank src)
    | TransferChoice.cold =>
        adapterStep obj 0 cand = cand ∧
          obj (adapterStep obj 0 cand) < obj 0 := by
  cases h : autoGate η k t θ with
  | warm =>
      simp only [h]
      exact warm_transfer_sound bank src dst obj cand hdropW
  | cold =>
      simp only [h]
      exact adapter_step_certified obj 0 cand hdropC

end Sound

end Hagi.Theory.AutoTransferGate
