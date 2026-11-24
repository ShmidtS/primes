import Mathlib

/-!
# RepairForgetting — итеративный repair забывания

Код-факт (HAGI_v2 READ-ONLY @e9a96fc, hagi/unified.py
`Unified._repair_forgetting`, режим `REPAIR_MODE = "replay"`,
unified.py:408-458 @e9a96fc): после шага обучения на свежем домене,
пока парный gate `post` (CE старых доменов на ФИКСИРОВАННЫХ окнах)
выше `pre`: (1) snapshot параметров; (2) шаг обучения на СТАРЫХ
байтах (`train_certified`, lr `REPAIR_LR`); (3) замер `new`;
если `new >= post - 1e-4` — точный rollback на snapshot и СТОП
(status ROLLBACK); иначе `post := new` и следующий раунд. Бюджет
`REPAIR_ROUNDS = 6` раундов.

СОПОСТАВЛЕНИЕ с клозом (2) `Hagi.Theory.MasterTheoremV3.master_theorem_v3`
(zero-forgetting ТОЧНО при `hfroz`: выход замороженной задачи не
меняется): repair НЕ удовлетворяет посылке — шаг на старых байтах
пишет в ВЕСЬ trunk, выход старых доменов меняется. Забывание
УМЕНЬШАЕТСЯ, а не равно нулю (измерено в commit e9a96fc: CE первых
доменов без repair +0.553, с repair +0.036; код сам пишет «Not
zero»). Механизм здесь другой — ограждённый спуск с точным
rollback; он и формализуется.

ЧТО ДОКАЗАНО / ЧТО НЕТ. В коде НЕТ коэффициента сжатия: шаг
принимается при любом результате лучше порога `tol`, без нижней
границы улучшения сверх `tol`. Поэтому честная граница — ЛИНЕЙНАЯ
по числу принятых раундов (`repair_drop_bound`: gate падает минимум на
`tol` за принятый раунд), а НЕ геометрическая `(1 − ρ)^k`. Верхней границы
забывания после repair нет: цепочка может кончиться rollback'ом при
`post > pre`. Gate-значение — выборочная оценка CE на <= 8 старых
доменах, а не забывание по популяции.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory.RepairForgetting

/-- Один шаг repair как функция от раунда: принятое значение —
кандидат (он строго ниже), откаченное — прежнее значение ТОЧНО.
source: hagi/unified.py:446-453 @e9a96fc (`q.copy_(s0)`). -/
noncomputable def stepValue (tol : ℝ) (v new : ℝ) : ℝ :=
  if new < v - tol then new else v

/-- Принятый шаг строго уменьшает gate минимум на `tol`. -/
theorem stepValue_retrain {tol v new : ℝ} (h : new < v - tol) :
    stepValue tol v new = new := by
  simp [stepValue, h]

/-- Откаченный шаг возвращает gate-значение ТОЧНО: rollback —
тождество на значении (а в коде — на всех параметрах snapshot'а). -/
theorem stepValue_rollback {tol v new : ℝ} (h : ¬ new < v - tol) :
    stepValue tol v new = v := by
  simp [stepValue, h]

/-- Прогон repair из бюджета `r` раундов: стартовое значение `v`,
финальное `z`. Ветки кода: (done) бюджет исчерпан или забывания
нет — значение не меняется; (retrain) шаг принят; (rollback) шаг
откачен и цикл СТОП — значение тождественно дораундовому.
source: hagi/unified.py:436-454 @e9a96fc. -/
inductive RepairRun (tol : ℝ) : ℕ → ℝ → ℝ → Type
  | done (r : ℕ) (v : ℝ) : RepairRun tol r v v
  | retrain (r : ℕ) (v w z : ℝ) (h : w < v - tol)
      (rest : RepairRun tol r w z) : RepairRun tol (r + 1) v z
  | rollback (r : ℕ) (v w : ℝ) (h : ¬ w < v - tol) :
      RepairRun tol (r + 1) v v

/-- Число ПРИНЯТЫХ раундов прогона. -/
def acceptedCount {tol : ℝ} : {r : ℕ} → {v z : ℝ} →
    RepairRun tol r v z → ℕ
  | _, _, _, .done _ _ => 0
  | _, _, _, .retrain _ _ _ _ _ rest => acceptedCount rest + 1
  | _, _, _, .rollback _ _ _ _ => 0

/-- ЛИНЕЙНАЯ граница: каждый принятый раунд уменьшает gate минимум на
`tol`, поэтому `z ≤ v − tol·(#принятых)`. НЕ геометрия: коэффициента
сжатия в коде нет, улучшение за раунд ограничено только снизу порогом. -/
theorem repair_drop_bound {tol : ℝ} {r : ℕ} {v z : ℝ}
    (run : RepairRun tol r v z) :
    z ≤ v - tol * (acceptedCount run : ℝ) := by
  induction run with
  | done _ _ => simp [acceptedCount]
  | @retrain r v w z h rest ih =>
      rw [acceptedCount]
      push_cast
      generalize hc : (acceptedCount rest : ℝ) = c at ih ⊢
      calc z ≤ w - tol * c := ih
        _ ≤ v - tol - tol * c := by linarith
        _ = v - tol * (c + 1) := by ring
  | rollback _ _ _ _ => simp [acceptedCount]

/-- Принятых раундов не больше бюджета. -/
theorem accepted_le_budget {tol : ℝ} {r : ℕ} {v z : ℝ}
    (run : RepairRun tol r v z) : acceptedCount run ≤ r := by
  induction run with
  | done _ _ => exact Nat.zero_le _
  | @retrain r v w z h rest ih =>
      simpa [acceptedCount] using Nat.succ_le_succ ih
  | rollback _ _ _ _ => exact Nat.zero_le _

/-- Полная формулировка моста: после прогона repair из бюджета `r`
gate НИКОГДА не увеличился (`z ≤ v`) и упал минимум на `tol` за каждый
принятый раунд (`z ≤ v − tol·a`), причём принятых раундов не больше
бюджета (`a ≤ r`). -/
theorem repair_sound {tol : ℝ} (htol : 0 ≤ tol) {r : ℕ} {v z : ℝ}
    (run : RepairRun tol r v z) :
    z ≤ v - tol * (acceptedCount run : ℝ) ∧ z ≤ v ∧
      acceptedCount run ≤ r := by
  have h1 := repair_drop_bound run
  have h2 : v - tol * (acceptedCount run : ℝ) ≤ v :=
    sub_le_self _ (mul_nonneg htol (Nat.cast_nonneg _))
  exact ⟨h1, h1.trans h2, accepted_le_budget run⟩

end Hagi.Theory.RepairForgetting
