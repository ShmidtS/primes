/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Unified.QuadMachine
import Hagi.Unified.FunctionalState

/-!
# Протоколы эталонной машины (объединённые)

MeasureProto (протокол измерения с операционными типами),
ProtoTrajectory (execution × measurement × certificate вдоль
реальной траектории), FsGate (commit/hold над функциональным
состоянием). Слит из трёх модулей; имена сохранены.
-/

/-!
# MeasureProto: протокол
измерений — У эффектов обязано быть происхождение.

«measure — произвольная входная
функция, не формальный вычислитель». Здесь интерфейс, где
каждый эффект — ПОЛЕ ПРОТОКОЛА с операционным типом
(функция из параметров/перехода), и ПЕРВЫЙ инстанс для
эталонной машины, где всё вычислено:

1. `MeasureProto`: loss/risk/capability/cost — поля-ФУНКЦИИ
   (происхождение фиксируется типом: Params → ℝ);
2. `machineProto`: инстанс для ReferenceMachine:
   loss = energy (реальное вычисление из весов);
3. `machineProto_gap`: dStep производственного QuadGate
   выводится из протокола: machineGap = loss(θ) −
   loss(jointStep θ) — НИКАКИХ внешних чисел;
4. `machineGateFromProto`: machineCert (GateCert такта
   №269) — спроецирован из протокола: gate-решение
   полностью происхождено.
-/

namespace Hagi.Unified.MeasureProto

open Hagi.Model.ReferenceMachine Hagi.Unified.QuadGate
  Hagi.Unified.CommitGate

variable {n : ℕ}

/-- ПРОТОКОЛ ИЗМЕРЕНИЙ: каждый канал — функция с
операционным типом (происхождение — часть интерфейса). -/
structure MeasureProto (P : Type) where
  /-- Лосс: вычисляется из параметров. -/
  loss : P → ℝ
  /-- Защищённый риск: вычисляется из параметров. -/
  risk : P → ℝ
  /-- Capability: вычисляется из параметров. -/
  capability : P → ℝ
  /-- Стоимость перехода: функция пары (до, после). -/
  cost : P → P → ℝ

/-- ИНСТАНС ДЛЯ МАШИНЫ: все каналы — реальные вычисления
из весов (loss = energy; risk/capability/ cost —
канонические тривиальные для эталона: нулевой риск,
единичная capability, нулевая цена hold... здесь цена
шага = 1 — счётчик вычислений). -/
noncomputable def machineProto (a : Fin n → ℝ) :
    MeasureProto (Fin n → ℝ) where
  loss := energy a
  risk := fun _ => 0
  capability := fun w => 1 / (1 + energy a w)
  cost := fun _ _ => 1

/-- dStep QuadGate ВЫВЕДЕН из протокола (тождество). -/
theorem machineProto_gap (a : Fin n → ℝ) (w : Fin n → ℝ)
    (eta : ℝ) :
    machineGap a w eta
      = (machineProto a).loss w
        - (machineProto a).loss (jointStep a w eta) := rfl


/-- Энергия неотрицательна (вспомогательная). -/
theorem energy_nonneg (a w : Fin n → ℝ) : 0 ≤ energy a w := by
  unfold energy
  exact Finset.sum_nonneg (fun i _ =>
    div_nonneg (sq_nonneg _) (by norm_num))

/-- Capability протокола — убывающая функция реальной
энергии: меньше энергии — больше capability (канал
происхождения согласован с loss). -/
theorem machineProto_capa_mono (a : Fin n → ℝ)
    (w₁ w₂ : Fin n → ℝ)
    (h : energy a w₁ ≤ energy a w₂) :
    (machineProto a).capability w₂
      ≤ (machineProto a).capability w₁ := by
  unfold MeasureProto.machineProto
  simp only []
  have h1 := energy_nonneg a w₁
  have h2 := energy_nonneg a w₂
  have hkey : 1 + energy a w₁ ≤ 1 + energy a w₂ := by linarith
  exact one_div_le_one_div_of_le (by linarith) hkey



/-- PROBE-CAPABILITY : отдельный
канал — доля координат, попавших в ε-окрестность цели.
НЕ сводим к loss: измеряет покрытие задач (счётное), а не
квадратичную ошибку; связь однонаправленная: энергия
ниже порога ⟹ полное покрытие (но не наоборот). -/
noncomputable def evalCapa (a : Fin n → ℝ) (eps : ℝ)
    (w : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, if |w i - a i| ≤ eps then (1:ℝ) else 0)
    / (Fintype.card (Fin n))

/-- Границы probe-capability: ∈ [0, 1]. -/
theorem evalCapa_bounds (a : Fin n → ℝ) (eps : ℝ)
    (w : Fin n → ℝ) (hn : 0 < n) :
    0 ≤ evalCapa a eps w ∧ evalCapa a eps w ≤ 1 := by
  have hnum : ∀ i : Fin n,
      (0:ℝ) ≤ (if |w i - a i| ≤ eps then (1:ℝ) else 0)
        ∧ (if |w i - a i| ≤ eps then (1:ℝ) else 0) ≤ 1 := by
    intro i
    by_cases h : |w i - a i| ≤ eps
    · simp [h]
    · simp [h]
  constructor
  · unfold evalCapa
    exact div_nonneg (Finset.sum_nonneg
      (fun i _ => (hnum i).1)) (by positivity)
  · unfold evalCapa
    have h1 : ∑ i : Fin n,
        (if |w i - a i| ≤ eps then (1:ℝ) else 0)
        ≤ ∑ i : Fin n, (1:ℝ) :=
      Finset.sum_le_sum (fun i _ => (hnum i).2)
    have h2 : (∑ i : Fin n, (1:ℝ))
      = (Fintype.card (Fin n : Type) : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [h2] at h1
    have hcard : (0:ℝ) < (Fintype.card (Fin n : Type)) := by
      simpa using hn
    exact (div_le_one hcard).mpr h1

end Hagi.Unified.MeasureProto

/-!
# ProtoTrajectory: протокол × траектория —
полная цепочка execution × measurement × certificate.

Замыкание интеграции аудита №5: лоссы, измеряемые
ПРОТОКОЛОМ (MeasureProto, ), вдоль РЕАЛЬНОЙ
траектории commit/hold (QuadTrajectory, ):

1. `proto_loss_mono`: loss-канал протокола не возрастает
   вдоль траектории (проекция gateTraj_mono);
2. `proto_loss_telescope`: ТОЧНЫЙ телескоп loss-канала =
   E₀ − E_T (проекция trajDropSum);
3. `proto_progress_bound`: суммарный сертифицированный
   прогресс loss-канала ≤ начального loss (проекция
   trajDropBound).

Всё происхождено: исполнение (gateTraj) × измерение
(machineProto.loss = energy) × сертификат (телескоп).
-/

namespace Hagi.Unified.ProtoTrajectory

open Hagi.Model.ReferenceMachine Hagi.Unified.QuadGate
  Hagi.Unified.QuadTrajectory Hagi.Unified.QuadBudget
  Hagi.Unified.MeasureProto

variable {n : ℕ}

/-- Лосс-канал протокола НЕ ВОЗРАСТАЕТ вдоль траектории. -/
theorem proto_loss_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w₀ : Fin n → ℝ) (T : ℕ) :
    (machineProto a).loss (gateTraj a eta Delta w₀ T)
      ≤ (machineProto a).loss w₀ := by
  show energy a (gateTraj a eta Delta w₀ T) ≤ energy a w₀
  exact gateTraj_mono a eta Delta hD w₀ T

/-- ТОЧНЫЙ телескоп loss-канала протокола. -/
theorem proto_loss_telescope (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T,
      ((machineProto a).loss (gateTraj a eta Delta w₀ t)
        - (machineProto a).loss
          (gateTraj a eta Delta w₀ (t + 1)))
      = (machineProto a).loss w₀
        - (machineProto a).loss (gateTraj a eta Delta w₀ T) :=
  trajDropSum a eta Delta w₀ T

/-- СУММАРНЫЙ СЕРТИФИЦИРОВАННЫЙ ПРОГРЕСС ≤ начального
loss (измеренного протоколом). -/
theorem proto_progress_bound (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T,
      ((machineProto a).loss (gateTraj a eta Delta w₀ t)
        - (machineProto a).loss
          (gateTraj a eta Delta w₀ (t + 1)))
      ≤ (machineProto a).loss w₀ :=
  trajDropBound a eta Delta w₀ T

/-- CAPABILITY-КАНАЛ НЕ УБЫВАЕТ вдоль траектории
(инверсия loss-монотонности: меньше энергии — больше
capability). -/
theorem proto_capa_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w₀ : Fin n → ℝ) (T : ℕ) :
    (machineProto a).capability w₀
      ≤ (machineProto a).capability
        (gateTraj a eta Delta w₀ T) := by
  exact machineProto_capa_mono a (gateTraj a eta Delta w₀ T)
    w₀ (gateTraj_mono a eta Delta hD w₀ T)

end Hagi.Unified.ProtoTrajectory

/-!
# FsGate: commit/hold-gate над ФУНКЦИОНАЛЬНЫМ
состоянием — замыкание FunState в траекторный цикл.

Мост: веса fsGate-шага РАВНЫ gateStep из QuadTrajectory
(тот же вычисленный gate); энергия — функция состояния.
Следствия (все проекции доказанных теорем):
1. `fsGate_weights_eq`: fsGate-веса = gateStep-веса;
2. `fsGate_mono`: энергия функционального состояния не
   возрастает на gate-шаге;
3. `fsTraj_mono`: кумулятивная монотонность по T.

Итог: полный стек (FunState × QuadGate × QuadTrajectory)
— функциональное состояние в сертифицированном цикле.
-/

namespace Hagi.Unified.FsGate

open Hagi.Model.ReferenceMachine Hagi.Unified.FunctionalState
  Hagi.Unified.QuadGate Hagi.Unified.QuadTrajectory
  Hagi.Unified.CommitGate

variable {n : ℕ}

open Classical

/-- Gate-шаг над функциональным состоянием: commit при
открытом gate (веса = machineStep), иначе hold. -/
noncomputable def fsGate (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) : FunState n :=
  if gate (machineCert a s.weights eta Delta) then
    funStep a eta Delta s else s

/-- Веса-мост: fsGate-веса = gateStep-веса (тот же
вычисленный gate над теми же весами). -/
theorem fsGate_weights_eq (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) :
    (fsGate a eta Delta s).weights
      = gateStep a eta Delta s.weights := by
  unfold fsGate gateStep funStep
  by_cases hg : gate (machineCert a s.weights eta Delta)
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]

/-- ЭНЕРГИЯ НЕ ВОЗРАСТАЕТ на gate-шаге (проекция
gateStep_mono через веса-мост). -/
theorem fsGate_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (s : FunState n) :
    fsEnergy a (fsGate a eta Delta s) ≤ fsEnergy a s := by
  unfold fsEnergy
  rw [fsGate_weights_eq a eta Delta s]
  exact gateStep_mono a eta Delta hD s.weights

/-- Траектория функционального состояния. -/
noncomputable def fsTraj (a : Fin n → ℝ) (eta Delta : ℝ)
    (s₀ : FunState n) : ℕ → FunState n
  | 0 => s₀
  | (t + 1) => fsGate a eta Delta (fsTraj a eta Delta s₀ t)

/-- Кумулятивная монотонность: энергия вдоль всей
fs-траектории не возрастает (индукция + fsGate_mono). -/
theorem fsTraj_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (s₀ : FunState n) (T : ℕ) :
    fsEnergy a (fsTraj a eta Delta s₀ T) ≤ fsEnergy a s₀ := by
  induction T with
  | zero => exact le_refl _
  | succ t ih =>
    have hstep := fsGate_mono a eta Delta hD
      (fsTraj a eta Delta s₀ t)
    exact le_trans hstep ih


/-- БЮДЖЕТ-ШАГ: commit платит 1, hold бесплатен. -/
theorem fsGate_budget (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) :
    (fsGate a eta Delta s).budget
      = if gate (machineCert a s.weights eta Delta)
        then s.budget - 1 else s.budget := by
  unfold fsGate funStep
  by_cases hg : gate (machineCert a s.weights eta Delta)
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]

/-- СЧЁТЧИК-ШАГ: commit считается, hold нет. -/
theorem fsGate_count (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) :
    (fsGate a eta Delta s).stepCount
      = if gate (machineCert a s.weights eta Delta)
        then s.stepCount + 1 else s.stepCount := by
  unfold fsGate funStep
  by_cases hg : gate (machineCert a s.weights eta Delta)
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]

/-- БЮДЖЕТ НЕ ВОЗРАСТАЕТ: бюджет вдоль fs-траектории не
превышает начального (индукция: commit платит, hold
бесплатен). -/
theorem fsTraj_budget_le (a : Fin n → ℝ) (eta Delta : ℝ)
    (s₀ : FunState n) (T : ℕ) :
    (fsTraj a eta Delta s₀ T).budget ≤ s₀.budget := by
  induction T with
  | zero => exact le_refl _
  | succ t ih =>
    simp only [fsTraj]
    have hstep := fsGate_budget a eta Delta
      (fsTraj a eta Delta s₀ t)
    rw [hstep]
    by_cases hg : gate (machineCert a
      ((fsTraj a eta Delta s₀ t)).weights eta Delta)
    · rw [if_pos hg]
      linarith
    · rw [if_neg hg]
      exact ih

/-- СЧЁТЧИК ≤ T: число реальных шагов не превышает горизонт
(верхняя граница commitCount). -/
theorem fsTraj_count_le (a : Fin n → ℝ) (eta Delta : ℝ)
    (s₀ : FunState n) (T : ℕ) :
    (fsTraj a eta Delta s₀ T).stepCount
      ≤ s₀.stepCount + T := by
  induction T with
  | zero =>
    show s₀.stepCount ≤ s₀.stepCount + 0
    omega
  | succ t ih =>
    simp only [fsTraj]
    have hstep := fsGate_count a eta Delta
      (fsTraj a eta Delta s₀ t)
    rw [hstep]
    by_cases hg : gate (machineCert a
      ((fsTraj a eta Delta s₀ t)).weights eta Delta)
    · rw [if_pos hg]
      omega
    · rw [if_neg hg]
      omega

end Hagi.Unified.FsGate
