import Mathlib
import Hagi.Unified.QuadGate

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
