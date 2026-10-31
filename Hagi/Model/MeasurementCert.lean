import Mathlib
import Hagi.Model.CertifiedTransition

/-!
# MeasurementCert — двухуровневая сертификация перехода
(направление TorchLean: Specification → Execution →
Verification; закрытие рекомендации аудита о разделении
execution- и measurement-сертификатов)

Уровень 1 (execution): `CertifiedTransition.exec` — переход
действительно выполнен (`S' = advance S u`). Уже есть.

Уровень 2 (measurement): ЗДЕСЬ — сертификат того, что
заявленный прирост подтверждён ИЗМЕРЕНИЕМ с доверительной
полосой: claimed ∈ [measured − δ, measured + δ], где δ —
ширина anytime-доверительного интервала (концентрационные
гейты дают δ; см. AnytimeMartingale/AnytimePACBayes).

Мост: честная нижняя оценка прироста = measured − δ; если
она положительна, прирост НЕ ЯВЛЯЕТСЯ статистическим шумом.
-/

namespace Hagi.Model.MeasurementCert

open Hagi.System

/-- Сертификат измерения эффекта шага: заявленное значение
лежит в доверительной полосе вокруг измеренного. -/
structure StepMeasurement where
  /-- Заявленный (используемый сертификатом перехода) прирост. -/
  claimed : ℝ
  /-- Измеренный (эмпирический) прирост. -/
  measured : ℝ
  /-- Полуширина доверительного интервала (anytime-валидная). -/
  delta : ℝ
  hdelta : 0 ≤ delta
  hband : measured - delta ≤ claimed ∧ claimed ≤ measured + delta

/-- ЧЕСТНАЯ НИЖНЯЯ ОЦЕНКА: заявленный прирост не меньше
измеренного минус полуширина полосы. -/
theorem claimed_floor (m : StepMeasurement) :
    m.measured - m.delta ≤ m.claimed := m.hband.1

/-- ЗАЗОР ПРЕВЫШАЕТ ШУМ: если измеренный прирост строго
превышает полуширину полосы, заявленный прирост строго
положителен — прирост не является статистическим шумом
(двухсторонняя полоса исключает и завышение). -/
theorem claimed_pos_of_signal (m : StepMeasurement)
    (hnoise : m.delta < m.measured) : 0 < m.claimed := by
  have h1 := m.hband.1
  have h2 : 0 < m.measured - m.delta := by linarith
  linarith

/-- НЕЗАВИСИМОСТЬ ОТ ЗАЯВЛЕННОГО: верхняя сторона полосы —
заявленный прирост не может превышать измеренный более чем
на δ (анти-лазейка для завышения отчётности). -/
theorem claimed_ceiling (m : StepMeasurement) :
    m.claimed ≤ m.measured + m.delta := m.hband.2

/-- КОМПОЗИЦИЯ ИЗМЕРЕНИЙ: последовательные шаги — полосы
складываются (сумма заявленных ∈ полосе сумм). -/
def compose (m1 m2 : StepMeasurement) : StepMeasurement where
  claimed := m1.claimed + m2.claimed
  measured := m1.measured + m2.measured
  delta := m1.delta + m2.delta
  hdelta := add_nonneg m1.hdelta m2.hdelta
  hband := by
    constructor <;> linarith [m1.hband.1, m1.hband.2, m2.hband.1, m2.hband.2]

/-- КУМУЛЯТИВНАЯ ЧЕСТНОСТЬ: цепочка измерений сохраняет
нижнюю оценку — суммарный заявленный прирост ≥ суммарный
измеренный − суммарная полуширина. -/
theorem chain_floor {T : ℕ} (ms : Fin T → StepMeasurement) :
    ∑ t, (ms t).measured - ∑ t, (ms t).delta
      ≤ ∑ t, (ms t).claimed := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h := ih (fun t => ms t.succ)
      have hlast := (ms 0).hband.1
      linarith

end Hagi.Model.MeasurementCert
