/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.LiveDelta

set_option linter.style.header false

/-!
# Контракт динамического аудита живых весов

План интеграции, п. 4: допустимость принятого блока по
изменению ИЗМЕРЕННЫХ динамических характеристик модели
(наибольший сингулярный показатель якобиана, доля
расширяющих направлений, эффективная размерность —
прокси спектра Ляпунова).

Контракт — это Prop на паре (до, после): каждая характеристика
меняется не больше чем на свой допуск. Значения характеристик —
h_emp_ телеметрия (их вычисление и связь со спектром Ляпунова
конкретной сети НЕ формализуются). Ничего о «меньше — лучше»
не утверждается: допуск двусторонний, направление решает
владелец контракта.
-/

namespace Hagi.LiveDeltaAudit

/-- Треугольное неравенство для трёх точек (руками: abs_add
в этой версии Mathlib недоступен по имени). -/
private theorem tri (x y z u v : ℝ)
    (h1 : |x - y| ≤ u) (h2 : |y - z| ≤ v) : |x - z| ≤ u + v := by
  obtain ⟨p1, q1⟩ := abs_le.mp h1
  obtain ⟨p2, q2⟩ := abs_le.mp h2
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- Измеренная динамическая телеметрия модели (прокси
спектра возмущений; все поля — h_emp_ значения). -/
structure DynTelemetry where
  /-- Наибольший показатель роста возмущений (λ_max). -/
  lamMax : ℝ
  /-- Доля положительных показателей (p₊). -/
  pPlus : ℝ
  /-- Эффективная размерность (прокси участия, PR). -/
  partRatio : ℝ

/-- Допуски аудита: сколько каждая характеристика может
измениться за один принятый блок. -/
structure AuditTolerance where
  tolLam : ℝ
  tolP : ℝ
  tolPR : ℝ

/-- Контракт динамического аудита: |после − до| ≤ допуск
по каждой характеристике. -/
def auditAccept (tol : AuditTolerance) (before after : DynTelemetry) :
    Prop :=
  |after.lamMax - before.lamMax| ≤ tol.tolLam
    ∧ |after.pPlus - before.pPlus| ≤ tol.tolP
    ∧ |after.partRatio - before.partRatio| ≤ tol.tolPR

/-- Нарушение контракта видно по хотя бы одной характеристике:
если аудит не принят, какая-то характеристика вышла за допуск. -/
theorem audit_violation_witness (tol : AuditTolerance)
    (before after : DynTelemetry)
    (h : ¬ auditAccept tol before after) :
    |after.lamMax - before.lamMax| > tol.tolLam
      ∨ |after.pPlus - before.pPlus| > tol.tolP
      ∨ |after.partRatio - before.partRatio| > tol.tolPR := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  exact h ⟨h1, h2, h3⟩

/-- Транзитивность допусков (для цепочки из двух принятых
блоков с удвоенными допусками): если каждый шаг в допуске,
суммарное изменение ограничено суммой допусков. -/
theorem audit_chain (tol : AuditTolerance)
    (t0 t1 t2 : DynTelemetry)
    (h1 : auditAccept tol t0 t1) (h2 : auditAccept tol t1 t2) :
    |t2.lamMax - t0.lamMax| ≤ 2 * tol.tolLam
      ∧ |t2.pPlus - t0.pPlus| ≤ 2 * tol.tolP
      ∧ |t2.partRatio - t0.partRatio| ≤ 2 * tol.tolPR := by
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  constructor
  · have h := tri t2.lamMax t1.lamMax t0.lamMax tol.tolLam tol.tolLam b1 a1
    linarith
  · constructor
    · have h := tri t2.pPlus t1.pPlus t0.pPlus tol.tolP tol.tolP b2 a2
      linarith
    · have h := tri t2.partRatio t1.partRatio t0.partRatio tol.tolPR tol.tolPR b3 a3
      linarith

end Hagi.LiveDeltaAudit
