/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.LiveDeltaSafe
import Hagi.Runtime.LiveDeltaQuant
import Hagi.Architecture.LiveDelta
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

namespace Hagi.Runtime

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

end Hagi.Runtime

set_option linter.style.header false

/-!
# Сквозной цикл живых весов (план интеграции, п. 6)

Одна теорема о полном цикле низкорангового обучения:

обновление новейшего блока (изоляция состояния) →
SafeQP-окно (защищаемые потери в бюджетах) →
динамический аудит (в допуске) →
квантизация при упаковке (квадратичная ошибка ≤ mn(s/2)²) →
бюджет памяти (точный, не меняется при обновлении).

Все измеряемые посылки (десцент-линии, телеметрия,
в-диапазонность) — h_emp_ гипотезы. Никакого утверждения о
качестве обучения нет — это сертификат ЦИКЛА, соединяющий
уже доказанные части.
-/

open Finset Matrix Real InnerProductSpace
open Hagi.Architecture Hagi.Step Hagi.Runtime
  Hagi.Runtime

namespace Hagi.Unified

variable {m n r : Type} [Fintype m] [Fintype n] [Fintype r]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- **Сквозной сертификат одного цикла живых весов**:
при (1) обновлении только новейшего блока, (2) SafeQP-окне
шага в фактор-пространстве, (3) прохождении динамического
аудита и (4) в-диапазонности упаковываемой базы —
одновременно: защищаемые потери в бюджетах, состояние
изолировано (база/хвост/длина/стоимость неизменны), аудит в
допуске, упаковочная ошибка ≤ mn(s/2)². -/
theorem live_delta_cycle (s : LiveDelta m n r)
    (B' : Matrix r n ℝ)
    -- SafeQP window in the factor space
    (g : K → X) (eps L : K → ℝ) (d : X) (dL : K → ℝ) (eta : ℝ)
    (hL : ∀ i, 0 < L i) (heps : ∀ i, 0 ≤ eps i) (heta : 0 ≤ eta)
    (hd : d ≠ 0)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, d⟫_ℝ
      + L i * eta * eta * ‖d‖ ^ 2 / 2)
    (h_eta : eta ≤ safeqpEtaMax g eps L d)
    -- dynamic audit
    (tol : AuditTolerance) (tel tel' : DynTelemetry)
    (haudit : auditAccept tol tel tel')
    -- packaging: the folded base is in ternary range
    (sPack : ℝ) (hs : 0 < sPack)
    (hin : ∀ i j, ternInRange sPack (effectiveWeights s i j)) :
    -- 1. protected losses within budgets
    (∀ i, dL i ≤ eps i)
    -- 2. state isolation
    ∧ (updateNewest B' s).base = s.base
      ∧ (updateNewest B' s).blocks.length = s.blocks.length
    -- 3. memory cost unchanged
    ∧ (updateNewest B' s).blocks.length
        * (Fintype.card r * (Fintype.card m + Fintype.card n))
      = s.blocks.length
        * (Fintype.card r * (Fintype.card m + Fintype.card n))
    -- 4. dynamic audit within tolerance
    ∧ (|tel'.lamMax - tel.lamMax| ≤ tol.tolLam
      ∧ |tel'.pPlus - tel.pPlus| ≤ tol.tolP
      ∧ |tel'.partRatio - tel.partRatio| ≤ tol.tolPR)
    -- 5. packaging quantization error bound
    ∧ ∑ i, ∑ j, (effectiveWeights s i j
        - quantMat sPack (effectiveWeights s) i j) ^ 2
      ≤ (Fintype.card m * Fintype.card n) * (sPack / 2) ^ 2 :=
  ⟨safe_update_window g eps L d dL eta hL heps heta hd h_lipline
      h_eta,
    updateNewest_base B' s, updateNewest_length B' s,
    updateNewest_cost B' s, haudit,
    quantMat_sq_bound sPack hs (effectiveWeights s) hin⟩

end Hagi.Unified
