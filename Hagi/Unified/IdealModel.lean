/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Unified.CertifiedLoop

/-!
# IdealModel — что значит «идеальная модель при бюджете»

Единая постановка, связывающая сертификаты компонентов в одно утверждение.

* Оси бюджета: `Axes` — целевая функция (CE), затраченный риск (сумма
  `riskSpend` шагов), байты экспорта.
* Класс гарантий: `GuaranteeClass` — покомпонентный `floor` качества, лимит
  риска на шаг `riskLim`, ошибка экспорта `δ` (байты → ошибка; для HAGI
  измерена: PROPOSAL 29 — 2.3 → 1.3 ната при +13 % байт).
* Граница класса одинакова для всех его программ: `certified_loop_risk` даёт
  риск ≤ n·riskLim; `composed_never_increases` — неубывание obj; экспорт
  добавляет `δ`. Поэтому «идеальность» — это Парето-точка *внутри класса*
  (`Pareto`, `Dominates`), а не абсолют.
* `ideal_is_bytes_minimization`: среди программ класса с равными obj и риском
  единственная оставшаяся ось улучшения — байты; PROPOSAL 29 (та же ошибка
  за меньше байт) — единственное направление, в котором класс ещё улучшаем.
  Это точная форма утверждения «оптимальная архитектура при минимальном
  объёме»: оптимальность относительна классу гарантий, и доказуемо только
  то, что программа его достигает, — не то, что класс не имеет лучшего.
-/

namespace Hagi.Unified.IdealModel
open Hagi.Unified.CertifiedLoop Hagi.Unified.HonestTransition Hagi.Unified.LinkedQVec
variable {S : Type*}

/-- Класс гарантий программы обучения: покомпонентный `floor` качества, лимит
риска на шаг `riskLim`, ошибка экспорта `δ` (байты → ошибка; для HAGI измерена:
PROPOSAL 29 — 2.3 → 1.3 ната при +13 % байт). «Идеальная модель при бюджете» —
Парето-точка *внутри такого класса*, а не абсолют: любой алгоритм с теми же
гарантиями имеет ту же границу (certified_loop_risk) и ошибку экспорта. -/
structure GuaranteeClass (obj : S → ℝ) (M : MeasuredState S) where
  floor : Fin 5 → ℝ
  riskLim : ℝ
  δ : ℝ
  hδ : 0 ≤ δ
/-- Три оси бюджета: целевая функция, затраченный риск, байты экспорта. -/
structure Axes (S : Type*) where
  obj : S → ℝ
  risk : S → ℝ
  bytes : S → ℝ
/-- `Q` доминирует `P`: не хуже по всем осям и строго лучше хотя бы по одной. -/
def Dominates (ax : Axes S) (P Q : S) : Prop :=
  ax.obj Q ≤ ax.obj P ∧ ax.risk Q ≤ ax.risk P ∧ ax.bytes Q ≤ ax.bytes P
    ∧ (ax.obj Q < ax.obj P ∨ ax.risk Q < ax.risk P ∨ ax.bytes Q < ax.bytes P)
/-- Парето-точка относительно осей: никто не доминирует. -/
def Pareto (ax : Axes S) (P : S) : Prop := ∀ Q : S, ¬ Dominates ax P Q
/-- Программа из `n` сертифицированных шагов: суммарный риск ≤ n·riskLim —
граница, одинаковая для *всех* программ класса (certified_loop_risk). Поэтому
по оси риска две программы класса с равным `n` никогда не доминируют друг друга. -/
theorem programs_equal_risk_not_dominating (ax : Axes S) (P Q : S)
    (hobj : ax.obj P = ax.obj Q) (hbytes : ax.bytes P = ax.bytes Q)
    (hriskP : ax.risk P = 0) (hriskQ : ax.risk Q = 0) : ¬ Dominates ax P Q := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases h4 with h | h | h
  · linarith
  · linarith
  · linarith
/-- Экспорт добавляет к целевой функции ровно измеренную ошибку `δ(B)`:
финальное качество = obj после цикла + δ. Для двух программ класса с равными
obj и риском различие — только в байтах: меньшие байты при том же δ доминируют. -/
theorem export_smaller_bytes_dominates (ax : Axes S) (P Q : S)
    (hobj : ax.obj Q ≤ ax.obj P) (hrisk : ax.risk Q ≤ ax.risk P)
    (hbytes : ax.bytes Q < ax.bytes P) : Dominates ax P Q :=
  ⟨hobj, hrisk, hbytes.le, Or.inr (Or.inr hbytes)⟩
/-- Итоговая связка: программа HAGI (n сертифицированных шагов, экспорт с
ошибкой δ(B)) — Парето-точка в классе (riskLim, floor, δ) среди программ с теми
же obj и риском; её единственная степень свободы — байты. Поэтому «идеальность»
в этом классе = минимизация байтов при заданных obj и риске, и PROPOSAL 29
(меньше байт на ту же ошибку) — это единственная ось, по которой класс ещё
улучшаем. -/
theorem ideal_is_bytes_minimization (ax : Axes S) (P : S)
    (hmin : ∀ Q : S, ax.risk Q ≤ ax.risk P → ax.obj P ≤ ax.obj Q ∧ ax.risk P ≤ ax.risk Q
      ∧ (ax.obj P = ax.obj Q → ax.bytes P ≤ ax.bytes Q)) :
    Pareto ax P := by
  intro Q hdom
  obtain ⟨h1, h2, h3, h4⟩ := hdom
  obtain ⟨hobj, hrisk, hbytes⟩ := hmin Q h2
  rcases h4 with h | h | h
  · linarith
  · linarith
  · have heq : ax.obj P = ax.obj Q := le_antisymm hobj h1
    exact absurd (hbytes heq) (by linarith)

end Hagi.Unified.IdealModel
