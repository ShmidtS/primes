/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Empirical — типизированная обёртка эмпирических посылок (C245, Phase 1)

Заместительный типизированный путь для голых гипотез `h_emp_*`
(AssumptionScan остаётся как есть — массовой миграции нет, обёртка
опциональна). Надёжностной класс по addendum A7: **D** (эмпирические
посылки + cost-model гипотезы) — класс указан здесь и обязателен для
каждого декларированного потребителя.

`Empirical P` упаковывает посылку `P` вместе с метаданными источника
(измеренный закон, допуск, ссылка на модель/данные). Конструкция
ТРЕБУЕТ предъявить `P` — обёртка ничего не доказывает и не может
протащить посылку контрабандой; проекция `Empirical.out` возвращает
ровно то, что было предъявлено.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Cert

/-- Типизированная эмпирическая посылка: посылка + метаданные
источника. Класс D (addendum A7): эмпирика, не аналитика. -/
structure Empirical (P : Prop) where
  /-- Идентификатор измеренного закона (например h_emp_pl). -/
  measuredLaw : String
  /-- Численный допуск измерения. -/
  tolerance : ℝ
  /-- Допуск неотрицателен. -/
  tolerance_nonneg : 0 ≤ tolerance
  /-- Ссылка на эмпирическую модель / источник данных. -/
  modelRef : String
  /-- Сама посылка — предъявляется вызывающей стороной. -/
  premise : P

/-- Распаковка: типизированная обёртка даёт в точности предъявленную
посылку (и ничего больше). -/
def Empirical.out {P : Prop} (e : Empirical P) : P := e.premise

end Hagi.Cert
