/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Math.Foundations.Telescope
import Mathlib.Tactic

/-!
# AdditiveLedger — единый обобщённый телескоп (A18.3, beat)

Аудит W6: cert-телескопы (`trajectory_telescope`, `delta_telescope`,
`trajectory_telescope_gen`, `risk_telescope_gen`,
`budget_ledger_telescope`, …) пере-доказывают одну и ту же индукцию
«Σ drops ≤ lvl₀ − lvl_N» над ledger-полями шага. Этот модуль — ОДИН
интерфейс: typeclass `AdditiveLedger` (≤-закон списания) и его точная
версия `ExactAdditiveLedger` (=-закон), с ОДНОЙ обобщённой леммой
`additive_ledger_telescope` (плюс `_eq`/`_floor` формы). Вся индукция
делегируется ядру `Hagi.Foundations.telescope_*` — здесь нет
ни одной новой индукции.

Модуль — лист (не импортирует cert-структуры): инстансы для
`CertStep`/`CertStepDelta` живут в `Hagi.Cert.Core`, для
`CertStepGen` — в `Hagi.Cert.StepGen`; доменные телескопы становятся
one-line специализациями `additive_ledger_telescope` с явным `level`.
НЕ сводятся без искажения: `certs_telescope`
(строгое убывание + risk-рост конъюнкцией), `ctv2_family_telescope`
(суть — per-step nlinarith, не телескоп), `floor_floor_telescope`
(контракт-обёртка двух каналов).
-/

set_option linter.style.header false

open Finset

namespace Hagi.Cert

variable {S : Type*}

/-- ОДИН обобщённый аддитивный ledger: уровень `level : S → ℝ`
списывается шагом `Step` на величину `spend` (≤-закон спуска).
`level` — явный параметр класса: инстансы различаются уровнем
(objective / budget / risk / deltaLevel) на одной шаговой структуре. -/
class AdditiveLedger (S : Type*) (level : S → ℝ)
    (Step : S → S → Type*) where
  /-- Списываемая шагом величина (ledger-поле шага: drop, delta,
  budgetSpend, riskSpend). -/
  spend : ∀ {s s' : S} (_c : Step s s'), ℝ
  /-- По-шаговый спуск уровня: `level s' ≤ level s − spend c`. -/
  step_descend : ∀ {s s' : S} (c : Step s s'), level s' ≤ level s - spend c

/-- Точная версия ledger-а: списание — равенство. -/
class ExactAdditiveLedger (S : Type*) (level : S → ℝ)
    (Step : S → S → Type*) where
  /-- Списываемая шагом величина. -/
  spend : ∀ {s s' : S} (_c : Step s s'), ℝ
  /-- Точный закон списания: `level s' = level s − spend c`. -/
  step_exact : ∀ {s s' : S} (c : Step s s'), level s' = level s - spend c

/-- ОДНА обобщённая лемма (≤-форма): терминальный уровень не выше
начального минус сумма списаний. Индукция — `Hagi.Foundations.
telescope_le_sub` (единственное место, где она доказана). -/
theorem additive_ledger_telescope {level : S → ℝ}
    {Step : S → S → Type*} [AdditiveLedger S level Step]
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j, Step (t j) (t (j + 1))) :
    level (t n) ≤ level (t 0)
      - ∑ j ∈ Finset.range n, AdditiveLedger.spend level (steps j) :=
  Hagi.Foundations.telescope_le_sub
    (f := fun k => level (t k))
    (c := fun j => AdditiveLedger.spend level (steps j))
    (fun j _ => AdditiveLedger.step_descend (steps j))

/-- Точная форма: терминальный уровень равен начальному минус сумма
списаний (закон ресурсного учёта). -/
theorem additive_ledger_telescope_eq {level : S → ℝ}
    {Step : S → S → Type*} [ExactAdditiveLedger S level Step]
    (n : ℕ) (t : ℕ → S)
    (steps : ∀ j, Step (t j) (t (j + 1))) :
    level (t n) = level (t 0)
      - ∑ j ∈ Finset.range n, ExactAdditiveLedger.spend level (steps j) :=
  Hagi.Foundations.telescope_sub_sum
    (f := fun k => level (t k))
    (c := fun j => ExactAdditiveLedger.spend level (steps j))
    (fun j _ => ExactAdditiveLedger.step_exact (steps j))

/-- Floor-форма: сумма списаний не превосходит начального уровня,
если терминальный уровень неотрицателен (неизрасходованный остаток
ресурса честно явной посылкой). -/
theorem additive_ledger_telescope_floor {level : S → ℝ}
    {Step : S → S → Type*} [ExactAdditiveLedger S level Step]
    (n : ℕ) (t : ℕ → S) (hn : 0 ≤ level (t n))
    (steps : ∀ j, Step (t j) (t (j + 1))) :
    ∑ j ∈ Finset.range n, ExactAdditiveLedger.spend level (steps j)
      ≤ level (t 0) := by
  have h := additive_ledger_telescope_eq (level := level) n t steps
  linarith

end Hagi.Cert
