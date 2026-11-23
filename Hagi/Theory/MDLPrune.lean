/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.MDLThreeCurrency
import Hagi.Growth.IntegrationOrder
import Hagi.Growth.FiberNecessity
import Hagi.Ensemble.MergePrice
import Hagi.Budget.JointCost

import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# MDLPrune — составная soundness MDL-prune цикла

Формализация HAGI_v2 self-optimization (implementation source,
READ-ONLY: `C:\HAGI_v2\hagi\mdl.py`, 185 строк; интеграция —
`C:\HAGI_v2\hagi\rewrite.py:294-310`). Prune-цикл кода
(`prune_library`, hagi/mdl.py:77-148): удаление поведенческих
дубликатов (keep-shortest-AST, :98-99) и unreferenced/pseudo
экспертов ПО ОДНОМУ за проход (`while changed`, :129-138),
с сохранением call-DAG (7-8) и полной ре-валидацией после
(`apply_prune`, :159-184 — любая неудача АБОРТИРУЕТ prune).

СОСТАВНАЯ теорема `mdl_prune_cycle_sound` СОЕДИНЯЕТ четыре
существующих обоснования (THEORY_ALIGNMENT.md), не пере-доказывая
их:

* (a) objective (Lpred + λ·Lcode) не растёт на каждом шаге
  prune — из `Hagi.Step.J3_nonincreasing` (обобщение
  `mdlObjective_nonincreasing`, цикл 33 сверки) + посылки
  «дубликаты не добавляют покрытия» (сертифицированная карта
  _certified_map, hagi/mdl.py:54-64: удалённый дубликат
  идентичен kept-копии на всём certified domain);
* (a′) удаление отрицательного эксперта строго улучшает сумму
  выигрышей — `Hagi.Growth.positive_selection_dominates`
  (IntegrationOrder);
* (b) покрытие/флоры не теряются — `Hagi.Growth.
  fiber_params_floor` (FiberNecessity): floor-оценка зависит
  только от used-конфигов; посылка call-DAG integrity
  (hagi/mdl.py:7-8) удерживает их в pruned-библиотеке;
* (merge) код-стоимость/риск merge-пере-кодирования аддитивны,
  компаундинга нет — `Hagi.Ensemble.merged_bound` +
  `deltaCost_concat` (MergePrice, ATTACK_VECTOR §2);
* (контрабаланс) pruned-библиотека остаётся в cheap-switching
  режиме — `Hagi.Budget.switching_never_exceeds_dense`
  (FlopsEconomy; ЧЕСТНЫЙ ПИН: теоремы amortized_growth_cheaper
  не существует — это label в docstring JointCost.lean:228;
  формальное содержание контрабаланса — switching-режим);
* (d) завершаемость — строгая убыль card на каждом erase-шаге
  над конечной библиотекой ⇒ бесконечный prune-цикл невозможен
  (паттерн `adopt_chain_terminates`, SelfEdit.lean:134;
  Theory→Theory импорт запрещён LayerLint — переиспользован
  паттерн, не импорт).

Честные границы (не заявляется):
* мост `mdlObjective_nonincreasing` нельзя вызвать напрямую —
  он сравнивает θ/θ′ ОДНОЙ функции ℝ→ℝ; библиотека в ℝ не
  вкладывается честно, поэтому мост идёт через скалярную
  `J3_nonincreasing` (λ_R = 0-случай той же модули);
* «дубликаты не покрывают нового» — ПОСЫЛКА (содержание
  _certified_map-дедупликации), не теорема этого модуля;
* cost-модель `bits` — ПОСЫЛКА: неточный cost может удалить
  редкого-but-полезного эксперта (негативная теорема
  `prune_can_drop_useful_expert` ниже);
* Lpred произвольна: ре-валидация кода (hagi/mdl.py:159-184)
  моделируется посылкой инвариантности, а не вычислением.
-/

open Finset

namespace Hagi.Theory.MDLPrune

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ### Модель библиотеки (source: hagi/mdl.py) -/

/-- Конечная библиотека экспертов. source: hagi/mdl.py — словарь
`proc.experts` с конечным числом имён (`names = list(experts.
keys())`, :80-82); one-step erase-семантика — цикл `while
changed` удаляет по одному эксперту за проход (129-138). -/
abbrev Library (N) [Fintype N] := Finset N

/-- Код-стоимость библиотеки: сумма AST-размеров экспертов.
source: hagi/mdl.py:48-51 `_ast_size` (размер AST эксперта);
keep-shortest-AST среди дубликатов — :98-99 (`members.sort(
key=_ast_size)`, `keep = members[0]`). -/
def libCodeCost (bits : N → ℝ) (s : Library N) : ℝ :=
  ∑ e ∈ s, bits e

/-- MDL-цель библиотеки: Lpred + λ·Lcode (предсказательная
потеря + λ-взвешенная длина описания). source:
THEORY_ALIGNMENT.md:620-623 (цикл 33 сверки,
mdlObjective_nonincreasing; J(θ) = L_pred(θ) + λ·L_code(θ)),
эмпирический факт механизма — MDL-prune 1285→864 экспертов. -/
def libObjective (Lpred : Library N → ℝ) (bits : N → ℝ)
    (lam : ℝ) (s : Library N) : ℝ :=
  Lpred s + lam * libCodeCost bits s

/-- Точный мост к трёхвалютной цели MDLThreeCurrency: libObjective
— это J3 с нулевым риском-забывания (λ_R = 0). Через этот мост
работает композиция с `J3_nonincreasing` (обобщением
`mdlObjective_nonincreasing`; прямого вызова последнего требует
вложенности Library→ℝ, которая была бы подгоном — см. модульный
докстринг). -/
theorem libObjective_eq_J3 (Lpred : Library N → ℝ) (bits : N → ℝ)
    (lam : ℝ) (s : Library N) :
    libObjective Lpred bits lam s
      = Hagi.Step.J3 (Lpred s) (libCodeCost bits s) 0 lam 0 := by
  unfold libObjective Hagi.Step.J3
  ring

/-! ### One-step prune: code-стоимость (source: keep-shortest) -/

/-- Удаление эксперта неотрицательной стоимости не увеличивает
код-стоимость библиотеки. source: hagi/mdl.py:98-99 — дубликаты
сортируются по AST-размеру, keep = shortest; :129-138 —
erase-шаг. -/
theorem prune_step_code_nonincreasing (bits : N → ℝ)
    {s : Library N} {e : N} (he : e ∈ s) (hbits : 0 ≤ bits e) :
    libCodeCost bits (s.erase e) ≤ libCodeCost bits s := by
  have h := Finset.sum_erase_add s bits he
  unfold libCodeCost
  rw [← h]
  linarith

/-- Если удаляемый эксперт имеет СТРОГО положительную стоимость,
код-стоимость строго убывает — каждый реальный prune-шаг кода
уменьшает библиотеку (keep-shortest-AST, hagi/mdl.py:98-99;
цикл продолжается только пока `changed`, :129). -/
theorem prune_step_code_decreases (bits : N → ℝ)
    {s : Library N} {e : N} (he : e ∈ s) (hbits : 0 < bits e) :
    libCodeCost bits (s.erase e) < libCodeCost bits s := by
  have h := Finset.sum_erase_add s bits he
  unfold libCodeCost
  rw [← h]
  linarith

/-! ### Нога (a′): отрицательные эксперты (IntegrationOrder) -/

/-- СОСТАВНАЯ НОГА (a′): удаление эксперта с отрицательным
чистым выигрышем СТРОГО улучшает суммарный выигрыш — прямая
композиция `Hagi.Growth.positive_selection_dominates`
(IntegrationOrder: в аддитивном режиме удаление отрицательного
эксперта улучшает в любом порядке). source: hagi/mdl.py:111-137
— pseudo-1-arg/unreferenced эксперты (отрицательный вклад
«стоимость без покрытия») удаляются итеративно. -/
theorem prune_negative_experts_improve_sum {M : ℕ} (g : Fin M → ℝ)
    {s : Finset (Fin M)} {i : Fin M} (hi : i ∈ s) (hg : g i < 0) :
    ∑ x ∈ s, g x < ∑ x ∈ s.erase i, g x :=
  Hagi.Growth.positive_selection_dominates g s i hi hg

/-! ### Нога (a): one-step objective (MDLThreeCurrency) -/

/-- СОСТАВНАЯ НОГА (a): MDL-цель (Lpred + λ·Lcode) НЕ РАСТЁТ на
шаге prune — композиция `Hagi.Step.J3_nonincreasing` (λ_R = 0
случай; обобщение `mdlObjective_nonincreasing` цикла 33).
Посылка `hdup` — «дубликаты не добавляют покрытия»: удаляемый
эксперт сертифицированно идентичен kept-копии на всём certified
domain (source: hagi/mdl.py:54-64 _certified_map —
ground-truth дедупликации; :98-99 dup-группы), поэтому
предсказательная часть не меняется. -/
theorem prune_step_objective_nonincreasing
    (Lpred : Library N → ℝ) (bits : N → ℝ) (lam : ℝ)
    {s : Library N} {e : N} (he : e ∈ s)
    (hlam : 0 ≤ lam) (hbits : 0 ≤ bits e)
    (hdup : Lpred (s.erase e) = Lpred s) :
    libObjective Lpred bits lam (s.erase e)
      ≤ libObjective Lpred bits lam s := by
  have hc := prune_step_code_nonincreasing bits he hbits
  rw [libObjective_eq_J3, libObjective_eq_J3]
  exact Hagi.Step.J3_nonincreasing (Lp := Lpred s)
    (Lp' := Lpred (s.erase e)) (Cst := libCodeCost bits s)
    (Cst' := libCodeCost bits (s.erase e)) (Rp := 0) (Rp' := 0)
    (lamM := lam) (lamR := 0) hdup.le hc (le_refl 0) hlam
    (le_refl 0)

/-! ### Нога (b): флоры/покрытие (FiberNecessity) -/

/-- СОСТАВНАЯ НОГА (b): prune СОХРАНЯЕТ fiber-флоры. Если все
used-конфигурации остаются в pruned-библиотеке (посылка
call-DAG integrity: referenced-эксперты не удаляются — source:
hagi/mdl.py:7-8 «keep every expert whose call-name is
referenced», :129-138 refd_now-пересчёт), то floor-оценка
`fiber_params_floor` (FiberNecessity) продолжает действовать:
дубликаты не добавляют покрытия, флоры — по kept-конфигам. -/
theorem prune_preserves_fiber_floor {A Q : Type} [DecidableEq Q]
    (good : A → A → Prop) (tasks : Finset A)
    (hsep : Hagi.Information.SepSeparated good tasks)
    (cfg : A → Q) (serve : Q → A)
    (hcover : ∀ x ∈ tasks, good (serve (cfg x)) x)
    (rank : Q → ℕ) (rmin d : ℕ)
    (hrank : ∀ q ∈ Finset.image cfg tasks, rmin ≤ rank q)
    {s' : Finset Q}
    (hkeep : Finset.image cfg tasks ⊆ s') :
    tasks.card * rmin * d
      ≤ ∑ q ∈ s', rank q * d := by
  have hfloor := Hagi.Growth.fiber_params_floor good tasks hsep
    cfg serve hcover rank rmin d hrank
  calc tasks.card * rmin * d
      ≤ ∑ q ∈ Finset.image cfg tasks, rank q * d := hfloor
    _ ≤ ∑ q ∈ s', rank q * d :=
        Finset.sum_le_sum_of_subset hkeep

/-! ### Нога (merge): аддитивность без компаундинга (MergePrice) -/

/-- СОСТАВНАЯ НОГА (merge): двухшаговое merge-пере-кодирование
платит ЛИНЕЙНО — сумма бит-стоимостей плюс константа на шаг,
без мультипликативного компаундинга (специализация
`Hagi.Ensemble.merged_bound` на K = 2 через `deltaCost_concat`).
Содержание: «слитый не хуже худшего» в bit-валюте — merge-часть
prune (дедупликация + keep-shortest) не может взорвать штраф.
source: hagi/mdl.py:98-99 (dup-группы → один kept-эксперт). -/
theorem merge_pair_risk_bound {d : ℕ} (risk : Hagi.Ensemble.Delta d → ℝ)
    (δ₁ δ₂ : Hagi.Ensemble.Delta d) (lambda mu : ℝ)
    (h1 : ∀ δ₀, risk (δ₀ ++ δ₁)
      ≤ risk δ₀ + lambda * Hagi.Ensemble.deltaCost δ₁ + mu)
    (h2 : ∀ δ₀, risk (δ₀ ++ δ₂)
      ≤ risk δ₀ + lambda * Hagi.Ensemble.deltaCost δ₂ + mu)
    (hcoeff : (0:ℝ) ≤ lambda) :
    risk (δ₁ ++ δ₂) ≤ risk []
      + lambda * (Hagi.Ensemble.deltaCost δ₁
        + Hagi.Ensemble.deltaCost δ₂)
      + 2 * mu := by
  have key := Hagi.Ensemble.merged_bound risk
    (fun k => if k = 0 then δ₁ else δ₂) lambda mu 2
    (fun δ₀ k => by
      by_cases hk : k = 0
      · simp only [hk, ite_true]
        exact h1 δ₀
      · simp only [hk, ite_false]
        exact h2 δ₀)
    hcoeff
  have hflat : List.flatMap (fun k => if k = 0 then δ₁ else δ₂)
      (List.range 2) = δ₁ ++ δ₂ := by
    simp [List.range_succ]
  have hsum : ∑ k ∈ Finset.range 2,
      Hagi.Ensemble.deltaCost (if k = 0 then δ₁ else δ₂)
      = Hagi.Ensemble.deltaCost δ₁ + Hagi.Ensemble.deltaCost δ₂ := by
    simp [Finset.sum_range_succ]
  rw [hflat, hsum] at key
  exact key

/-! ### Контрабаланс: pruned-библиотека в cheap-switching режиме -/

/-- СОСТАВНОЙ КОНТРАБАЛАНС (FlopsEconomy): если pruned-библиотека
(активных конфигов = card) с ростом r остаётся в режиме
card + r ≤ d, её активная per-token стоимость не превышает
плотного эксперта d² — композиция `Hagi.Budget.
switching_never_exceeds_dense` (JointCost/FlopsEconomy).
ЧЕСТНЫЙ ПИН: теоремы amortized_growth_cheaper НЕ существует —
это label docstring'а JointCost.lean:228; формальное содержание
контрабаланса MDL-prune против роста — switching-режим.
source: hagi/mdl.py (prune держит библиотеку малой против
grow-цикла rewrite.py:294-310). -/
theorem pruned_switching_le_dense (r d : ℕ) {s : Library N}
    (hreg : s.card + r ≤ d) :
    (s.card + r) * d ≤ d * d :=
  Hagi.Budget.switching_never_exceeds_dense s.card r d hreg

/-! ### Нога (d): завершаемость prune-цикла -/

/-- СОСТАВНАЯ НОГА (d): ЗАВЕРШАЕМОСТЬ. Каждый prune-шаг кода
удаляет ровно одного эксперта (`while changed`, erase — source:
hagi/mdl.py:129-138), поэтому card строго убывает; строго
убывающая ℕ-цепочка ограничена card начальной библиотеки ⇒
бесконечный prune-цикл НЕВОЗМОЖЕН. Паттерн
`adopt_chain_terminates` (SelfEdit.lean:134: строгий
gain/убыль + конечность ⇒ нет бесконечной цепочки; здесь
ℕ-индукция вместо Fintype.card-противоречия, Theory→Theory
импорт запрещён LayerLint). -/
theorem prune_chain_terminates (f : ℕ → Library N)
    (h : ∀ i, ∃ e : N, e ∈ f i ∧ f (i + 1) = (f i).erase e) :
    False := by
  have hdec : ∀ i, (f (i + 1)).card < (f i).card := by
    intro i
    obtain ⟨e, hemem, herase⟩ := h i
    rw [herase, Finset.card_erase_of_mem hemem]
    have : 1 ≤ (f i).card := Finset.card_pos.2 ⟨e, hemem⟩
    omega
  have key : ∀ i : ℕ, (f i).card + i ≤ (f 0).card := by
    intro i
    induction i with
    | zero => omega
    | succ i ih => have := hdec i; omega
  have := key ((f 0).card + 1)
  omega

/-! ### ГЛАВНАЯ составная теорема -/

/-- ГЛАВНАЯ СОСТАВНАЯ ТЕОРЕМА: MDL-prune-цикл (удалить
отрицательных/дубликаты + сохранить флоры) КОРРЕКТЕН ПО ШАГАМ.

Для цепочки библиотек `f`, где каждый шаг удаляет одного
эксперта (source: hagi/mdl.py:129-138 `while changed`),
удаление — certified-дубликат (посылка `hdup`: Lpred не меняется;
source: hagi/mdl.py:54-64, :98-99) с положительной
код-стоимостью (keep-shortest, :98-99), при λ ≥ 0:

* (a) MDL-цель Lpred + λ·Lcode НЕ РАСТЁТ на каждом шаге —
  нога `prune_step_objective_nonincreasing` (композиция
  `J3_nonincreasing` = обобщение `mdlObjective_nonincreasing`,
  MDLThreeCurrency, цикл 33 сверки);
* (a′) код-стоимость СТРОГО убывает (keep-shortest-AST);
* (d) card строго убывает ⇒ завершаемость
  (`prune_chain_terminates`, паттерн).

Ноги (b) (флоры: `prune_preserves_fiber_floor` из
`fiber_params_floor` + call-DAG-посылка) и (merge)
(`merge_pair_risk_bound` из `merged_bound`) — посылки цикла,
выполнение которых код гарантирует точной ре-валидацией
(hagi/mdl.py:159-184: любая неудача АБОРТИРУЕТ prune).

Честные границы: soundness КОНДИЦИОНАЛЬНА на cost-модель bits
и duplicate-посылку — см. негатив `prune_can_drop_useful_expert`.
-/
theorem mdl_prune_cycle_sound (Lpred : Library N → ℝ)
    (bits : N → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (f : ℕ → Library N)
    (hstep : ∀ i, ∃ e : N, e ∈ f i ∧ f (i + 1) = (f i).erase e
      ∧ Lpred (f (i + 1)) = Lpred (f i) ∧ 0 < bits e) :
    ∀ i, libObjective Lpred bits lam (f (i + 1))
        ≤ libObjective Lpred bits lam (f i)
      ∧ libCodeCost bits (f (i + 1)) < libCodeCost bits (f i)
      ∧ (f (i + 1)).card < (f i).card := by
  intro i
  obtain ⟨e, hemem, herase, hdup, hbits⟩ := hstep i
  refine ⟨?_, ?_, ?_⟩
  · rw [herase]
    exact prune_step_objective_nonincreasing Lpred bits lam
      hemem hlam hbits.le (by rw [← herase]; exact hdup)
  · rw [herase]
    exact prune_step_code_decreases bits hemem hbits
  · rw [herase, Finset.card_erase_of_mem hemem]
    have : 1 ≤ (f i).card := Finset.card_pos.2 ⟨e, hemem⟩
    omega

/-! ### Негатив: cost-модель — посылка -/

/-- НЕГАТИВНАЯ ТЕОРЕМА (честный предел): prune МОЖЕТ удалить
редкого-but-полезного эксперта. Библиотека из двух экспертов
(N = 2): эксперт №1 полезен (его удаление СТРОГО ухудшает
предсказание: Lpred 0 → 1), но дорог (bits = 2); при λ = 1
MDL-цель всё равно СТРОГО падает при его удалении (4 → 3) —
cost-модель доминирует полезность. Soundness
`mdl_prune_cycle_sound` не защищает от этого: она
кондициональна на точность `bits` (source: hagi/mdl.py —
cost-модель фиксируется `_ast_size`, полезность не входит в
критерий удаления дубликатов). -/
theorem prune_can_drop_useful_expert :
    ∃ (Lpred : Library (Fin 2) → ℝ) (bits : Fin 2 → ℝ)
      (lam : ℝ) (s : Library (Fin 2)) (e : Fin 2),
      0 ≤ lam
        ∧ Lpred (s.erase e) > Lpred s
        ∧ libObjective Lpred bits lam (s.erase e)
          < libObjective Lpred bits lam s := by
  refine ⟨fun s => if (1 : Fin 2) ∈ s then 0 else 1,
    fun _ => 2, 1, Finset.univ, 1, by norm_num, ?_, ?_⟩
  · simp [Finset.mem_univ, Finset.mem_erase]
  · simp only [libObjective, libCodeCost, Finset.mem_univ,
      Finset.mem_erase]
    norm_num

end Hagi.Theory.MDLPrune
