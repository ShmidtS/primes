/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.CertifiedEstimator
set_option linter.style.header false

/-!
# SelfDevelopment — детерминированное ядро поиска upgrade и статистическая оболочка

* `controller_max_exists`: на непустом safe-наборе существует
  argmax certified gain;
* `self_development_find`: если в safe-наборе есть кандидат с
  `0 < G a₀`, то argmax-кандидат `a'` удовлетворяет
  `0 < G a'` и `G a₀ ≤ G a'`;
* `certified_gain_select`: если `|Ghat a − g a| ≤ eps` для
  всех a и `3·eps < g a₀`, то найденный argmax-кандидат
  удовлетворяет `0 < g a'` и `g a₀ − 2·eps ≤ g a'`;
* `search_cost_bound`: сумма стоимостей измерений равна
  `card · cMeas`.

Полнота candidate set и ε-концентрация оценок — посылки.
-/

open Finset

namespace Hagi.Growth

variable {A : Type} [Fintype A] [Nonempty A]

/-- Safe-подмножество кандидатов: фильтр `Finset.univ` по
`safe` (decidable). -/
def safeCandidates (safe : A → Prop) [DecidablePred safe] : Finset A :=
  Finset.univ.filter safe

/-- Если safe-набор непуст, то существует
`a' ∈ safeCandidates safe` с `G a ≤ G a'` для всех
`a ∈ safeCandidates safe`. -/
theorem controller_max_exists (G : A → ℝ) (safe : A → Prop)
    [DecidablePred safe] (hne : (safeCandidates safe).Nonempty) :
    ∃ a' ∈ safeCandidates safe, ∀ a ∈ safeCandidates safe, G a ≤ G a' :=
  Finset.exists_max_image (safeCandidates safe) G hne

/-- Если `a₀ ∈ safeCandidates safe` и `0 < G a₀`, то существует
`a' ∈ safeCandidates safe` с `0 < G a'` и `G a₀ ≤ G a'`. -/
theorem self_development_find (G : A → ℝ) (safe : A → Prop)
    [DecidablePred safe]
    (a₀ : A) (h₀ : a₀ ∈ safeCandidates safe) (hpos : 0 < G a₀) :
    ∃ a' ∈ safeCandidates safe,
      0 < G a' ∧ G a₀ ≤ G a' := by
  have hne : (safeCandidates safe).Nonempty := ⟨a₀, h₀⟩
  obtain ⟨a', ha'mem, hmax⟩ := controller_max_exists G safe hne
  exact ⟨a', ha'mem, ⟨hpos.trans_le (hmax a₀ h₀), hmax a₀ h₀⟩⟩

/-- Если `|Ghat a − g a| ≤ eps` для всех a,
`a₀ ∈ safeCandidates safe` и `3·eps < g a₀`, то существует
`a' ∈ safeCandidates safe` с `0 < g a'` и
`g a₀ − 2·eps ≤ g a'`. -/
theorem certified_gain_select (g Ghat : A → ℝ) (safe : A → Prop)
    [DecidablePred safe] (eps : ℝ) (heps : 0 ≤ eps)
    (hconc : ∀ a, |Ghat a - g a| ≤ eps)
    (a₀ : A) (h₀ : a₀ ∈ safeCandidates safe)
    (hgap : 3 * eps < g a₀) :
    ∃ a' ∈ safeCandidates safe,
      0 < g a' ∧ g a₀ - 2 * eps ≤ g a' := by
  have hne : (safeCandidates safe).Nonempty := ⟨a₀, h₀⟩
  obtain ⟨a', ha'mem, hmax⟩ := controller_max_exists Ghat safe hne
  refine ⟨a', ha'mem, ?_, ?_⟩
  · -- 0 < g a': |Ĝa' − g a'| ≤ ε, Ĝa' ≥ Ĝa₀ ≥ g a₀ − ε ≥ 3ε − ε = 2ε
    have ha'c := hconc a'
    have ha₀c := hconc a₀
    have hsel : Ghat a₀ ≤ Ghat a' := hmax a₀ h₀
    have hlow : g a₀ - eps ≤ Ghat a₀ := by
      have := abs_le.mp ha₀c |>.1
      linarith [abs_le.mp ha₀c |>.1, abs_le.mp ha₀c |>.2]
    have hhigh : Ghat a' - eps ≤ g a' := by
      have := abs_le.mp ha'c |>.2
      linarith [abs_le.mp ha'c |>.1, abs_le.mp ha'c |>.2]
    have hkey : g a₀ - 2 * eps ≤ g a' := by linarith
    have hpos2 : 0 < g a₀ - 2 * eps := by linarith [hgap, heps]
    linarith
  · have ha'c := hconc a'
    have ha₀c := hconc a₀
    have hsel : Ghat a₀ ≤ Ghat a' := hmax a₀ h₀
    have hlow : g a₀ - eps ≤ Ghat a₀ := by
      have := abs_le.mp ha₀c |>.1
      linarith [abs_le.mp ha₀c |>.1, abs_le.mp ha₀c |>.2]
    have hhigh : Ghat a' - eps ≤ g a' := by
      have := abs_le.mp ha'c |>.2
      linarith [abs_le.mp ha'c |>.1, abs_le.mp ha'c |>.2]
    linarith

/-- Сумма стоимостей измерения всех кандидатов равна
`card · cMeas`. -/
theorem search_cost_bound (cMeas : ℝ) (hc : 0 ≤ cMeas) (safe : A → Prop)
    [DecidablePred safe] :
    (∑ a ∈ safeCandidates safe, cMeas) = ((safeCandidates safe).card : ℝ) * cMeas := by
  simp [Finset.sum_const]

end Hagi.Growth

namespace Hagi
export Hagi.Growth (safeCandidates controller_max_exists self_development_find certified_gain_select search_cost_bound)
end Hagi
