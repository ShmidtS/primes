/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.CertifiedEstimator
set_option linter.style.header false

/-!
# Мост V: SelfDevelopment — controller находит положительный upgrade

Аудит §25: для саморазвития нужно доказать минимальную
теорему вида «если существует безопасный upgrade a с
Gain(a) > 0, то controller за конечное число действий находит
upgrade a' с Gain(a') ≥ c·Gain(a) при ограниченном cost».

Этот модуль формализует детерминированное ядро и его
статистическую оболочку:

* `controller_max_exists` — на конечном множестве кандидатов
  (фильтр safe-предиката) argmax certified gain существует
  (`Finset.exists_max_image`).
* `self_development_find` — **ядро моста**: если в safe-наборе
  есть кандидат с положительным certified gain, то выбранный
  argmax-кандидат тоже положителен и не хуже него
  (c = 1 на candidate set).
* `certified_gain_select` — статистическая оболочка: если
  измеренные gains отклоняются от истинных не более чем на ε
  (R114-сертифицированные оценки), то argmax по измеренным
  даёт истинный gain ≥ Gain(a₀) − 2ε; при Gain(a₀) ≥ 3ε
  найденный upgrade строго положителен ИСТИННО, а не только
  по измерению.
* `search_cost_bound` — бюджет поиска линеен: суммарная
  стоимость измерений ≤ |A|·c_meas (конечность — суть
  «за ограниченный ресурс»).

**Честные границы**: (1) полнота пространства кандидатов
(существующий вне candidate set upgrade не найден — audit §25
требует именно «достаточно полного» генератора, это
предпосылка safe-набора); (2) ε-концентрация оценок —
посылка, сертифицируемая R114 на каждое действие.
-/

open Finset

namespace Hagi

variable {A : Type} [Fintype A] [Nonempty A]

/-- Safe-подмножество кандидатов (decidable). -/
def safeCandidates (safe : A → Prop) [DecidablePred safe] : Finset A :=
  Finset.univ.filter safe

/-- На safe-наборе существует argmax certified gain. -/
theorem controller_max_exists (G : A → ℝ) (safe : A → Prop)
    [DecidablePred safe] (hne : (safeCandidates safe).Nonempty) :
    ∃ a' ∈ safeCandidates safe, ∀ a ∈ safeCandidates safe, G a ≤ G a' :=
  Finset.exists_max_image (safeCandidates safe) G hne

/-- **Ядро моста V**: если в safe-наборе есть кандидат с
положительным certified gain, controller (argmax) выбирает
кандидат с положительным gain, не худшим найденного
(аппроксимация c = 1 на candidate set). -/
theorem self_development_find (G : A → ℝ) (safe : A → Prop)
    [DecidablePred safe]
    (a₀ : A) (h₀ : a₀ ∈ safeCandidates safe) (hpos : 0 < G a₀) :
    ∃ a' ∈ safeCandidates safe,
      0 < G a' ∧ G a₀ ≤ G a' := by
  have hne : (safeCandidates safe).Nonempty := ⟨a₀, h₀⟩
  obtain ⟨a', ha'mem, hmax⟩ := controller_max_exists G safe hne
  exact ⟨a', ha'mem, ⟨hpos.trans_le (hmax a₀ h₀), hmax a₀ h₀⟩⟩

/-- **Статистическая оболочка**: измеренные gains Ĝ отклоняются
от истинных g не более чем на ε (посылка, сертифицируемая
`certified_premise`/`cert_upper`-`cert_lower` на каждое
действие). Тогда argmax по измеренным даёт истинный gain
≥ g a₀ − 2ε; при g a₀ ≥ 3ε найденный upgrade строго
положителен по ИСТИННОМУ gain — измерение не обмануло
controller. -/
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

/-- Бюджет поиска: суммарная стоимость измерения всех кандидатов
линейна по размеру safe-набора — «за ограниченный ресурс». -/
theorem search_cost_bound (cMeas : ℝ) (hc : 0 ≤ cMeas) (safe : A → Prop)
    [DecidablePred safe] :
    (∑ a ∈ safeCandidates safe, cMeas) = ((safeCandidates safe).card : ℝ) * cMeas := by
  simp [Finset.sum_const]

end Hagi
