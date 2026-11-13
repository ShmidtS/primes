/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.CertifiedEstimator
import Hagi.Cert.CertifiedArgmax
set_option linter.style.header false

/-!
# SelfDevelopment — детерминированное ядро поиска upgrade и статистическая оболочка

Селекторы сертифицированного argmax (`safeCandidates`,
`controller_max_exists`, `certified_gain_select`) консолидированы
в канон `Hagi.Cert.CertifiedArgmax` (R3, C234).

* `self_development_find`: если в safe-наборе есть кандидат с
  `0 < G a₀`, то argmax-кандидат `a'` удовлетворяет
  `0 < G a'` и `G a₀ ≤ G a'`;
* `search_cost_bound`: сумма стоимостей измерений равна
  `card · cMeas`.

Полнота candidate set и ε-концентрация оценок — посылки.
-/

open Finset

namespace Hagi.Growth

variable {A : Type} [Fintype A] [Nonempty A]

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

/-- Сумма стоимостей измерения всех кандидатов равна
`card · cMeas`. -/
theorem search_cost_bound (cMeas : ℝ) (hc : 0 ≤ cMeas) (safe : A → Prop)
    [DecidablePred safe] :
    (∑ a ∈ safeCandidates safe, cMeas) = ((safeCandidates safe).card : ℝ) * cMeas := by
  simp [Finset.sum_const]

end Hagi.Growth

