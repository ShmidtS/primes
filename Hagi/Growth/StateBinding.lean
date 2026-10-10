/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.FrontierScaling
import Hagi.Growth.SelfDevelopment
import Hagi.Unified.GrowthState
set_option linter.style.header false

/-!
# StateBinding — связывание процессов-теней с полями состояния + полнота кандидатов

* `usableFrontier`: поле frontier состояния (`S.dataField`);
* `capability_takeoff_state`: если
  `C t = (S t).capability`, `G t = (S t).growGain`,
  `D t = usableFrontier (S t)` и выполнены посылки
  `sustained_takeoff_from_production`, то
  `(S 0).capability·(1+α)^T ≤ (S T).capability`;
* `CandidateComplete`: полнота генератора — если существует
  safe-кандидат с gain ≥ g, генератор выдаёт safe-кандидат
  с gain ≥ g − ε (посылка);
* `candidate_completeness_find`: полнота + существование
  safe-кандидата с `eps < G a₀` ⇒ argmax по сгенерированным
  safe-кандидатам находит `a'` с `0 < G a'` и
  `G a₀ − eps ≤ G a'`.

Посылки динамики и полнота генератора — измеряемые/открытые,
здесь не выводятся.
-/

open Finset

namespace Hagi.Growth

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ## Связывание теней с состоянием -/

/-- Поле frontier состояния: `usableFrontier S = S.dataField`. -/
def usableFrontier (S : GrowthState X) : ℝ := S.dataField

/-- Если выполнены посылки `sustained_takeoff_from_production`
для `C t = (S t).capability`, `G t = (S t).growGain`,
`D t = usableFrontier (S t)`, то
`(S 0).capability·(1+α)^T ≤ (S T).capability`. -/
theorem capability_takeoff_state (S : ℕ → GrowthState X) (xi : ℕ → ℝ)
    (alpha gamma rho beta : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hrho : 0 ≤ rho)
    (hC0 : 0 < (S 0).capability)
    (h_cone0 : alpha / gamma * (S 0).capability ≤ usableFrontier (S 0))
    (h_step : ∀ t, (S (t + 1)).capability
      = (S t).capability + (S t).growGain)
    (h_gain_prod : ∀ t, gamma * usableFrontier (S t) ≤ (S t).growGain)
    (h_dyn : ∀ t, rho * usableFrontier (S t) + beta * (S t).capability
      - xi t ≤ usableFrontier (S (t + 1)))
    (h_C_cap : ∀ t, (S (t + 1)).capability
      ≤ (1 + alpha) * (S t).capability)
    (hbeta : ∀ t, alpha / gamma * ((1 + alpha) - rho)
      + xi t / (S t).capability ≤ beta)
    (T : ℕ) :
    (S 0).capability * (1 + alpha) ^ T ≤ (S T).capability :=
  sustained_takeoff_from_production
    (fun t => (S t).capability) (fun t => (S t).growGain)
    (fun t => usableFrontier (S t)) xi
    alpha gamma rho beta halpha hgamma hrho hC0 h_cone0 h_step h_gain_prod
    h_dyn h_C_cap hbeta T

/-! ## Полнота генератора кандидатов -/

variable {A : Type} [Fintype A] [Nonempty A]

/-- `CandidateComplete gen G safe eps`: для любого g и
safe-кандидата `astar` с `g − eps ≤ G astar` существует
`a` с `gen a`, `safe a` и `g − eps ≤ G a`. Посылка о
генерации, не теорема. -/
def CandidateComplete (gen : A → Prop) [DecidablePred gen]
    (G : A → ℝ) (safe : A → Prop) [DecidablePred safe] (eps : ℝ) : Prop :=
  ∀ (g : ℝ) (astar : A),
    safe astar → g - eps ≤ G astar →
      ∃ a, gen a ∧ safe a ∧ g - eps ≤ G a

/-- При `0 ≤ eps`, `CandidateComplete gen G safe eps`,
`safe a₀` и `eps < G a₀` существует `a'` с `gen a'`,
`safe a'`, `0 < G a'` и `G a₀ − eps ≤ G a'`. -/
theorem candidate_completeness_find
    (G : A → ℝ) (gen safe : A → Prop) [DecidablePred gen] [DecidablePred safe]
    (eps : ℝ) (heps : 0 ≤ eps)
    (hgen : CandidateComplete gen G safe eps)
    (a₀ : A) (hsafe₀ : safe a₀) (hpos : eps < G a₀) :
    ∃ a', gen a' ∧ safe a'
      ∧ 0 < G a' ∧ G a₀ - eps ≤ G a' := by
  -- генератор покрывает a₀ на уровне g := G a₀
  obtain ⟨a, hgena, hsafea, hgaina⟩ := hgen (G a₀) a₀ hsafe₀ (by linarith)
  -- argmax по сгенерированным safe-кандидатам (содержит a)
  classical
  set cand : A → Prop := fun a => gen a ∧ safe a with hcand
  have hamem : a ∈ safeCandidates cand := by
    simp only [safeCandidates, Finset.mem_filter, Finset.mem_univ, true_and,
      hcand]
    exact ⟨hgena, hsafea⟩
  obtain ⟨a', ha'mem, hpos', hle⟩ :=
    self_development_find G cand a hamem
      (by linarith [hgaina, hpos])
  refine ⟨a', ?_, ?_, hpos', ?_⟩
  · exact ((Finset.mem_filter.mp ha'mem).2).1
  · exact ((Finset.mem_filter.mp ha'mem).2).2
  · linarith

end Hagi.Growth

namespace Hagi
export Hagi.Growth (usableFrontier capability_takeoff_state CandidateComplete candidate_completeness_find)
end Hagi
