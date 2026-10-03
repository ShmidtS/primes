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
# P0-2: связывание процессов-теней с полями состояния + P0-3: полнота кандидатов

Аудит R119 (§4–5, §9, P0-2/P0-3):

**P0-2**: `sustained_takeoff_from_production` (R107) доказывала
экспоненциальный рост для ОТДЕЛЬНОЙ последовательности `C` —
shadow process, параллельного `S_{t+1} = cycle(S_t)`. Этот
модуль связывает их в одну динамическую систему:
`C_t := (S_t).capability`, `G_t := (S_t).growGain`,
`D_t := usableFrontier (S_t)` — и переэкземплярирует takeoff:
рост доказывается для НАСТОЯЩЕГО поля состояния, а не тени.

* `usableFrontier` — измеримое поле frontier (dataField:
  D-дивергенция смеси данных; семантика — свежая
  информация/разнообразие, источник renewal).
* `capability_takeoff_state` — P0-2-теорема: при связанных
  последовательностях и тех же динамических посылках
  `(S T).capability ≥ (S 0).capability · (1+α)^T`.

**P0-3**: `CandidateComplete` — полнота генератора кандидатов:
если существует safe upgrade a* с gain ≥ g, генератор выдаёт
safe-кандидат a с gain ≥ g − ε. `candidate_completeness_find`
компонует её с `self_development_find` (R118): полнота
генератора + существование положительного upgrade ⇒
argmax-controller находит положительный upgrade —
рекурсивная цепочка generation → verification → selection.

**Честные границы**: посылки динамики (h_step, h_gain_prod,
h_dyn, h_C_cap, hβ) остаются измеряемыми (R117 сертифицирует
h_dyn; training theorem для h_step/gain — audit P0-1/P0-5,
открыто); полнота генератора — посылка (теорема о самой
генерации — открыта, см. докстринги).
-/

open Finset

namespace Hagi

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ## P0-2: связывание теней с состоянием -/

/-- Измеримый frontier состояния: D-поле смеси данных
(дивергенция распределения данных; семантика — свежая
информация/разнообразие, источник renewal). -/
def usableFrontier (S : GrowthState X) : ℝ := S.dataField

/-- **P0-2**: экспоненциальный takeoff НАСТОЯЩЕГО поля
capability. Последовательности связаны с состоянием
(C_t = S_t.capability, G_t = S_t.growGain,
D_t = usableFrontier S_t), динамика — те же посылки R107;
доказательство — переэкземпляриация
`sustained_takeoff_from_production`: рост больше не shadow
process, а свойство последовательности состояний. -/
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

/-! ## P0-3: полнота генератора кандидатов -/

variable {A : Type} [Fintype A] [Nonempty A]

/-- **Полнота генератора** (audit §9/P0-3): если существует
safe-кандидат с gain ≥ g, генератор выдаёт safe-кандидат с
gain ≥ g − ε. Это посылка о генерации (рекурсивное
саморазвитие требует достаточно полного пространства
кандидатов); сам генератор — реализация, не теорема. -/
def CandidateComplete (gen : A → Prop) [DecidablePred gen]
    (G : A → ℝ) (safe : A → Prop) [DecidablePred safe] (eps : ℝ) : Prop :=
  ∀ (g : ℝ) (astar : A),
    safe astar → g - eps ≤ G astar →
      ∃ a, gen a ∧ safe a ∧ g - eps ≤ G a

/-- **P0-3-композиция**: полнота генератора (ε-margin) +
существование safe upgrade с gain > ε ⇒ argmax-controller по
СГЕНЕРИРОВАННЫМ safe-кандидатам находит upgrade со строго
положительным ИСТИННЫМ gain, не худшим G(a₀) − ε. Полный цикл
generation → verification → selection даёт положительный
upgrade — рекурсивное саморазвитие на уровне одного шага. -/
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

end Hagi
