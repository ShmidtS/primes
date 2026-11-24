/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
set_option linter.unusedSectionVars false

/-!
# OEComplete — полнота поиска с Observational Equivalence дедупликацией

HAGI_v2 synthesize_batched_mdl
прунит программы с уже виденным вектором значений на пробах
(OE hash-consing поверх Levin priority queue). Бенчмарк:
naive — 6478 узлов без решения; Levin+OE+MITM — 896 узлов до
решения. Этот модуль — дискретная теорема корректности прунинга:
OE-дедупликация НЕ теряет решения.

Модель (честная, KISS):

* программа `p : Prog` абстрактна; наблюдение `obsV p : Obs` —
  вектор значений программы на ФИКСИРОВАННЫХ пробах
  (навешивание проб — часть `obsV`);
* глубинно-ограниченное пространство программ — явный список
  `space : List Prog` (перечисление всех программ глубины ≤ d;
  конечность структурная);
* OE-дедуп поиск `oeFirsts obsV space` — структурная рекурсия:
  программа сохраняется iff её obs-вектор ещё не представлен в
  выдаче → ровно один (первый достигнутый) представитель на
  OE-класс.

Что доказано:

* (a) `oe_classes_partition` — наблюдательная эквивалентность
  `obsV p = obsV q` — подлинная эквивалентность (Setoid):
  OE-классы корректно разбивают пространство;
* (b) `oe_search_complete` (main) — если в пространстве есть
  программа `p`, совпадающая со спецификацией на пробах, то
  OE-дедуп поиск вернёт `q` с `obsV q = obsV p`: решение на
  пробах СОХРАНЯЕТСЯ (первый представитель каждого OE-класса
  достигается). Полнота — ОТНОСИТЕЛЬНО ПРОБ: утверждается
  совпадение векторов значений на фиксированном пробном
  наборе, НЕ семантическая эквивалентность программ (это
  отдельный вопрос внешнего плана);
* (c) `oe_search_terminates` — обход с дедупликацией не длиннее
  полного перечисления конечного пространства
  (`(oeFirsts obsV space).length ≤ space.length`): терминация
  структурная, бюджет дедупа ≤ бюджета naive-перебора.
-/

namespace Hagi.Theory.OEComplete

variable {Prog : Type} {Obs : Type} [DecidableEq Obs] (obsV : Prog → Obs)

/-- OE-дедуп поиск: первый достигнутый представитель каждого
OE-класса (obs-вектора) сохраняется, повторы отбрасываются.
Структурная рекурсия по пространству — терминация бесплатна. -/
def oeFirsts : List Prog → List Prog
  | [] => []
  | p :: ps =>
      let rest := oeFirsts ps
      if rest.any (fun q => obsV q = obsV p) then rest else p :: rest

/-- Наблюдательная эквивалентность (по фиксированным пробам) —
Setoid на программах: классы = множества программ с равными
obs-векторами. -/
def oeSetoid : Setoid Prog where
  r p q := obsV p = obsV q
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- (a) OE-классы образуют разбиение: отношение `obsV p = obsV q`
— рефлексивно, симметрично, транзитивно (эквивалентность). -/
theorem oe_classes_partition : Equivalence (fun p q : Prog => obsV p = obsV q) :=
  (oeSetoid obsV).iseqv

/-- (b, main) OE-полнота: если программа `p` со спецификационным
obs-вектором есть в глубинно-ограниченном пространстве, поиск с
OE-дедупликацией вернёт `q` с тем же obs-вектором — решение на
пробах не теряется (первый представитель каждого OE-класса
достигается). Полнота ОТНОСИТЕЛЬНО ПРОБ: `obsV q = obsV p`, не
семантическая эквивалентность. -/
theorem oe_search_complete {p : Prog} {space : List Prog} (hp : p ∈ space) :
    ∃ q ∈ oeFirsts obsV space, obsV q = obsV p := by
  induction space generalizing p with
  | nil => cases hp
  | cons a as ih =>
    show ∃ q ∈ (if (oeFirsts obsV as).any (fun q => obsV q = obsV a)
        then oeFirsts obsV as else a :: oeFirsts obsV as), obsV q = obsV p
    by_cases h : (oeFirsts obsV as).any (fun q => obsV q = obsV a)
    · rw [if_pos h]
      rcases List.mem_cons.mp hp with hpa | hpa
      · rcases List.any_eq_true.mp h with ⟨q, hq_mem, hq⟩
        refine ⟨q, hq_mem, ?_⟩
        rw [hpa]
        simpa using of_decide_eq_true hq
      · obtain ⟨q, hq_mem, hq_obs⟩ := ih hpa
        exact ⟨q, hq_mem, hq_obs⟩
    · rw [if_neg h]
      rcases List.mem_cons.mp hp with hpa | hpa
      · exact ⟨a, List.mem_cons_self, by simp [hpa]⟩
      · obtain ⟨q, hq_mem, hq_obs⟩ := ih hpa
        exact ⟨q, List.mem_cons_of_mem _ hq_mem, hq_obs⟩

/-- (c) Терминация и бюджет: OE-дедуп обход не длиннее полного
перечисления конечного (глубина ≤ d) пространства. -/
theorem oe_search_terminates (space : List Prog) :
    (oeFirsts obsV space).length ≤ space.length := by
  induction space with
  | nil => simp [oeFirsts]
  | cons a as ih =>
    show (if (oeFirsts obsV as).any (fun q => obsV q = obsV a)
        then oeFirsts obsV as else a :: oeFirsts obsV as).length ≤ (a :: as).length
    by_cases h : (oeFirsts obsV as).any (fun q => obsV q = obsV a)
    · rw [if_pos h]
      exact ih.trans (Nat.le_succ _)
    · rw [if_neg h]
      simp only [List.length_cons]
      omega

end Hagi.Theory.OEComplete
