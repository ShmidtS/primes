/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Learning.ContinualForgetting

/-!
# Rollback — откат приёма блока должен быть полным

`unified.py` (9baf5d6): откат приёма на месте обязан вернуть не только
параметры (`prm.copy_(inc)`), но и число блоков роста, заморозку и словари
обхода (`_restore_blocks`). До фикса «откат молча обнулял блок»: параметры
инкумбента при новых блоках — неконсистентное состояние.

* `GrowState` — параметры, блоки, заморозка, словари;
* `full` — точный откат (все четыре);
* `paramsOnly` — частичный откат (только параметры);
* `paramsOnly_ne_full` — если кандидат изменил блоки, заморозку или словари,
  частичный откат ≠ полному.

`unified.py` (52be847): откатанный домен записывается в книгу с признаком
`rolled_back` и честным CE — CE установленной (откатанной) модели.

* `Entry` — запись: `ce`, `rolled_back`;
* `honestCE` — CE книги: откатан ⇒ установленная модель, принят ⇒ кандидат;
* `honestCE_rolled_back`, `honestCE_accepted`;
* `rolled_back_forget_zero` — откатанный домен не забывается (прирост CE 0).

Тот же коммит: снимок весов стал словарём по именам (`_param_name`). До фикса
позиционный `zip(params, incumbent_state)` после вставки блока посередине
присваивал параметрам чужие снимки.

* `positionalRestore` — параметр `i` ← снимок `i` (zip);
* `namedRestore` — параметр по имени ← снимок по имени; новые имена не трогаются;
* `positional_misaligns` — блок, вставленный посередине, смещает позиционный
  откат (`y` получает `a` вместо `b`), именованный — точен;
* `positional_length` — позиционный обрезает новые параметры до длины снимка;
* `named_length`, `named_keeps_new` — именованный сохраняет длину и новые.
-/

namespace Hagi.Unified.Rollback

/-- Полное состояние роста: параметры `P`, число блоков `k`, маска заморозки
`F`, словари обхода `D`. Приём блока меняет все четыре. -/
structure GrowState (P K F D : Type) where
  params : P
  blocks : K
  frozen : F
  dicts : D
/-- Точный откат: все четыре компоненты возвращаются к снимку. -/
def full (snap : GrowState P K F D) (_cur : GrowState P K F D) : GrowState P K F D := snap
/-- Частичный откат: только параметры (как до 9baf5d6: блоки, заморозка и
словари оставались от принятого кандидата). -/
def paramsOnly (snap cur : GrowState P K F D) : GrowState P K F D :=
  { cur with params := snap.params }
/-- Частичный откат не равен полному, если кандидат изменил блоки, заморозку
или словари — состояние неконсистентно: новые блоки при старых параметрах. -/
theorem paramsOnly_ne_full (snap cur : GrowState P K F D)
    (h : cur.blocks ≠ snap.blocks ∨ cur.frozen ≠ snap.frozen ∨ cur.dicts ≠ snap.dicts) :
    paramsOnly snap cur ≠ full snap cur := by
  intro heq
  rcases h with h | h | h
  · exact h (by have := congrArg GrowState.blocks heq; simpa [paramsOnly, full] using this)
  · exact h (by have := congrArg GrowState.frozen heq; simpa [paramsOnly, full] using this)
  · exact h (by have := congrArg GrowState.dicts heq; simpa [paramsOnly, full] using this)

/-- Запись домена в книге: CE и признак отката. -/
structure Entry where
  ce : ℝ
  rolled_back : Bool
/-- Честная запись CE (52be847): для откатанного домена пишется CE
установленной модели, для принятого — CE кандидата (модель и есть кандидат). -/
def honestCE (installed candidate : ℝ) (rolled_back : Bool) : ℝ :=
  if rolled_back then installed else candidate
/-- CE книги для откатанного домена — это CE установленной модели. -/
theorem honestCE_rolled_back (installed candidate : ℝ) :
    honestCE installed candidate true = installed := by simp [honestCE]
/-- CE книги для принятого домена — CE кандидата. -/
theorem honestCE_accepted (installed candidate : ℝ) :
    honestCE installed candidate false = candidate := by simp [honestCE]
/-- Откатанный домен не забывается моделью: прирост CE на нём равен нулю
относительно снимка (модель после отката = модель до приёма). -/
theorem rolled_back_forget_zero (pre installed : ℝ) (h : installed = pre)
    (post : Fin 1 → ℝ) (hpost : post 0 = installed) :
    Hagi.Learning.ContinualForgetting.forget (fun _ => pre) post 0 = 0 := by
  unfold Hagi.Learning.ContinualForgetting.forget
  rw [hpost, h]; ring

/-- Позиционный откат: параметр с индексом `i` получает снимок с индексом `i`
(`zip(model.params(), incumbent_state)` до 52be847). -/
def positionalRestore (snap : List ℝ) (cur : List ℝ) : List ℝ :=
  (cur.zip snap).map (fun (_, s) => s)
/-- Именованный откат: параметр с именем `n` получает снимок `snap[n]`, если он
был до приёма; новые параметры не трогаются. -/
def namedRestore (snap : List (String × ℝ)) (cur : List (String × ℝ)) :
    List (String × ℝ) :=
  cur.map (fun (n, v) => (n, match snap.lookup n with | some s => s | none => v))
/-- Позиционный откат со вставленным блоком: параметры после вставки получают
чужие снимки. Снимок `[a, b]` (имена `x`, `y`), кандидат `[(x,a), (w,0), (y,b)]`
(блок `w` вставлен посередине): позиционно `y` получает `a` вместо `b`. -/
theorem positional_misaligns :
    positionalRestore [1, 2] [0, 0, 0] = [1, 2] ∧
      namedRestore [("x", 1), ("y", 2)] [("x", 0), ("w", 0), ("y", 0)]
        = [("x", 1), ("w", 0), ("y", 2)] := by
  unfold positionalRestore namedRestore
  simp only [List.zip_cons_cons, List.zip_nil_right, List.zip_nil_left, List.map_cons,
    List.map_nil]
  have e1 : ("w" == "x") = false := by decide
  have e2 : ("w" == "y") = false := by decide
  have e3 : ("x" == "x") = true := by decide
  have e4 : ("y" == "y") = true := by decide
  simp only [List.lookup, e1, e2, e3, e4, if_false, if_true, Option.getD_some, reduceIte,
    and_true]
  exact ⟨trivial, rfl⟩
/-- Позиционный откат молча обрезает новые параметры (zip по более короткому
списку) — длина результата = длина снимка, а не модели. -/
theorem positional_length (snap cur : List ℝ) :
    (positionalRestore snap cur).length = min snap.length cur.length := by
  simp [positionalRestore, min_comm]
/-- Именованный откат никогда не меняет длину и не трогает новые имена. -/
theorem named_length (snap cur : List (String × ℝ)) :
    (namedRestore snap cur).length = cur.length := by
  simp [namedRestore]
theorem named_keeps_new (snap : List (String × ℝ)) (n : String) (v : ℝ)
    (h : n ∉ snap.map Prod.fst) :
    namedRestore snap [(n, v)] = [(n, v)] := by
  unfold namedRestore
  simp only [List.map_cons, List.map_nil]
  have hl : List.lookup n snap = none := by
    apply (List.lookup_eq_none_iff).2
    intro p hp
    have hmem : p.1 ∈ snap.map Prod.fst := List.mem_map_of_mem hp
    have hne : n ≠ p.1 := fun he => h (he ▸ hmem)
    simp [hne]
  simp only [List.map_cons, List.map_nil, hl, ite_true]

end Hagi.Unified.Rollback
