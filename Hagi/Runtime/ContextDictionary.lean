/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

/-!
# ContextDictionary — причинные словари точного обхода и их безошибочность

`HagiOptimalLM.bypass_fit/bypass_apply` (optimal_lm.py): словарь контекстов
(5 и 3 байта) отвечает следующим байтом, если все наблюдённые продолжения
контекста совпадают и их не меньше порога; противоречивый контекст
помечается сбойным навсегда.

* `answer` — ответ словаря: единообразные продолжения ≥ `k` → `some b`, иначе `none`.
* `answer_correct_on_fit` — на обученном потоке ответ либо истинный байт, либо
  отказ: ложных ответов нет.
* `answer_none_of_contradiction` — контекст с двумя разными продолжениями не
  отвечает никогда; добавление наблюдений не превращает отказ в ответ.

Граница: на новом потоке словарь может ошибаться; сертификат только для fit.
-/

namespace Hagi.Runtime.ContextDictionary

variable {α : Type*} [DecidableEq α]
/-- Словарь контекстов: наблюдения «за контекст идёт байт». -/
abbrev Dict (α : Type*) := List (List α × α)
/-- Продолжения контекста в словаре. -/
def nexts (D : Dict α) (ctx : List α) : List α := (D.filter fun o => o.1 = ctx).map Prod.snd
/-- Все элементы списка равны `b`. -/
def Uniform (l : List α) (b : α) : Prop := ∀ x ∈ l, x = b
theorem uniform_all (l : List α) (b : α) (h : Uniform l b) : l.all (· = b) = true := by
  rw [List.all_eq_true]; exact fun x hx => decide_eq_true (h x hx)
/-- Ответ: первое продолжение `b`, если все продолжения равны `b` и их не меньше
`k`; иначе отказ (`none`). -/
def answer (D : Dict α) (k : ℕ) (ctx : List α) : Option α :=
  ((nexts D ctx).head?).bind fun b =>
    if k ≤ (nexts D ctx).length && (nexts D ctx).all (· = b) then some b else none
/-- Словарь обучен на потоке: каждое окно длины `n` в нём записано. -/
def FitsStream (D : Dict α) (n : ℕ) (xs : List α) : Prop :=
  ∀ i (h : i < xs.length), n ≤ i → ((xs.take i).drop (i - n), xs.get ⟨i, h⟩) ∈ D
theorem answer_eq_some (D : Dict α) (k : ℕ) (ctx : List α) (b : α)
    (hb : b ∈ nexts D ctx) (hall : Uniform (nexts D ctx) b) (hk : k ≤ (nexts D ctx).length) :
    answer D k ctx = some b := by
  have hne : nexts D ctx ≠ [] := fun h => by rw [h] at hb; exact absurd hb (by simp)
  have hhead : (nexts D ctx).head? = some b := by
    rw [List.head?_eq_some_head hne, hall _ (List.head_mem hne)]
  unfold answer
  rw [hhead]
  simp only [Option.bind_some]
  have hcond : (decide (k ≤ (nexts D ctx).length) && (nexts D ctx).all (· = b)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, uniform_all _ _ hall, hk, and_self]
  rw [hcond]
  rfl
theorem answer_eq_none (D : Dict α) (k : ℕ) (ctx : List α)
    (h : ∀ b, b ∈ nexts D ctx → ¬ (Uniform (nexts D ctx) b ∧ k ≤ (nexts D ctx).length)) :
    answer D k ctx = none := by
  unfold answer
  cases hh : (nexts D ctx).head? with
  | none => rfl
  | some b =>
      simp only [Option.bind_some]
      rw [ite_eq_right]
      · intro hc
        have hb : b ∈ nexts D ctx := List.mem_of_head? hh
        rw [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact h b hb ⟨fun x hx => of_decide_eq_true (List.all_eq_true.1 hc.2 x hx), hc.1⟩
/-- На обучающем потоке словарь не ошибается: ответ либо истинный байт, либо отказ. -/
theorem answer_correct_on_fit (D : Dict α) (n k : ℕ) (xs : List α) (hfit : FitsStream D n xs)
    (i : ℕ) (hi : n ≤ i) (hlt : i < xs.length) :
    answer D k ((xs.take i).drop (i - n)) = some (xs.get ⟨i, hlt⟩) ∨
    answer D k ((xs.take i).drop (i - n)) = none := by
  have hmem : ((xs.take i).drop (i - n), xs.get ⟨i, hlt⟩) ∈ D := hfit i hlt hi
  have hinn : xs.get ⟨i, hlt⟩ ∈ nexts D ((xs.take i).drop (i - n)) :=
    List.mem_map_of_mem (List.mem_filter_of_mem hmem (by simp))
  by_cases hall : Uniform (nexts D ((xs.take i).drop (i - n))) (xs.get ⟨i, hlt⟩)
  · by_cases hk : k ≤ (nexts D ((xs.take i).drop (i - n))).length
    · exact Or.inl (answer_eq_some _ _ _ _ hinn hall hk)
    · exact Or.inr (answer_eq_none _ _ _ fun b hb ⟨h1, h2⟩ => hk h2)
  · refine Or.inr (answer_eq_none _ _ _ fun d dmem ⟨dun, _⟩ => ?_)
    exact hall fun x hx => (dun x hx).trans (dun _ hinn).symm
/-- Контекст с противоречием не отвечает никогда: добавление наблюдений не
превращает отказ в ответ. -/
theorem answer_none_of_contradiction (D : Dict α) (k : ℕ) (ctx : List α) (b c : α)
    (hb : (ctx, b) ∈ D) (hc : (ctx, c) ∈ D) (hbc : b ≠ c) : answer D k ctx = none := by
  have h1 : b ∈ nexts D ctx := List.mem_map_of_mem (List.mem_filter_of_mem hb (by simp))
  have h2 : c ∈ nexts D ctx := List.mem_map_of_mem (List.mem_filter_of_mem hc (by simp))
  refine answer_eq_none D k ctx fun d dmem ⟨dun, _⟩ => ?_
  exact hbc ((dun b h1).trans (dun c h2).symm)

end Hagi.Runtime.ContextDictionary
