/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Hagi.Model.Memory

/-!
# RamProtocol: протокол store/load + нормализация заикания (E6)

Обзор «HAGI Neural Computer» (E6, Python-сторона: RAM discovery /
shared vocab / stutter chunker) требует формализации протокола
store/load поверх идеального one-hot RAM и ядра stutter-чанкинга
(схлопывание подряд идущих дубликатов адресов).

Носитель — GDNRAM (`Hagi.Model.GDNRAM`): запись `ramWrite`
(замена строки one-hot адресом), чтение `ramRead` (строка i).
Идеальный roundtrip уже доказан как `ram_read_after_write` и
`gdn_ram_roundtrip`; здесь он упакован в протольный API
(`ramStore`/`ramLoad`) с теоремой roundtrip и изоляции адресов.

Stutter-чанкер: `stutterNorm` схлопывает подряд идущие дубликаты
([1,1,2,2,1] → [1,2,1]); доказаны идемпотентность, монотонность
длины и сохранение первого/последнего элементов.

Мост: `ram_load_stutter_head` — первый адрес заикающейся
последовательности и её нормализованной версии порождают
одинаковое первое чтение (без промежуточных записей повторы
адресов не меняют результат). Полная эквивалентность потоков
чтения (чанк на серию повторов) — следующая ступень, не заявлена.
-/

namespace Hagi.Model.RamProtocol

variable {m n : ℕ}

/-! ## Протокол store/load на носителе GDNRAM -/

/-- ЗАПИСЬ протокола: значение v в слот i (one-hot адресация,
делегирует `Hagi.Model.GDNRAM.ramWrite`). -/
def ramStore (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (v : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Hagi.Model.GDNRAM.ramWrite S i v

/-- ЧТЕНИЕ протокола: содержимое слота i (one-hot запрос,
делегирует `Hagi.Model.GDNRAM.ramRead`). -/
def ramLoad (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Fin n → ℝ := S i

/-- PROTOCOL ROUNDTRIP: store затем load по тому же адресу
возвращает записанное значение В ТОЧНОСТИ (упаковка идеального
roundtrip `ram_read_after_write` / `gdn_ram_roundtrip` как API
протокола). -/
theorem ram_store_load_roundtrip (S : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (v : Fin n → ℝ) :
    ramLoad (ramStore S i v) i = v :=
  Hagi.Model.GDNRAM.ram_read_after_write S i v

/-- ИЗОЛЯЦИЯ АДРЕСОВ (one-hot independence, ideal-mode): load по
ДРУГОМУ адресу j ≠ i не затронут записью в i (инертность соседних
слотов — режим lag-1 выравнивания `gdn_lag1_read_miss`). -/
theorem ram_store_isolation (S : Matrix (Fin m) (Fin n) ℝ)
    (i j : Fin m) (v : Fin n → ℝ) (h : j ≠ i) :
    ramLoad (ramStore S i v) j = ramLoad S j :=
  Hagi.Model.GDNRAM.ram_write_independent S i j v h

/-! ## Нормализация заикания (ядро Python stutter chunker) -/

variable {α : Type*} [DecidableEq α]

/-- Один шаг свёртки: x отбрасывается, если он дублирует голову
уже нормализованного хвоста (схлопывание серии повторов). -/
def stStep (x : α) (acc : List α) : List α :=
  match acc with
  | y :: _ => if x = y then acc else x :: acc
  | [] => [x]

/-- Схлопывание подряд идущих дубликатов: ядро stutter-чанкинга
([1,1,2,2,1] → [1,2,1]; рекурсия справа, одношаговая индукция). -/
def stutterNorm (l : List α) : List α := l.foldr stStep []

@[simp] theorem stutterNorm_nil :
    stutterNorm ([] : List α) = [] := by
  simp only [stutterNorm, List.foldr_nil]

@[simp] theorem stutterNorm_cons (a : α) (l : List α) :
    stutterNorm (a :: l) = stStep a (stutterNorm l) := by
  simp only [stutterNorm, List.foldr_cons]

/-- Шаг нормализации никогда не выдаёт пустой список. -/
theorem stStep_ne_nil (x : α) (acc : List α) :
    stStep x acc ≠ [] := by
  match acc with
  | [] => simp [stStep]
  | c :: cu =>
    by_cases h : x = c
    · simp [stStep, h]
    · simp [stStep, h]

/-- Нормализация непустого списка непуста. -/
theorem stutterNorm_ne_nil {l : List α} (hl : l ≠ []) :
    stutterNorm l ≠ [] := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    rw [stutterNorm_cons]
    intro h
    have := stStep_ne_nil a (stutterNorm t)
    contradiction

/-- Шаг нормализации удлиняет не более чем на единицу. -/
theorem stStep_length (x : α) (acc : List α) :
    (stStep x acc).length ≤ acc.length + 1 := by
  match acc with
  | [] => simp [stStep]
  | c :: cu =>
    by_cases h : x = c
    · simp [stStep, h]
    · have h3 : (stStep x (c :: cu)).length = (c :: cu).length + 1 := by
        simp [stStep, h]
      omega

/-- Нормализация не удлиняет список (чанков не больше, чем
токенов). -/
theorem stutterNorm_length_le (l : List α) :
    (stutterNorm l).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 := stStep_length a (stutterNorm t)
    have h2 : (a :: t).length = t.length + 1 := rfl
    rw [stutterNorm_cons]
    omega

/-- Первый элемент серии повторов сохраняется головой
нормализованного списка. -/
theorem stutterNorm_head (a : α) (l : List α) :
    (stutterNorm (a :: l)).head? = some a := by
  rw [stutterNorm_cons]
  cases h : stutterNorm l with
  | nil => simp [stStep]
  | cons c cu =>
    by_cases hac : a = c
    · simp [stStep, hac]
    · simp [stStep, hac]

/-- ПЕРВЫЙ сохраняется: голова нормализованного списка = голова
исходного (первый адрес потока не меняется чанкингом). -/
theorem stutterNorm_head? (l : List α) :
    l.head? = (stutterNorm l).head? := by
  match l with
  | [] => rfl
  | a :: t => rw [stutterNorm_head]; rfl

/-- Шаг нормализации сохраняет последний элемент непустого
хвоста. -/
theorem stStep_getLast? (x : α) {acc : List α} (hne : acc ≠ []) :
    (stStep x acc).getLast? = acc.getLast? := by
  match acc, hne with
  | c :: cu, _ =>
    by_cases h : x = c
    · simp [stStep, h]
    · simp [stStep, h, List.getLast?_cons_of_ne_nil]

/-- ПОСЛЕДНИЙ сохраняется: хвост нормализованного списка = хвост
исходного (последний адрес потока не меняется чанкингом). -/
theorem stutterNorm_getLast? (l : List α) :
    l.getLast? = (stutterNorm l).getLast? := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ht : t = []
    · subst ht; rfl
    · rw [stutterNorm_cons, stStep_getLast? a (stutterNorm_ne_nil ht),
        List.getLast?_cons_of_ne_nil ht]
      exact ih

/-- ИДЕМПОТЕНТНОСТЬ: повторная нормализация ничего не меняет
(norm ∘ norm = norm — повторный чанкинг стабильного потока
не создаёт новых чанков). -/
theorem stutterNorm_idempotent (l : List α) :
    stutterNorm (stutterNorm l) = stutterNorm l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ht : t = []
    · subst ht; simp [stStep]
    · have hne := stutterNorm_ne_nil ht
      cases h : stutterNorm t with
      | nil => exact absurd h hne
      | cons c cu =>
        rw [stutterNorm_cons] at ⊢
        rw [h] at ih ⊢
        by_cases hac : a = c
        · rw [show stStep a (c :: cu) = c :: cu by simp [stStep, hac]]
          exact ih
        · rw [show stStep a (c :: cu) = a :: c :: cu by simp [stStep, hac],
            stutterNorm_cons, ih]
          simp [stStep, hac]

/-! ## Мост: чтение по заикающейся последовательности адресов -/

/-- МОСТ (честное ядро stutter-чанкинга): первый адрес
заикающейся последовательности и её нормализованной версии
порождают ОДИНАКОВОЕ первое чтение RAM — без промежуточных
записей повторы адреса не меняют результат чтения
(`ramLoad` чист относительно состояния). Полная эквивалентность
потоков (чанк на серию повторов) — следующая ступень E6,
не заявлена. -/
theorem ram_load_stutter_head (S : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m) (l : List (Fin m)) :
    ((a :: l).map (ramLoad S)).head?
      = ((stutterNorm (a :: l)).map (ramLoad S)).head? := by
  simp only [List.map_cons, List.head?_cons, List.head?_map]
  rw [stutterNorm_head]
  rfl

/-! ## Якоря (decide) -/

/-- Якорь stutter-чанкинга: [1,1,2,2,1] → [1,2,1]. -/
example : stutterNorm [1,1,2,2,1] = [1,2,1] := by decide

/-- Якорь RAM на Fin 3: запись двух значений в два слота и
чтение ОБЕИХ по roundtrip-теореме протокола. -/
example : ∀ (S : Matrix (Fin 3) (Fin 2) ℝ) (v w : Fin 2 → ℝ),
    ramLoad (ramStore (ramStore S 0 v) 1 w) 0 = v ∧
    ramLoad (ramStore (ramStore S 0 v) 1 w) 1 = w := by
  intro S v w
  constructor
  · rw [ram_store_isolation _ 1 0 w (by decide)]
    exact ram_store_load_roundtrip S 0 v
  · exact ram_store_load_roundtrip _ _ _

/-!
## span offsets (аддитивное окно по смещению)

Модель адресов — `Fin m` (строки GDNRAM), без усечений:
каждый адрес конструируется корректным. Окно-адрес — explicit
mod-wrap (единственное честное сведение `base + off` к `Fin m`);
внутри окна перенос НЕ срабатывает (`ram_span_no_wrap`), так что
аддитивная семантика смещений точна, пока окно лежит в адресном
пространстве (Python RAM читает только обнаруженные in-range
спаны общего словаря).

Честная граница: сам DISCOVERY спанов общего словаря
(индуктивный, Python-сторона) НЕ заявлен.
-/

/-- ОКНО-АДРЕС: base + off с явным mod-переносом в Fin m
(премиза `hm : 0 < m`; усечения нет —  адреса всегда
корректны, перенос инертен внутри окна). -/
def ramSpanAddr {m : ℕ} (hm : 0 < m) (base : Fin m) (off : ℕ) :
    Fin m := ⟨(base.val + off) % m, Nat.mod_lt _ hm⟩

/-- ЧТЕНИЕ ПО СМЕЩЕНИЮ: значение в окне с базой base по индексу
off (`ramLoad` по окно-адресу `ramSpanAddr`). -/
def ramLoadSpan (S : Matrix (Fin m) (Fin n) ℝ) (base : Fin m)
    (off : ℕ) (hm : 0 < m) : Fin n → ℝ :=
  ramLoad S (ramSpanAddr hm base off)

/-- SPAN-ROUNDTRIP: запись по адресу base+off и чтение окном с
базой base по индексу off возвращают записанное значение
(композиция `ram_store_load_roundtrip` на окно-адресе). -/
theorem ram_span_offset_roundtrip (S : Matrix (Fin m) (Fin n) ℝ)
    (base : Fin m) (off : ℕ) (hm : 0 < m) (v : Fin n → ℝ) :
    ramLoadSpan (ramStore S (ramSpanAddr hm base off) v) base off hm
      = v :=
  ram_store_load_roundtrip S _ v

/-- ОКНО В ПРЕДЕЛАХ: чтение окном остаётся в адресном
пространстве — out-of-bounds невозможен конструктивно
(премизы `off < w`, `w ≤ m` — оконная дисциплина; валидность —
следствие mod-конструкции `ramSpanAddr`). -/
theorem ram_span_within (base : Fin m) (off w : ℕ) (hm : 0 < m)
    (_h : off < w) (_hw : w ≤ m) :
    (ramSpanAddr hm base off).val < m := by
  have := Nat.mod_lt (base.val + off) hm
  omega

/-- БЕЗ ПЕРЕНОСА: пока base + off < m, окно-адрес РАВЕН
base + off (mod-перенос не срабатывает — семантика смещений
точна внутри окна). -/
theorem ram_span_no_wrap (base : Fin m) (off : ℕ) (hm : 0 < m)
    (h : base.val + off < m) :
    (ramSpanAddr hm base off).val = base.val + off :=
  Nat.mod_eq_of_lt h

/-!
## разделение selection/gate (RamAccess)

Дисциплина Python-стороны: выбор адреса (диспетчер) отделён от
решения о допуске (gate); никаких захардкоженных token ID —
модель параметрична по типам адресов (`Fin m`) и значений
(`Fin n → ℝ`) ПО КОНСТРУКЦИИ.
-/
structure RamAccess (m n : ℕ) : Type where
  /-- Выбранный адрес (решение диспетчера). -/
  sel : Fin m
  /-- Флаг допуска (решение гейта). -/
  gate : Bool
  /-- Прочитанное значение (нет допуска — none). -/
  val : Option (Fin n → ℝ)

/-- СБОРКА ДОСТУПА: gate=true — допущенное чтение `ramLoad` по
sel; gate=false — none (гейт только фильтрует). -/
def ramAccess (S : Matrix (Fin m) (Fin n) ℝ) (a : Fin m)
    (g : Bool) : RamAccess m n where
  sel := a
  gate := g
  val := if g then some (ramLoad S a) else none

/-- ГЕЙТ НЕ ФАБРИКУЕТ: при gate=true и val=some w значение w
есть в точности `ramLoad` по выбранному адресу sel — допуск
только фильтрует, никогда не создаёт значений. -/
theorem ram_access_gate_sound (S : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m) (g : Bool) (w : Fin n → ℝ)
    (hg : (ramAccess S a g).gate = true)
    (hv : (ramAccess S a g).val = some w) :
    w = ramLoad S a := by
  cases g with
  | true =>
      simp only [ramAccess] at hv ⊢
      exact (Option.some.inj hv).symm
  | false => simp [ramAccess] at hg

/-- ВЫБОР НЕ МЕНЯЕТ ПАМЯТЬ: любые два допущенных доступа по
ТОМУ ЖЕ sel дают одно значение — `val` зависит только от
состояния и sel (selection чист: `ramAccess` не пишет, в
согласии с C303-изоляцией записей). -/
theorem ram_access_selection_free (S : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin m) (g₁ g₂ : Bool) (w₁ w₂ : Fin n → ℝ)
    (h₁ : (ramAccess S a g₁).val = some w₁)
    (h₂ : (ramAccess S a g₂).val = some w₂) :
    w₁ = w₂ := by
  cases g₁ <;> cases g₂ <;> simp_all [ramAccess]

/-! ## Якоря (decide) -/

/-- Якорь span-офсетов на Fin 8: окно с базой 2 и смещением 3
указывает на адрес 5. -/
example : (ramSpanAddr (by decide : 0 < 8) ⟨2, by decide⟩ 3).val
    = 5 := by decide

/-- Якорь span-офсетов: roundtrip через окно base=2 off=3. -/
example : ∀ (S : Matrix (Fin 8) (Fin 3) ℝ),
    ramLoadSpan (ramStore S
      (ramSpanAddr (by decide : 0 < 8) ⟨2, by decide⟩ 3)
      ![(0:ℝ),1,0]) ⟨2, by decide⟩ 3 (by decide)
      = ![(0:ℝ),1,0] := by
  intro S
  exact ram_span_offset_roundtrip S _ _ _ _

/-- Якорь гейт-фильтрации: gate=true — допущенное чтение,
gate=false — none. -/
example : ∀ (S : Matrix (Fin 8) (Fin 3) ℝ) (a : Fin 8),
    (ramAccess S a true).val = some (ramLoad S a) ∧
    (ramAccess S a false).val = none := by
  intro S a
  constructor <;> rfl

end Hagi.Model.RamProtocol
