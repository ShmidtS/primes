/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
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

end Hagi.Model.RamProtocol
