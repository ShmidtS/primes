/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Energy.Landauer

/-!
# Семейство памяти (объединённое)

WeightTying, MemoryConsolidation, GDNRAM. Имена
деклараций сохранены.
-/

/-!
# Weight Tying (источник №49)

Источник №49: Press & Wolf, "Using the Output Embedding to
Improve Language Models" (arXiv 1608.05859). Совместное
использование матрицы входных эмбеддингов и выходной
проекции (softmax-слой): E_out = E_in^T — параметры
проекции УДЕШАЕТСЯ ВДВОЕ (mn вместо 2mn), а связка
пространств улучшает маленькие модели.

Формализованное ядро (строгое):
- `wt_params`: связанная конфигурация — mn параметров;
- `untied_params`: раздельная — 2mn;
- `wt_saving`: при mn > 0 связывание СТРОГО экономит
  параметры (mn < 2mn).
-/

namespace Hagi.Model.WeightTying

/-- Параметры связанной конфигурации. -/
noncomputable def wtParams (m n : ℝ) : ℝ := m * n

/-- Параметры раздельной конфигурации. -/
noncomputable def untiedParams (m n : ℝ) : ℝ := 2 * m * n

/-- СТРОГАЯ экономия при ненулевом словаре. -/
theorem wt_saving (m n : ℝ) (hmn : 0 < m * n) :
    wtParams m n < untiedParams m n := by
  unfold wtParams untiedParams
  nlinarith [hmn]

end Hagi.Model.WeightTying

-- Мост Cortex (2610.20399) ↔ термодинамика HAGI.
open Hagi.Energy

namespace Hagi.Model

/-!
Мост Cortex (arXiv 2610.20399) ↔ термодинамика HAGI:
консолидация контекста в параметрическую память подчинена
ленандауэровскому бюджету — записываемые биты ограничены
энергией цикла; консолидация n бит невозможна при
недостаточном бюджете.
-/

/-- Кэп на биты консолидации: запись F бит параметров в
энергобюджете B при ленандауэровской цене cUnit за бит.
(переадресация на ядро `written_bits_cap`.) -/
@[deprecated Hagi.Energy.written_bits_cap]
theorem consolidation_bits_cap (B cUnit F : ℝ) (hcUnit : 0 < cUnit)
    (h_emp_memwrite : cUnit * F ≤ B) :
    F ≤ B / cUnit :=
  Hagi.Energy.written_bits_cap B cUnit F hcUnit h_emp_memwrite

/-- Нет бесплатной консолидации: если требуется записать n бит
(весь контекст), а бюджет строго меньше n·cUnit, запись
невозможна — энергия против B. -/
theorem consolidation_no_free_lunch (B cUnit n : ℝ)
    (_hcUnit : 0 < cUnit) (_hn : 0 ≤ n)
    (hstrict : B < cUnit * n) :
    ¬ (cUnit * n ≤ B) := by
  intro hcontra
  linarith

end Hagi.Model

/-!
# GDNRAM — точная адресуемая память (источник №62:
# Qwenputer-эксперимент, divagr.com 2026; теоретическая
# основа — Gated DeltaNet 2404.01648 с one-hot адресами;
# аудит v10 §5.3)

Идея: GDN-слой с gate/write-strength = 1 и one-hot
адресами ведёт себя как ТОЧНАЯ адресуемая RAM: запись в
строку i заменяет её содержимое, чтение по i возвращает
записанное значение в точности. Формализуем контракт
exact-RAM: запись/чтение/перезапись на матрице состояния.
-/

namespace Hagi.Model.GDNRAM

variable {m n : ℕ}

/-- ЗАПИСЬ: обновление строки i матрицы состояния значением
v (one-hot адресация). -/
def ramWrite (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (v : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.updateRow S i v

/-- ЧТЕНИЕ: строка i матрицы (one-hot запрос e_i через
умножение: e_iᵀ · S = строка i). -/
def ramRead (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Fin n → ℝ := S i

/-- ИСТОЧНИК №62, УРОВЕНЬ 1: ТОЧНОЕ ЧТЕНИЕ — после записи
значения v в строку i чтение по i возвращает v В ТОЧНОСТИ
(контракт exact-RAM; Mathlib updateRow_self). -/
theorem ram_read_after_write
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (v : Fin n → ℝ) :
    ramRead (ramWrite S i v) i = v := by
  unfold ramRead ramWrite
  exact Matrix.updateRow_self

/-- УРОВЕНЬ 1b: НЕЗАВИСИМОСТЬ ДРУГИХ СТРОК — запись в
строку i не меняет содержимое любой другой строки j ≠ i
(адресуемость: строки изолированы). -/
theorem ram_write_independent
    (S : Matrix (Fin m) (Fin n) ℝ) (i j : Fin m)
    (v : Fin n → ℝ) (h : j ≠ i) :
    ramRead (ramWrite S i v) j = S j := by
  unfold ramRead ramWrite
  exact Matrix.updateRow_ne h

/-- УРОВЕНЬ 2: ИДЕМПОТЕНТНОСТЬ ПЕРЕЗАПИСИ — двойная запись
того же значения равна одинарной (повторная запись не
искажает состояние). -/
theorem ram_write_idem
    (S : Matrix (Fin m) (Fin n) ℝ) (i : Fin m)
    (v : Fin n → ℝ) :
    ramWrite (ramWrite S i v) i v = ramWrite S i v := by
  unfold ramWrite
  funext j k
  by_cases hj : j = i
  · subst hj
    simp [Matrix.updateRow_self]
  · simp [Matrix.updateRow_ne hj]

end Hagi.Model.GDNRAM
