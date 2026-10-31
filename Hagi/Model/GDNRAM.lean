import Mathlib

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
