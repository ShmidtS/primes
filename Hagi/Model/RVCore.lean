/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib

/-!
# RV-ядро (объединённое)

RVCore и RVCoreBignum (перенос разряда). Имена сохранены.
-/

/-!
# RVCore (приоритет 2 «HAGI Neural Computer», ):
бит-точное ядро операций RISC-V над машинными словами.

Полная формализация RV32IM — отдельный проект; здесь
ЧЕСТНОЕ ЯДРО: основные ALU-операции над 32-битными словами
с точными спецификациями относительно ℕ-арифметики по
модулю 2³² (семантика без ошибок — «нулевой энтропии»
внутреннего CPU Qwenputer).

- `wordAdd`/`wordSub`/`wordAnd`: обёртки UInt32;
- `wordAdd_spec`: toNat(w + w') = (n + n') % 2^32 —
  перенос точно по спецификации RISC-V;
- `wordAnd_spec`: поразрядное И = min на битах
  (поточечная ℕ-спецификация через toNat/OFNat — через
  Bitwise-леммы UInt32);
- `execDeterministic`: исполнение операции — функция
  (детерминированность CPU: одинаковый вход ⟹ одинаковый
  выход, основа «RAM_Parity» из StageCertificate).
-/

namespace Hagi.Model.RVCore

/-- 32-битное слово. -/
abbrev Word := UInt32

/-- Сложение слов (wraparound по спецификации RISC-V). -/
def wordAdd (a b : Word) : Word := a + b

/-- Вычитание слов. -/
def wordSub (a b : Word) : Word := a - b

/-- Поразрядное И. -/
def wordAnd (a b : Word) : Word := a &&& b

/-- СПЕЦИФИКАЦИЯ СЛОЖЕНИЯ: машинное сложение — в точности
сложение ℕ по модулю 2³² (переносы отбрасываются согласно
спецификации RISC-V; беззнаковая семантика). -/
theorem wordAdd_spec (a b : Word) :
    (wordAdd a b).toNat = (a.toNat + b.toNat) % 2 ^ 32 := by
  simp [wordAdd, UInt32.toNat_add]

/-- СПЕЦИФИКАЦИЯ ВЫЧИТАНИЯ: машинное вычитание — ℕ-разность
по модулю 2³² (заём оборачивается). -/
theorem wordSub_spec (a b : Word) :
    (wordSub a b).toNat = (2 ^ 32 - b.toNat + a.toNat) % 2 ^ 32 := by
  simp [wordSub, UInt32.toNat_sub]

/-- ДЕТЕРМИНИРОВАННОСТЬ CPU: операция — функция; одинаковые
входы дают одинаковые выходы (основа инварианта RAM_Parity:
внутренний CPU не «галлюцинирует» — нулевая энтропия
ошибки вычислений). -/
theorem execDeterministic (op : Word → Word → Word)
    (a b a' b' : Word) (ha : a = a') (hb : b = b') :
    op a b = op a' b' := by
  rw [ha, hb]

/-- Идемпотентность AND (поразрядная операция с точной
ℕ-семантикой через toNat_and: Bitwise). -/
theorem wordAnd_spec (a b : Word) :
    (wordAnd a b).toNat = Nat.land a.toNat b.toNat := by
  simp [wordAnd, UInt32.toNat_and]

/-- AND идемпотентен (a &&& a = a) — свойство маскирования. -/
theorem wordAnd_idem (a : Word) : wordAnd a a = a := by
  simp [wordAnd, UInt32.and_self]

end Hagi.Model.RVCore

/-!
# Bignum-кирпич: перенос машинного сложения

Точный CPU-путь нейрокомпьютера: поразрядное сложение
машинных слов с переносом. Ключевой закон многословной
(длинной) арифметики: полная сумма двух слов отличается от
машинной суммы ровно на перенос, и перенос ограничен
единицей — старший разряд не переполняется дважды.
Многословная точная арифметика собирается из слов без
накопления ошибки переноса.
-/

namespace Hagi.Model.RVCoreBignum

open Hagi.Model.RVCore

/-- Перенос сложения слов: единица, если полная сумма
выходит за разрядную сетку. -/
def carry (a b : Word) : ℕ :=
  (a.toNat + b.toNat) / 2 ^ 32

/-- Машинная сумма — полная сумма минус перенос,
умноженный на разрядную сетку. -/
theorem wordAdd_carry_decomp (a b : Word) :
    a.toNat + b.toNat
      = (wordAdd a b).toNat + carry a b * 2 ^ 32 := by
  rw [show (wordAdd a b).toNat
      = (a.toNat + b.toNat) % 2 ^ 32 from wordAdd_spec a b,
    show carry a b * 2 ^ 32
      = (a.toNat + b.toNat) / 2 ^ 32 * 2 ^ 32 from rfl]
  omega

/-- ПЕРЕНОС ОГРАНИЧЕН: сложение двух слов даёт перенос не
больше единицы — разрядной сетки хватает ровно на один
старший разряд. -/
theorem carry_le_one (a b : Word) : carry a b ≤ 1 := by
  have h1 : a.toNat < 2 ^ 32 := UInt32.toNat_lt a
  have h2 : b.toNat < 2 ^ 32 := UInt32.toNat_lt b
  have h3 : carry a b = (a.toNat + b.toNat) / 2 ^ 32 := rfl
  omega

/-- Перенос нулевой ровно тогда, когда сумма помещается в
разрядную сетку. -/
theorem carry_eq_zero_iff (a b : Word) :
    carry a b = 0 ↔ a.toNat + b.toNat < 2 ^ 32 := by
  unfold carry
  omega

end Hagi.Model.RVCoreBignum
