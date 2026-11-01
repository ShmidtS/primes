import Hagi.Model.RVCore

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
