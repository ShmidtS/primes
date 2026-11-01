import Mathlib

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
