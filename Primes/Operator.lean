import Mathlib
import Primes.Basic
import Primes.GapFrequency

set_option linter.style.header false
set_option linter.style.longLine false

namespace PrimeGaps

noncomputable section

/-- Арифметическая функция на натуральных числах. -/
abbrev ArithmeticFunction := Nat → ℝ

/-- Оператор суммирования по простым: `(Af)(n) = Σ_{p≤n} f(p)`. -/
def primeSummatoryOperator (f : ArithmeticFunction) (n : Nat) : ℝ :=
  (Finset.range (n + 1)).sum fun p => if Nat.Prime p then f p else 0

/-- Собственная пара для оператора суммирования по простым. -/
def IsPrimeSummatoryEigenpair (f : ArithmeticFunction) (eigenvalue : ℝ) : Prop :=
  f ≠ 0 ∧ ∀ n : Nat, primeSummatoryOperator f n = eigenvalue * f n

/-- Любая собственная пара удовлетворяет локальной рекурсии:
при переходе от `n` к `n+1` добавляется только вклад `n+1`. -/
theorem primeSummatoryEigenpair_recurrence {f : ArithmeticFunction} {eigenvalue : ℝ}
    (h : IsPrimeSummatoryEigenpair f eigenvalue) (n : Nat) :
    eigenvalue * f (n + 1) =
      eigenvalue * f n + if Nat.Prime (n + 1) then f (n + 1) else 0 := by
  rw [← h.2 (n + 1), ← h.2 n]; unfold primeSummatoryOperator
  rw [show (n + 1) + 1 = n + 2 by omega, Finset.sum_range_succ]

end
end PrimeGaps
