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

/-- Собственная пара с собственным значением 0: `f` обращается в нуль на всех простых. -/
theorem primeSummatoryEigenpair_zero_eigenvalue
    {f : ArithmeticFunction} (h : IsPrimeSummatoryEigenpair f 0) :
    ∀ p : Nat, Nat.Prime p → f p = 0 := by
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  have hrec := primeSummatoryEigenpair_recurrence h (p - 1)
  rw [show (p - 1) + 1 = p by omega] at hrec
  simp only [zero_mul, if_pos hp, zero_add] at hrec
  exact hrec.symm

/-- При ненулевом собственном значении `f` постоянна между простыми. -/
theorem primeSummatoryEigenpair_const_between_primes
    {f : ArithmeticFunction} {ev : ℝ} (h : IsPrimeSummatoryEigenpair f ev)
    (hev : ev ≠ 0) (n : Nat) (hn : ¬Nat.Prime (n + 1)) :
    f (n + 1) = f n := by
  have hrec := primeSummatoryEigenpair_recurrence h n
  rw [if_neg hn, add_zero] at hrec
  exact mul_left_cancel₀ hev hrec

/-- При простом `n+1` скачок: `(ev - 1) · f(n+1) = ev · f(n)`. -/
theorem primeSummatoryEigenpair_jump_at_prime
    {f : ArithmeticFunction} {ev : ℝ} (h : IsPrimeSummatoryEigenpair f ev)
    (n : Nat) (hn : Nat.Prime (n + 1)) :
    (ev - 1) * f (n + 1) = ev * f n := by
  have hrec := primeSummatoryEigenpair_recurrence h n
  rw [if_pos hn] at hrec
  linear_combination hrec

end
end PrimeGaps
