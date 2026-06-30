import Mathlib
import Primes.Basic
import Primes.GapFrequency

namespace PrimeGaps

/-! ## Operator: prime summatory operator and eigenpairs -/

noncomputable section

/-- Арифметическая функция на натуральных числах. -/
abbrev ArithmeticFunction := Nat → ℝ

/-- Оператор суммирования по простым: `(Af)(n) = Σ_{p≤n} f(p)`. -/
def primeSummatoryOperator (f : ArithmeticFunction) (n : Nat) : ℝ :=
  (Finset.range (n + 1)).sum fun p => if Nat.Prime p then f p else 0

/-- Собственная пара для оператора суммирования по простым. -/
def IsPrimeSummatoryEigenpair (f : ArithmeticFunction) (eigenvalue : ℝ) : Prop :=
  f ≠ 0 ∧ ∀ n : Nat, primeSummatoryOperator f n = eigenvalue * f n

/-- Локальная рекурсия оператора: при переходе от `n` к `n+1` добавляется только `n+1`. -/
theorem primeSummatoryOperator_succ (f : ArithmeticFunction) (n : Nat) :
    primeSummatoryOperator f (n + 1) =
      primeSummatoryOperator f n + if Nat.Prime (n + 1) then f (n + 1) else 0 := by
  change (Finset.range ((n + 1) + 1)).sum (fun p => if Nat.Prime p then f p else 0) =
    (Finset.range (n + 1)).sum (fun p => if Nat.Prime p then f p else 0) +
      (if Nat.Prime (n + 1) then f (n + 1) else 0)
  rw [Finset.sum_range_succ]

/-- Любая собственная пара удовлетворяет локальной рекурсии оператора. -/
theorem primeSummatoryEigenpair_recurrence {f : ArithmeticFunction} {eigenvalue : ℝ}
    (h : IsPrimeSummatoryEigenpair f eigenvalue) (n : Nat) :
    eigenvalue * f (n + 1) =
      eigenvalue * f n + if Nat.Prime (n + 1) then f (n + 1) else 0 := by
  rw [← h.2 (n + 1), ← h.2 n]
  exact primeSummatoryOperator_succ f n

/-! ### Linearity properties -/

/-- Оператор на нулевой функции равен нулю. -/
theorem primeSummatoryOperator_zero (n : Nat) :
    primeSummatoryOperator 0 n = 0 := by
  unfold primeSummatoryOperator
  simp

/-- Оператор линеен: `(A(f + g))(n) = (Af)(n) + (Ag)(n)`. -/
theorem primeSummatoryOperator_add (f g : ArithmeticFunction) (n : Nat) :
    primeSummatoryOperator (f + g) n =
      primeSummatoryOperator f n + primeSummatoryOperator g n := by
  unfold primeSummatoryOperator
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1; ext p; split_ifs <;> ring

/-- Оператор однороден: `(A(c • f))(n) = c * (Af)(n)`. -/
theorem primeSummatoryOperator_smul (c : ℝ) (f : ArithmeticFunction) (n : Nat) :
    primeSummatoryOperator (c • f) n = c * primeSummatoryOperator f n := by
  unfold primeSummatoryOperator
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_comm c, Finset.sum_mul]
  congr 1; ext p; split_ifs <;> ring

/-- Оператор монотонен по функции: `f ≤ g → Af ≤ Ag`. -/
theorem primeSummatoryOperator_monotone {f g : ArithmeticFunction}
    (hfg : ∀ n, f n ≤ g n) (n : Nat) :
    primeSummatoryOperator f n ≤ primeSummatoryOperator g n := by
  unfold primeSummatoryOperator
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : Nat.Prime p
  · simp only [hp, if_true]
    exact hfg p
  · simp only [hp, if_false]
    exact le_refl _

/-- Оператор неотрицателен на неотрицательных функциях. -/
theorem primeSummatoryOperator_nonneg {f : ArithmeticFunction}
    (hf : ∀ n, 0 ≤ f n) (n : Nat) :
    0 ≤ primeSummatoryOperator f n := by
  unfold primeSummatoryOperator
  apply Finset.sum_nonneg
  intro p _
  by_cases hp : Nat.Prime p
  · simp only [hp, if_true]
    exact hf p
  · simp only [hp, if_false]
    exact le_refl _

/-- Оператор на `n = 0` всегда равен нулю (0 не простое). -/
theorem primeSummatoryOperator_zero_arg (f : ArithmeticFunction) :
    primeSummatoryOperator f 0 = 0 := by
  unfold primeSummatoryOperator
  simp [Finset.range, Nat.not_prime_zero]

end

end PrimeGaps
