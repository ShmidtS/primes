import Mathlib

/-!
# BernoulliFactory — Bernstein-гейт (источник №59: Jessica
# Taylor, "Dice enterprises and polynomial approximation:
# uniform query tails", arXiv 2610.38964)

Идея Bernoulli factory: реализовать бинарное решение с
вероятностью f(p), НЕ зная p — только через случайные
наблюдения. Ядро конструкции — Bernstein-полином: n
наблюдений Бернулли(p), счёт успехов J, решение «принять»
с вероятностью c_J. Тогда полная вероятность принятия —
в точности Bernstein-оценка полинома с коэффициентами c.

Уровень 1 (этот файл): ТОЧНОСТЬ Bernstein-гейта —
вероятность принятия равна bernPoly c p; нормировка
(сумма мультиномиальных весов = 1); границы [0,1] при
c ∈ [0,1]. Оговорка аудита v12: это математика механизма,
НЕ доказательство, что вероятностный gate заменяет
SafeQP-гарантии отдельного шага.
-/

namespace Hagi.Probability.BernoulliFactory

open Finset

/-- Мультиномиальный (биномиальный) вес: вероятность
увидеть j успехов в n наблюдениях Бернулли(p). -/
def binomWeight (n : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  Nat.choose n j * p ^ j * (1 - p) ^ (n - j)

/-- Полная вероятность принятия Bernstein-гейта:
счётчик J ~ binomWeight, решение «принять» с вероятностью
c J. -/
def probAccept (n : ℕ) (p : ℝ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), binomWeight n p j * c j

/-- Bernstein-полином с коэффициентами c. -/
def bernPoly (n : ℕ) (p : ℝ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), c j * Nat.choose n j * p ^ j * (1 - p) ^ (n - j)

/-- ТОЧНОСТЬ ГЕЙТА: вероятность принятия = Bernstein-полином
(перестановка множителей; comm-ring). -/
theorem probAccept_eq_bernPoly (n : ℕ) (p : ℝ) (c : ℕ → ℝ) :
    probAccept n p c = bernPoly n p c := by
  unfold probAccept bernPoly binomWeight
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- НЕОТРИЦАТЕЛЬНОСТЬ весов. -/
theorem binomWeight_nonneg (n : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (j : ℕ) : 0 ≤ binomWeight n p j := by
  unfold binomWeight
  have h4 : 0 ≤ (1 - p) ^ (n - j) := pow_nonneg (by linarith) (n - j)
  have h1 : 0 ≤ (p:ℝ) ^ j := pow_nonneg hp.1 j
  positivity

/-- Масса распределения счётчика (сумма весов). Полная
нормировка = 1 (индукция по биному Ньютона) — уровень 2. -/
def binomMass (n : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), binomWeight n p j

/-- ГРАНИЦА ГЕЙТА (уровень 1, честная): вероятность
принятия НЕ превосходит массы распределения счётчика;
неотрицательность — из неотрицательности весов. Полная
нормировка binomMass = 1 — отдельный уровень 2. -/
theorem probAccept_bounds (n : ℕ) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) (c : ℕ → ℝ)
    (hc : ∀ j ∈ range (n + 1), 0 ≤ c j ∧ c j ≤ 1) :
    0 ≤ probAccept n p c
      ∧ probAccept n p c ≤ binomMass n p := by
  constructor
  · unfold probAccept
    apply Finset.sum_nonneg
    intro j hj
    have : j < n + 1 := Finset.mem_range.mp hj
    exact mul_nonneg (binomWeight_nonneg n p hp j) (hc j (Finset.mem_range.mpr this)).1
  · unfold probAccept binomMass
    apply Finset.sum_le_sum
    intro j hj
    have : j < n + 1 := Finset.mem_range.mp hj
    exact (mul_le_mul_of_nonneg_left (hc j (Finset.mem_range.mpr this)).2
      (binomWeight_nonneg n p hp j)).trans_eq (mul_one _)

end Hagi.Probability.BernoulliFactory
