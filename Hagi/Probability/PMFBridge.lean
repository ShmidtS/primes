/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib

set_option linter.style.header false

/-!
# Мост вероятностных языков: V → ℝ ↔ PMF (этап 4 рецензии)

Рецензия (§2.3): библиотека говорит на четырёх несвязанных
вероятностных языках. Этот модуль — первый мост: самодельный
закон `q : V → ℝ` (конечный, ∑ q = 1) отождествляется с
Mathlib-типом `PMF V` точно и в обе стороны.

* `toPMF` — вложение (масса сохраняется);
* `fromPMF` — проекция (`.toReal`);
* `fromPMF_sum` — масса сохраняется при проекции;
* `toPMF_fromPMF` — round-trip: PMF восстанавливается точно
  (конечный носитель ⟹ каждый вес ≤ 1 < ∞);
* `fromPMF_toPMF` — обратный round-trip на функциях.

Мост KL (наш `klDef` ↔ Mathlib `klDiv` на мерах) остаётся
открытым: `klDiv` определён через rnDeriv-интегралы,
поточечной дискретной формы в Mathlib нет.
-/

open ENNReal Finset

namespace Hagi.Probability

variable {V ι : Type} [Fintype V] [Nonempty V]

/-- Сумма `ofReal` равна `ofReal` суммы для неотрицательных
слагаемых (в этой версии Mathlib готовой леммы нет). -/
private theorem ofReal_finset_sum (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, ENNReal.ofReal (f i)
      = ENNReal.ofReal (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hnn_s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hnn_a : 0 ≤ f a := h a (Finset.mem_insert_self a s)
      have hnn_sum : 0 ≤ ∑ i ∈ s, f i :=
        Finset.sum_nonneg hnn_s
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ih hnn_s, ENNReal.ofReal_add hnn_a hnn_sum]

/-- В конечном пространстве каждый вес PMF не превосходит
общей массы 1. -/
private theorem pmfWeight_le_one (p : PMF V) (v : V) : p v ≤ 1 := by
  have hsum : ∑ w, p w = 1 := by
    have h := PMF.tsum_coe p
    rwa [tsum_fintype] at h
  have hsingle : p v ≤ ∑ w ∈ Finset.univ, p w :=
    Finset.single_le_sum (fun w _ => by positivity) (Finset.mem_univ v)
  rwa [hsum] at hsingle

/-- Самодельный закон q (конечный) как PMF: масса сохраняется
точным равенством сумм. -/
def toPMF (q : V → ℝ) (hnn : ∀ v, 0 ≤ q v)
    (hs : ∑ v, q v = 1) : PMF V :=
  ⟨fun v => ENNReal.ofReal (q v), by
    have h1 : HasSum (fun v => ENNReal.ofReal (q v))
        (∑ v, ENNReal.ofReal (q v)) := hasSum_fintype _
    have h2 : ∑ v, ENNReal.ofReal (q v)
        = ENNReal.ofReal (∑ v, q v) :=
      ofReal_finset_sum Finset.univ q (fun v _ => hnn v)
    have h3 : ENNReal.ofReal (∑ v, q v) = 1 := by rw [hs]; simp
    rw [h2, h3] at h1
    exact h1⟩

theorem toPMF_apply (q : V → ℝ) (hnn : ∀ v, 0 ≤ q v)
    (hs : ∑ v, q v = 1) (v : V) :
    toPMF q hnn hs v = ENNReal.ofReal (q v) := rfl

/-- PMF как самодельный закон: вещественные веса. -/
def fromPMF (p : PMF V) : V → ℝ := fun v => (p v).toReal

/-- Масса PMF сохраняется при проекции в самодельный закон. -/
theorem fromPMF_sum (p : PMF V) : ∑ v, (p v).toReal = 1 := by
  have hsum : ∑ v, p v = 1 := by
    have h := PMF.tsum_coe p
    rwa [tsum_fintype] at h
  have hne : ∀ v ∈ Finset.univ, p v ≠ ⊤ := by
    intro v _
    exact ne_of_lt
      (lt_of_le_of_lt (pmfWeight_le_one p v) ENNReal.one_lt_top)
  rw [← ENNReal.toReal_sum hne, hsum]
  simp

/-- Round-trip PMF → функция → PMF — тождество (конечный
носитель: каждый вес ≤ 1 < ∞, поэтому .toReal не теряет
массу). -/
theorem toPMF_fromPMF (p : PMF V) :
    toPMF (fromPMF p) (fun v => ENNReal.toReal_nonneg)
      (fromPMF_sum p) = p := by
  apply Subtype.ext
  funext v
  have hv : p v ≠ ⊤ :=
    ne_of_lt
      (lt_of_le_of_lt (pmfWeight_le_one p v) ENNReal.one_lt_top)
  exact ENNReal.ofReal_toReal hv

/-- Round-trip функция → PMF → функция — тождество на
неотрицательных законах. -/
theorem fromPMF_toPMF (q : V → ℝ) (hnn : ∀ v, 0 ≤ q v)
    (hs : ∑ v, q v = 1) :
    fromPMF (toPMF q hnn hs) = q := by
  funext v
  exact ENNReal.toReal_ofReal (hnn v)

end Hagi.Probability

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
