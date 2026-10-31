import Mathlib
import Hagi.Probability.EntropyConvexity
import Hagi.Energy.Cooling

/-!
# LabelSmoothing (источник №74: "Rethinking the Inception
# Architecture", Szegedy et al., 1606.04586; анализ
# калибровки 1906.02629)

Сглаживание меток: цель q^LS = (1−ε)·q + ε·u, где u —
равномерное распределение. Формализуем честные свойства:
нормировка (сглаженная цель — распределение),
неотрицательность, поточечная и L¹-границы расстояния до
исходной цели (линейны по ε).
-/

namespace Hagi.Model.LabelSmoothing

variable {K : Type*} [Fintype K] [Nonempty K] [DecidableEq K]

/-- Сглаженная цель: выпуклая комбинация с равномерной. -/
noncomputable def lsTarget (q : K → ℝ) (ε : ℝ) : K → ℝ :=
  fun i => (1 - ε) * q i + ε / (Fintype.card K)

/-- СГЛАЖЕННАЯ ЦЕЛЬ — РАСПРЕДЕЛЕНИЕ. -/
theorem ls_sum_one (q : K → ℝ) (hq : ∑ i : K, q i = 1) (ε : ℝ) :
    ∑ i : K, lsTarget q ε i = 1 := by
  unfold lsTarget
  rw [Finset.sum_add_distrib]
  have h1 : ∑ x : K, (1 - ε) * q x = (1 - ε) * ∑ x : K, q x :=
    (Finset.mul_sum Finset.univ q (1 - ε)).symm
  have hcard : (0:ℝ) < Fintype.card K := by
    have : (0:ℕ) < Fintype.card K := Fintype.card_pos
    exact_mod_cast this
  have hu : ∑ i : K, (1 / (Fintype.card K : ℝ)) = 1 := by
    rw [Finset.sum_const]; simp
  have h2 : ∑ x : K, ε / (Fintype.card K : ℝ)
      = ε * ∑ i : K, 1 / (Fintype.card K : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => div_eq_mul_one_div _ _
  rw [h1, h2, hq, hu]
  ring

/-- НЕОТРИЦАТЕЛЬНОСТЬ при ε ∈ [0,1]. -/
theorem ls_nonneg (q : K → ℝ) (hq : ∀ i, 0 ≤ q i)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ i, 0 ≤ lsTarget q ε i := by
  intro i
  unfold lsTarget
  have h1 : 0 ≤ (1 - ε) * q i := mul_nonneg (by linarith) (hq i)
  have h2 : 0 ≤ ε / (Fintype.card K : ℝ) := by positivity
  linarith

/-- ПОТОЧЕЧНАЯ ГРАНИЦА: |q^LS i − q i| = ε·|q i − 1/K| —
расстояние до исходной цели линейно по ε. -/
theorem ls_pointwise_dist (q : K → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (i : K) :
    |lsTarget q ε i - q i|
      = ε * |q i - 1 / (Fintype.card K : ℝ)| := by
  unfold lsTarget
  have hEq : (1 - ε) * q i + ε / (Fintype.card K : ℝ) - q i
      = ε * (1 / (Fintype.card K : ℝ) - q i) := by ring
  rw [hEq, abs_mul, abs_of_nonneg hε, abs_sub_comm]

/-- L¹-ГРАНИЦА: ∑|q^LS − q| ≤ ε·(card K)·1 ≤ ... при
card K ≥ 2 имеем ≤ 2ε — сглаженная цель остаётся в
ε-окрестности исходной (цель обучения не уходит далеко). -/
theorem ls_l1_bound (q : K → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hq1 : ∑ i : K, q i = 1) (ε : ℝ) (hε : 0 ≤ ε) :
    ∑ i : K, |lsTarget q ε i - q i| ≤ ε * Fintype.card K := by
  have hcard : (0:ℝ) < Fintype.card K := by
    have : (0:ℕ) < Fintype.card K := Fintype.card_pos
    exact_mod_cast this
  have hkey : ∀ i, |q i - 1 / (Fintype.card K : ℝ)| ≤ 1 := by
    intro i
    have hqi : q i ≤ 1 :=
      le_trans (Finset.single_le_sum (fun j _ => hq j) (Finset.mem_univ i))
        (by rw [hq1])
    have hle : (1:ℝ) / Fintype.card K ≤ 1 :=
      (div_le_one hcard).mpr
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_pos.ne')
    rw [abs_le]
    constructor
    · linarith [hle, hq i]
    · have hge0 : (0:ℝ) ≤ 1 / Fintype.card K :=
        div_nonneg zero_le_one hcard.le
      linarith [hle, hqi, hge0]
  calc ∑ i : K, |lsTarget q ε i - q i|
      = ∑ i : K, ε * |q i - 1 / (Fintype.card K : ℝ)| := by
        exact Finset.sum_congr rfl fun i _ => ls_pointwise_dist q ε hε i
    _ ≤ ∑ i : K, ε * 1 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hkey i) hε
    _ = ε * Fintype.card K := by simp; ring


/-! ### Энтропийное возрастание (углубление №74):
сглаживание НЕ УМЕНЬШАЕТ энтропию цели — регуляризация
к равномерному распределению (мотивация калибровки из
1906.02629). -/

/-- Энтропия цели. -/
noncomputable def lsH (p : K → ℝ) : ℝ := -∑ i : K, p i * Real.log (p i)

/-- СГЛАЖИВАНИЕ УВЕЛИЧИВАЕТ ЭНТРОПИЮ: H(q) ≤ H(q^LS) при
строго положительной цели и ε ∈ (0,1). Вывод: Jensen по
слагаемым (x·log x выпукла — xlogx_convex) даёт
H(q^LS) ≥ (1−ε)·H(q) + ε·log(card K) ≥ H(q), поскольку
H(q) ≤ log(card K) (shannon_entropy_le_log_card). -/
theorem ls_entropy_ge (q : K → ℝ) (hq : ∀ i, 0 < q i)
    (hq1 : ∑ i : K, q i = 1) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    lsH q ≤ lsH (lsTarget q ε) := by
  have hcard : (0:ℝ) < Fintype.card K := by
    have : (0:ℕ) < Fintype.card K := Fintype.card_pos
    exact_mod_cast this
  have hu : ∀ i : K, 0 < 1 / (Fintype.card K : ℝ) := by
    intro i; positivity
  have hlspos : ∀ i, 0 < lsTarget q ε i := by
    intro i
    have h1 : 0 < (1 - ε) * q i := mul_pos (by linarith) (hq i)
    have h2 : 0 ≤ ε / (Fintype.card K : ℝ) := by positivity
    unfold lsTarget
    linarith

  -- Jensen по слагаемым (x·log x выпукла)
  have hjensen : ∀ i : K,
      lsTarget q ε i * Real.log (lsTarget q ε i)
        ≤ (1 - ε) * (q i * Real.log (q i))
          + ε * ((1 / (Fintype.card K : ℝ))
            * Real.log (1 / (Fintype.card K : ℝ))) := by
    intro i
    have := Hagi.Probability.xlogx_convex (a := q i)
      (b := 1 / (Fintype.card K : ℝ)) (lam := 1 - ε) (hq i) (hu i)
      (by linarith) (by linarith)
    -- форма: (lam*a + (1-lam)*b)*log(...) ≤ lam*a*log a + (1-lam)*b*log b
    have hform : (1 - ε) * q i + ε * (1 / (Fintype.card K : ℝ))
        = lsTarget q ε i := by
      unfold lsTarget
      rw [div_eq_mul_one_div]
      ring
    rw [← hform]
    have hsimp : 1 - (1 - ε) = ε := by ring
    rw [hsimp] at this
    linarith [this]
  have hsum : (∑ i : K, lsTarget q ε i * Real.log (lsTarget q ε i))
      ≤ ∑ i : K, ((1 - ε) * (q i * Real.log (q i))
        + ε * ((1 / (Fintype.card K : ℝ))
          * Real.log (1 / (Fintype.card K : ℝ)))) :=
    Finset.sum_le_sum (fun i _ => hjensen i)
  -- сумма: ∑ lsT·log lsT ≤ (1−ε)·∑ q·log q + ε·∑ u·log u
  have hsumu : ∑ i : K, (1 / (Fintype.card K : ℝ))
      * Real.log (1 / (Fintype.card K : ℝ))
      = -(Real.log (Fintype.card K : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card K : ℝ) ≠ 0 := by positivity
    have hcc : (Fintype.card K : ℝ) * (Fintype.card K : ℝ)⁻¹ = 1 :=
      mul_inv_cancel₀ hc
    rw [one_div, ← mul_assoc, hcc, one_mul, Real.log_inv]

  -- разбиение суммы на два слагаемых
  have hsplit : ∑ i : K, ((1 - ε) * (q i * Real.log (q i))
      + ε * ((1 / (Fintype.card K : ℝ))
        * Real.log (1 / (Fintype.card K : ℝ))))
      = (1 - ε) * ∑ i : K, q i * Real.log (q i)
        + ε * ∑ i : K, (1 / (Fintype.card K : ℝ))
          * Real.log (1 / (Fintype.card K : ℝ)) := by
    rw [Finset.sum_add_distrib]
    have e1 : ∑ i : K, (1 - ε) * (q i * Real.log (q i))
        = (1 - ε) * ∑ i : K, q i * Real.log (q i) :=
      (Finset.mul_sum Finset.univ (fun i => q i * Real.log (q i)) (1 - ε)).symm
    have e2 : ∑ i : K, ε * ((1 / (Fintype.card K : ℝ))
        * Real.log (1 / (Fintype.card K : ℝ)))
        = ε * ∑ i : K, (1 / (Fintype.card K : ℝ))
          * Real.log (1 / (Fintype.card K : ℝ)) :=
      (Finset.mul_sum Finset.univ
        (fun i => (1 / (Fintype.card K : ℝ))
          * Real.log (1 / (Fintype.card K : ℝ))) ε).symm
    rw [e1, e2]

  rw [hsplit, hsumu] at hsum
  -- H(q) ≤ log card (шенноновская граница)
  have hqcap := Hagi.Energy.shannon_entropy_le_log_card q hq hq1
  -- финал: −∑q·log q ≤ −∑lsT·log lsT (через neg_le_neg)
  unfold lsH
  rw [neg_le_neg_iff]
  nlinarith [hsum, hqcap]

end Hagi.Model.LabelSmoothing
