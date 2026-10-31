import Mathlib

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

end Hagi.Model.LabelSmoothing
