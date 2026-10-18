/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# HypothesisCompetition — Dynamic Hypothesis Competition (DHC) ядро

Модель динамической конкуренции гипотез (DHC, биоинспирированная):
система хранит `K` гипотез с активациями `a i`, превращает их
softmax-функцией (температура `T > 0`) в веса выбора `p i` и
обновляет активации разностным уравнением с взаимным подавлением:

* `dhcTotal a T = ∑ j, exp (a j / T)`;
* `dhcWeights a T i = exp (a i / T) / dhcTotal a T` — softmax-вес
  (representation ≠ active choice: веса положительны при любом
  `a`, сумма равна 1);
* `dhcStep a s C rho kappa T i` — один шаг
  `a' i = (1-ρ) a i + ρ s i - κ ∑ j, C i j * p j` — инерция `(1-ρ)`,
  поддержка оценками `ρ s`, взаимное подавление через матрицу
  несовместимости `C`.

Теоремы:

* `dhcTotal_pos` — знаменатель строго положителен при `0 < K`.
* `dhcWeights_pos` — веса строго положительны.
* `dhcWeights_sum_one` — `∑ i, dhcWeights a T i = 1`.
* `dhcWeights_le_one` — каждый вес ≤ 1.
* `dhcWeights_mono` — `a i ≤ a k → p i ≤ p k` (softmax монотонен).
* `dhcStep_suppressed` — при `0 ≤ κ`, `0 ≤ C` обновление не
  превышает инерционно-поддерживающую часть.
* `dhcStep_abs_bound` — равномерная оценка |a' i| (инвариант
  ограниченности орбиты при ограниченных оценках).

Модель гипотетико-дедуктивная: матрица `C` (несовместимость),
температура `T` и параметры `ρ, κ` — семантика предметной
области; связка с конкретным оценщиком `s` не формализуется.
-/

open Finset Real

namespace Hagi.Model

variable {K : ℕ}

/-- Сумма экспонент — знаменатель softmax. -/
noncomputable def dhcTotal (a : Fin K → ℝ) (T : ℝ) : ℝ :=
  ∑ j, Real.exp (a j / T)

/-- Знаменатель softmax строго положителен (при непустом наборе
гипотез `0 < K`). -/
theorem dhcTotal_pos (a : Fin K → ℝ) (T : ℝ) (hK : 0 < K) :
    0 < dhcTotal a T := by
  show (0:ℝ) < ∑ j, Real.exp (a j / T)
  have hn : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  obtain ⟨j0⟩ := hn
  have hge : Real.exp (a j0 / T) ≤ ∑ j, Real.exp (a j / T) :=
    Finset.single_le_sum (f := fun j => Real.exp (a j / T))
      (fun j _ => le_of_lt (exp_pos _)) (Finset.mem_univ j0)
  exact lt_of_lt_of_le (exp_pos _) hge

/-- Softmax-веса выбора: положительные, суммируются в 1
(representation ≠ active choice). -/
noncomputable def dhcWeights (a : Fin K → ℝ) (T : ℝ) : Fin K → ℝ :=
  fun i => Real.exp (a i / T) / dhcTotal a T

/-- Один шаг DHC-динамики: инерция `(1-ρ)a`, поддержка `ρ s`,
взаимное подавление `κ · C · p`. -/
noncomputable def dhcStep (a s : Fin K → ℝ) (C : Matrix (Fin K) (Fin K) ℝ)
    (rho kappa T : ℝ) : Fin K → ℝ :=
  fun i => (1 - rho) * a i + rho * s i
    - kappa * ∑ j, C i j * dhcWeights a T j

/-- Веса строго положительны при `T ≠ 0`, `0 < K`. -/
theorem dhcWeights_pos (a : Fin K → ℝ) {T : ℝ} (_hT : T ≠ 0) (hK : 0 < K)
    (i : Fin K) : 0 < dhcWeights a T i := by
  unfold dhcWeights
  exact div_pos (exp_pos _) (dhcTotal_pos a T hK)

/-- Нормировка: сумма весов равна 1. -/
theorem dhcWeights_sum_one (a : Fin K → ℝ) {T : ℝ} (_hT : T ≠ 0) (hK : 0 < K) :
    ∑ i, dhcWeights a T i = 1 := by
  show ∑ i, (Real.exp (a i / T) / dhcTotal a T) = 1
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (dhcTotal_pos a T hK))

/-- Каждый вес ≤ 1 (следствие нормировки и положительности). -/
theorem dhcWeights_le_one (a : Fin K → ℝ) {T : ℝ} (hT : T ≠ 0) (hK : 0 < K)
    (i : Fin K) : dhcWeights a T i ≤ 1 := by
  refine (dhcWeights_sum_one a hT hK) ▸ ?_
  exact Finset.single_le_sum (f := fun j => dhcWeights a T j)
    (fun j _ => le_of_lt (dhcWeights_pos a hT hK j)) (Finset.mem_univ i)

/-- Softmax монотонен по активации: `a i ≤ a k → p i ≤ p k`. -/
theorem dhcWeights_mono (a : Fin K → ℝ) {T : ℝ} (hT : 0 < T) (hK : 0 < K)
    {i k : Fin K} (h : a i ≤ a k) : dhcWeights a T i ≤ dhcWeights a T k := by
  show Real.exp (a i / T) / dhcTotal a T
      ≤ Real.exp (a k / T) / dhcTotal a T
  rw [div_le_div_iff_of_pos_right (dhcTotal_pos a T hK), exp_le_exp,
    div_le_div_iff_of_pos_right hT]
  exact h

/-- Подавление: при `0 ≤ κ`, `0 ≤ C`, `0 < K` шаг не превышает
инерционно-поддерживающую часть `(1-ρ)a + ρs`. -/
theorem dhcStep_suppressed (a s : Fin K → ℝ) (C : Matrix (Fin K) (Fin K) ℝ)
    {rho kappa T : ℝ} (hkap : 0 ≤ kappa) (hT : T ≠ 0) (hK : 0 < K)
    (hC : ∀ i j, 0 ≤ C i j) (i : Fin K) :
    dhcStep a s C rho kappa T i
      ≤ (1 - rho) * a i + rho * s i := by
  unfold dhcStep
  refine sub_le_self _ (mul_nonneg hkap ?_)
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hC i j) (le_of_lt (dhcWeights_pos a hT hK j)))

/-- Равномерная оценка шага: |a' i| ≤ (1−ρ)|a i| + ρ|s i| +
κ ∑ |C i j| (при 0 ≤ ρ ≤ 1, 0 ≤ κ, T ≠ 0, 0 < K, 0 ≤ C) — инвариант
ограниченности орбиты активаций при ограниченных оценках. -/
theorem dhcStep_abs_bound (a s : Fin K → ℝ) (C : Matrix (Fin K) (Fin K) ℝ)
    {rho kappa T : ℝ} (hrho1 : 0 ≤ rho) (hrho2 : rho ≤ 1) (hkap : 0 ≤ kappa)
    (hT : T ≠ 0) (hK : 0 < K) (hC : ∀ i j, 0 ≤ C i j) (i : Fin K) :
    |dhcStep a s C rho kappa T i| ≤ (1 - rho) * |a i| + rho * |s i|
      + kappa * ∑ j, |C i j| := by
  have hp0 : ∀ j, 0 ≤ dhcWeights a T j := fun j =>
    le_of_lt (dhcWeights_pos a hT hK j)
  have hp1 : ∀ j, dhcWeights a T j ≤ 1 := fun j => dhcWeights_le_one a hT hK j
  have hy0 : 0 ≤ kappa * ∑ j, C i j * dhcWeights a T j :=
    mul_nonneg hkap (Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hC i j) (hp0 j)))
  have hsup : |kappa * ∑ j, C i j * dhcWeights a T j|
      ≤ kappa * ∑ j, |C i j| := by
    rw [abs_mul, abs_of_nonneg hkap]
    refine mul_le_mul_of_nonneg_left ?_ hkap
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hp0 j)]
    refine le_trans (mul_le_mul_of_nonneg_left (hp1 j)
      (abs_nonneg _)) ?_
    rw [mul_one]
  have hpart : |(1 - rho) * a i + rho * s i|
      ≤ (1 - rho) * |a i| + rho * |s i| := by
    have htri2 : |(1 - rho) * a i + rho * s i|
        ≤ |(1 - rho) * a i| + |rho * s i| := by
      rw [abs_le]
      constructor <;> linarith [abs_nonneg ((1 - rho) * a i),
        abs_nonneg (rho * s i), le_abs_self ((1 - rho) * a i),
        (by
          have h := le_abs_self (-((1 - rho) * a i))
          rwa [abs_neg] at h),
        le_abs_self (rho * s i),
        (by
          have h := le_abs_self (-(rho * s i))
          rwa [abs_neg] at h)]
    have h1 : |(1 - rho) * a i| ≤ (1 - rho) * |a i| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - rho)]
    have h2 : |rho * s i| ≤ rho * |s i| := by
      rw [abs_mul, abs_of_nonneg hrho1]
    linarith
  have htri : |((1 - rho) * a i + rho * s i)
      - kappa * ∑ j, C i j * dhcWeights a T j|
      ≤ |(1 - rho) * a i + rho * s i|
        + |kappa * ∑ j, C i j * dhcWeights a T j| := by
    rw [abs_le]
    constructor <;> linarith [abs_nonneg ((1 - rho) * a i + rho * s i),
      abs_nonneg (kappa * ∑ j, C i j * dhcWeights a T j),
      le_abs_self ((1 - rho) * a i + rho * s i),
      (by
        have h := le_abs_self (-((1 - rho) * a i + rho * s i))
        rwa [abs_neg] at h),
      le_abs_self (kappa * ∑ j, C i j * dhcWeights a T j),
      (by
        have h := le_abs_self (-(kappa * ∑ j, C i j * dhcWeights a T j))
        rwa [abs_neg] at h)]
  unfold dhcStep
  exact le_trans htri (by linarith)

end Hagi.Model
