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

/-- **DHC-орбита**: рекурсивная траектория активаций
с обновлением на каждом шаге (оценки `s` постоянны — это
закрытая модель; пересчёт оценок после новых свидетельств —
уровень окружения). -/
noncomputable def dhcOrbit (s : Fin K → ℝ) (C : Matrix (Fin K) (Fin K) ℝ)
    (rho kappa T : ℝ) (a0 : Fin K → ℝ) : ℕ → Fin K → ℝ
  | 0 => a0
  | t + 1 => dhcStep (dhcOrbit s C rho kappa T a0 t) s C rho kappa T

/-- Шаг орбиты — обновление предыдущей точки. -/
theorem dhcOrbit_succ (s : Fin K → ℝ) (C : Matrix (Fin K) (Fin K) ℝ)
    (rho kappa T : ℝ) (a0 : Fin K → ℝ) (t : ℕ) :
    dhcOrbit s C rho kappa T a0 (t + 1)
      = dhcStep (dhcOrbit s C rho kappa T a0 t) s C rho kappa T := rfl

/-- Ограниченность орбиты по индукции: при 0 ≤ ρ ≤ 1, 0 ≤ κ, 0 ≤ C
  — |a_t i| ≤ |a0 i| + t·(ρ|s i| + κ∑|C i j|): прирост на шаг не
  превосходит константы поддержки + подавления; линейная оболочка
  инварианта dhcStep_abs_bound. -/
theorem dhcOrbit_bound (s : Fin K → ℝ) (C : Matrix (Fin K) (Fin K) ℝ)
    {rho kappa T : ℝ} (hrho1 : 0 ≤ rho) (hrho2 : rho ≤ 1) (hkap : 0 ≤ kappa)
    (hT : T ≠ 0) (hK : 0 < K) (hC : ∀ i j, 0 ≤ C i j)
    (a0 : Fin K → ℝ) (i : Fin K) (t : ℕ) :
    |dhcOrbit s C rho kappa T a0 t i|
      ≤ |a0 i| + (t : ℝ) * (rho * |s i| + kappa * ∑ j, |C i j|) := by
  induction t with
  | zero => simpa [dhcOrbit] using abs_nonneg a0 i
  | succ n ih =>
    have hstep := dhcStep_abs_bound (dhcOrbit s C rho kappa T a0 n) s C
      hrho1 hrho2 hkap hT hK hC i
    have h1 : (1 - rho) * |dhcOrbit s C rho kappa T a0 n i|
        ≤ (1 - rho) * (|a0 i| + (n : ℝ) * (rho * |s i|
          + kappa * ∑ j, |C i j|)) :=
      mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ 1 - rho)
    rw [dhcOrbit_succ]
    refine le_trans hstep ?_
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
      push_cast
      ring
    have hG : (0:ℝ) ≤ rho * |s i| + kappa * ∑ j, |C i j| := by
      have ha : (0:ℝ) ≤ rho * |s i| := mul_nonneg hrho1 (abs_nonneg _)
      have hb : (0:ℝ) ≤ kappa * ∑ j, |C i j| :=
        mul_nonneg hkap (Finset.sum_nonneg fun j _ => abs_nonneg _)
      linarith
    rw [hcast, add_mul, one_mul]
    have h1' : (1 - rho) * (|a0 i| + (n:ℝ) * (rho * |s i|
        + kappa * ∑ j, |C i j|))
        = (1 - rho) * |a0 i| + (1 - rho) * ((n:ℝ)
          * (rho * |s i| + kappa * ∑ j, |C i j|)) := by ring
    have h3 : (1 - rho) * |a0 i| ≤ |a0 i| := by
      have hEq : (1 - rho) * |a0 i| = |a0 i| - rho * |a0 i| := by ring
      rw [hEq]
      exact sub_le_self _ (mul_nonneg hrho1 (abs_nonneg _))
    have h4 : (1 - rho) * ((n:ℝ) * (rho * |s i| + kappa * ∑ j, |C i j|))
        ≤ (n:ℝ) * (rho * |s i| + kappa * ∑ j, |C i j|) := by
      have hc : (0:ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      have hEq : (1 - rho) * ((n : ℝ) * (rho * |s i|
            + kappa * ∑ j, |C i j|))
          = (n : ℝ) * (rho * |s i| + kappa * ∑ j, |C i j|)
            - rho * ((n : ℝ) * (rho * |s i| + kappa * ∑ j, |C i j|)) := by
        ring
      rw [hEq]
      exact sub_le_self _ (mul_nonneg hrho1 (mul_nonneg hc hG))
    linarith [ih, h1, h1', h3, h4]

/-- Критерий завершения, часть 1: вес лидера (гипотезы
с максимальной активацией) не меньше 1/K — основа
порога уверенности τ в критерии p₁ ≥ τ ∧ p₁-p₂ ≥ Δ. -/
theorem dhcWeights_leader_ge_invK (a : Fin K → ℝ) {T : ℝ} (hT : 0 < T)
    (hK : 0 < K) {i : Fin K} (hmax : ∀ j, a j ≤ a i) :
    (1 / (K : ℝ)) ≤ dhcWeights a T i := by
  have hsum := dhcWeights_sum_one a (ne_of_gt hT) hK
  have hmono : ∀ j, dhcWeights a T j ≤ dhcWeights a T i := fun j =>
    dhcWeights_mono a hT hK (hmax j)
  have hcomm : (K : ℝ) * dhcWeights a T i
      = dhcWeights a T i * (K : ℝ) := mul_comm _ _
  have hle : ∑ j, dhcWeights a T j ≤ dhcWeights a T i * (K : ℝ) := by
    refine le_trans (Finset.sum_le_sum (fun j _ => hmono j)) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      hcomm]
  rw [div_le_iff₀ (by exact_mod_cast hK : (0:ℝ) < K)]
  linarith [hsum, hle]

/-- Критерий завершения, часть 2: нормировка весов выбора
вдоль всей орбиты — на каждом шаге веса образуют
распределение (сумма = 1), поэтому критерий
p₁ ≥ τ ∧ p₁ - p₂ ≥ Δ корректен на любом шаге траектории. -/
theorem dhcOrbit_weights_sum_one (s : Fin K → ℝ)
    (C : Matrix (Fin K) (Fin K) ℝ) (rho kappa T : ℝ) (hT : T ≠ 0)
    (hK : 0 < K) (a0 : Fin K → ℝ) (t : ℕ) :
    ∑ i, dhcWeights (dhcOrbit s C rho kappa T a0 t) T i = 1 :=
  dhcWeights_sum_one _ hT hK

/-- Критерий завершения, часть 3: если вес гипотезы
строго больше 1/2, она — единственный лидер: любая
другая гипотеза весит меньше (следствие нормировки;
замыкает критерий p₁ ≥ τ ∧ p₁ - p₂ ≥ Δ при τ > 1/2). -/
theorem dhcWeights_unique_leader (a : Fin K → ℝ) {T : ℝ} (hT : T ≠ 0)
    (hK : 0 < K) {i : Fin K} (hlead : 1 / 2 < dhcWeights a T i)
    (j : Fin K) (hij : j ≠ i) :
    dhcWeights a T j < dhcWeights a T i := by
  have hsum := dhcWeights_sum_one a hT hK
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun k => dhcWeights a T k) (Finset.mem_univ i)
  have hmem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩
  have hlej : dhcWeights a T j
      ≤ ∑ k ∈ Finset.univ.erase i, dhcWeights a T k :=
    Finset.single_le_sum (f := fun k => dhcWeights a T k)
      (fun k _ => le_of_lt (dhcWeights_pos a hT hK k)) hmem
  have hsplit1 : ∑ k ∈ Finset.univ.erase i, dhcWeights a T k
      + dhcWeights a T i = 1 := by linarith
  linarith [hlead]

/-- Контрольная точка: при равных активациях
(все `a j = c`) softmax даёт равномерное распределение
1/K — санитийная проверка нормировки. -/
theorem dhcWeights_uniform (a : Fin K → ℝ) {T : ℝ} (hT : T ≠ 0)
    (hK : 0 < K) (c : ℝ) (hc : ∀ j, a j = c) (i : Fin K) :
    dhcWeights a T i = 1 / (K : ℝ) := by
  have hsum : ∑ j, Real.exp (a j / T)
      = (K : ℝ) * Real.exp (c / T) := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [hc j])]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hne : (K : ℝ) * Real.exp (c / T) ≠ 0 :=
    mul_ne_zero (ne_of_gt (by exact_mod_cast hK : (0:ℝ) < (K : ℝ)))
      (ne_of_gt (exp_pos _))
  unfold dhcWeights
  have htot : dhcTotal a T = (K : ℝ) * Real.exp (c / T) := by
    unfold dhcTotal
    linarith [hsum]
  rw [hc i, htot, mul_comm]
  field_simp

/-- Параметрическая чувствительность 1: шаг монотонен по оценкам
гипотез при 0 ≤ ρ (сильнее поддержка → сильнее активация). -/
theorem dhcStep_mono_scores (a s s' : Fin K → ℝ)
    (C : Matrix (Fin K) (Fin K) ℝ) {rho kappa T : ℝ} (hrho : 0 ≤ rho)
    (h : ∀ j, s j ≤ s' j) (i : Fin K) :
    dhcStep a s C rho kappa T i ≤ dhcStep a s' C rho kappa T i := by
  have h1 : rho * s i ≤ rho * s' i :=
    mul_le_mul_of_nonneg_left (h i) hrho
  unfold dhcStep
  linarith

/-- Параметрическая чувствительность 2: шаг антитоничен по силе
подавления при 0 ≤ C (усиление κ подавляет активацию). -/
theorem dhcStep_antitone_kappa (a s : Fin K → ℝ)
    (C : Matrix (Fin K) (Fin K) ℝ) {rho kappa1 kappa2 T : ℝ}
    (hkap : kappa1 ≤ kappa2) (hT : T ≠ 0) (hK : 0 < K)
    (hC : ∀ i j, 0 ≤ C i j) (i : Fin K) :
    dhcStep a s C rho kappa2 T i ≤ dhcStep a s C rho kappa1 T i := by
  have hp0 : ∀ j, 0 ≤ dhcWeights a T j := fun j =>
    le_of_lt (dhcWeights_pos a hT hK j)
  have hsum : 0 ≤ ∑ j, C i j * dhcWeights a T j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hC i j) (hp0 j))
  have hdiff : (kappa2 - kappa1) * ∑ j, C i j * dhcWeights a T j
      = kappa2 * ∑ j, C i j * dhcWeights a T j
        - kappa1 * ∑ j, C i j * dhcWeights a T j := by ring
  have hdom : kappa1 * ∑ j, C i j * dhcWeights a T j
      ≤ kappa2 * ∑ j, C i j * dhcWeights a T j :=
    mul_le_mul_of_nonneg_right hkap hsum
  unfold dhcStep
  linarith [hdiff, hdom]

end Hagi.Model
