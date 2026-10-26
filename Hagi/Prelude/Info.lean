/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic


/-!
# Prelude.Info — the single information-theory prelude

The canonical information-theoretic definitions:

* `klDef q p := ∑ v, q v * log (q v / p v)` — KL divergence
  (`q` is the sampling distribution);
* `entDef p := −∑ v, p v * log (p v)` — Shannon entropy;
* `tvDef p q := (∑ v, |p v − q v|)/2` — total variation;
* `softDef z := exp(z)/Σexp` — softmax.

Bridge identities to historical consumer names are stated in
the consumers, each as a one-line `rfl`.
-/
namespace Hagi.Prelude

open Finset

variable {V : Type*} [Fintype V]

/-- KL divergence: `∑ v, q v * log (q v / p v)` (`q` is the
sampling distribution). -/
noncomputable def klDef (q p : V → ℝ) : ℝ :=
  ∑ v, q v * Real.log (q v / p v)

/-- КОНТРАКТ ДОПУСТИМОСТИ KL (аудит v4 §3.9): klDef определена
на произвольных вещественных векторах, где log(0) и деление
на 0 дают конечные значения Lean — математическая KL при
q ≰ p (носитель q не вложен в носитель p) равна +∞.
Допустимый вход: вероятностные векторы с вложенным носителем
(q ≪ p); на них конечная klDef совпадает с математической
KL и корректна (kl_nonneg и все мосты уже требуют p > 0). -/
def KLSupported (q p : V → ℝ) : Prop :=
  (∀ v, 0 ≤ q v) ∧ (∑ v, q v = 1)
    ∧ (∀ v, 0 < p v) ∧ (∑ v, p v = 1)

/-- Допустимость даёт строгую положительность p всюду —
частный случай вложения носителей (наиболее общий случай
поддержки сведён к строгой положительности; расширенная
ENNReal-семантика остаётся отдельным слоем). -/
theorem KLSupported_pos (q p : V → ℝ) (h : KLSupported q p) :
    ∀ v, 0 < p v := h.2.2.1

/-- На допустимых входах слагаемые klDef корректны:
конечные логарифмы положительных отношений (для активных
компонент q v > 0; слагаемые с q v = 0 равны нулю и
семантически корректны как 0·log 0 = 0). -/
theorem klDef_terms_finite (q p : V → ℝ) (h : KLSupported q p)
    (v : V) (hq : 0 < q v) : 0 < q v / p v :=
  div_pos hq (h.2.2.1 v)

/-- Shannon entropy: `−∑ v, p v * log (p v)`. -/
noncomputable def entDef (p : V → ℝ) : ℝ :=
  -∑ v, p v * Real.log (p v)

/-- Total variation distance (half the L1 distance). -/
noncomputable def tvDef (p q : V → ℝ) : ℝ :=
  (∑ v, |p v - q v|) / 2

/-- The softmax: `exp (z a) / ∑ b, exp (z b)`. -/
noncomputable def softDef {k : Type*} [Fintype k] (z : k → ℝ) : k → ℝ :=
  fun a => Real.exp (z a) / ∑ b, Real.exp (z b)

/-- Softmax is strictly positive (exp positive over a positive
normalizer). -/
theorem softDef_pos {k : Type*} [Fintype k] [Nonempty k] (z : k → ℝ) (a : k) :
    0 < softDef z a := by
  unfold softDef
  exact div_pos (Real.exp_pos _)
    (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)

/-- Softmax normalizes: `∑ a, softDef z a = 1`. -/
theorem softDef_sum_one {k : Type*} [Fintype k] [Nonempty k] (z : k → ℝ) :
    ∑ a, softDef z a = 1 := by
  have hZ : 0 < ∑ b : k, Real.exp (z b) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  unfold softDef
  rw [← Finset.sum_div (Finset.univ : Finset k)]
  rw [div_self (Ne.symm (ne_of_lt hZ))]

/-- **KL ≥ 0 при нулевых вероятностях q** (§1.2 аудита v3:
явная постановка для q ≥ 0, p > 0): KL-расхождение
неотрицательно, когда q лишь неотрицательно (слагаемые с
q v = 0 равны 0: 0 · log 0 = 0). Строгая положительность
требуется только от p. -/
theorem kl_nonneg_of_nonneg (q p : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1) :
    0 ≤ klDef q p := by
  have hterm : ∀ v : V, q v - p v ≤ q v * Real.log (q v / p v) := by
    intro v
    by_cases hq0 : q v = 0
    · rw [hq0, zero_div, Real.log_zero, mul_zero]
      linarith [hp v]
    · have hqpos : 0 < q v := lt_of_le_of_ne (hq v) (Ne.symm hq0)
      have h1 : Real.log (p v / q v) ≤ p v / q v - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hp v) hqpos)
      have h2 : Real.log (p v / q v) = -Real.log (q v / p v) := by
        rw [Real.log_div (ne_of_gt (hp v)) (ne_of_gt hqpos),
            Real.log_div (ne_of_gt hqpos) (ne_of_gt (hp v))]
        ring
      rw [h2] at h1
      have h3 : q v * (-(Real.log (q v / p v))) ≤ q v * (p v / q v - 1) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hqpos)
      have h4 : q v * (p v / q v - 1) = p v - q v := by
        have hqv : q v ≠ 0 := ne_of_gt hqpos
        have h : p v / q v - 1 = (p v - q v) / q v := by
          field_simp [hqv]
        rw [h]
        exact mul_div_cancel₀ (p v - q v) hqv
      rw [h4, mul_neg] at h3
      linarith
  have hsum : ∑ v, (q v - p v) ≤ ∑ v, q v * Real.log (q v / p v) :=
    Finset.sum_le_sum fun v _ => hterm v
  unfold klDef at hsum ⊢
  rw [Finset.sum_sub_distrib, hsumq, hsump] at hsum
  norm_num at hsum
  exact hsum

/-- **KL ≥ 0 (Gibbs)**: для строго положительных вероятностных
векторов KL-расхождение неотрицательно. Канон R334:
потребители (`Data/DField.KLdiv`, `Energy/Variational.kldiv'`,
все rfl-мосты к `klDef`) делегируют сюда. -/
theorem kl_nonneg (q p : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1) :
    0 ≤ klDef q p := by
  -- dedup: the strict case is the special case q > 0 of the
  -- zero-tolerant canon below (one-line delegation)
  exact kl_nonneg_of_nonneg q p (fun v => le_of_lt (hq v)) hp hsumq hsump

end Hagi.Prelude
