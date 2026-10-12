/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

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

/-- Shannon entropy: `−∑ v, p v * log (p v)`. -/
noncomputable def entDef (p : V → ℝ) : ℝ :=
  -∑ v, p v * Real.log (p v)

/-- Total variation distance (half the L1 distance). -/
noncomputable def tvDef (p q : V → ℝ) : ℝ :=
  (∑ v, |p v - q v|) / 2

/-- The softmax: `exp (z a) / ∑ b, exp (z b)`. -/
noncomputable def softDef {k : Type*} [Fintype k] (z : k → ℝ) : k → ℝ :=
  fun a => Real.exp (z a) / ∑ b, Real.exp (z b)

/-- **KL ≥ 0 (Gibbs)**: для строго положительных вероятностных
векторов KL-расхождение неотрицательно. Канон R334:
потребители (`Data/DField.KLdiv`, `Energy/Variational.kldiv'`,
все rfl-мосты к `klDef`) делегируют сюда. -/
theorem kl_nonneg (q p : V → ℝ)
    (hq : ∀ v, 0 < q v) (hp : ∀ v, 0 < p v)
    (hsumq : ∑ v, q v = 1) (hsump : ∑ v, p v = 1) :
    0 ≤ klDef q p := by
  have hterm : ∀ v : V, q v - p v ≤ q v * Real.log (q v / p v) := by
    intro v
    have h1 : Real.log (p v / q v) ≤ p v / q v - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hp v) (hq v))
    have h2 : Real.log (p v / q v) = -Real.log (q v / p v) := by
      rw [Real.log_div (ne_of_gt (hp v)) (ne_of_gt (hq v)),
          Real.log_div (ne_of_gt (hq v)) (ne_of_gt (hp v))]
      ring
    rw [h2] at h1
    have h3 : q v * (-(Real.log (q v / p v))) ≤ q v * (p v / q v - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt (hq v))
    have h4 : q v * (p v / q v - 1) = p v - q v := by
      have hqv : q v ≠ 0 := ne_of_gt (hq v)
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

end Hagi.Prelude
