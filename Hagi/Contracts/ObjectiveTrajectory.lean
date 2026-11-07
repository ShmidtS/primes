/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-! Objective-height helpers over real sequences. -/

namespace Hagi.Contracts.ObjectiveTrajectory

open Filter Topology

/-- Dominating drops telescope against the actual objective differences. -/
theorem sum_drop_le_initial_sub
    (E δ : ℕ → ℝ) (T : ℕ)
    (hδ : ∀ t, δ t ≤ E t - E (t + 1)) :
    ∑ t ∈ Finset.range T, δ t ≤ E 0 - E T := by
  calc
    ∑ t ∈ Finset.range T, δ t ≤
        ∑ t ∈ Finset.range T, (E t - E (t + 1)) :=
      Finset.sum_le_sum fun t _ht => hδ t
    _ = E 0 - E T := by
      simpa using Finset.sum_range_sub' E T

/-- A nonnegative antitone sequence converges to its real infimum. -/
theorem tendsto_ciInf_of_antitone_nonneg
    (E : ℕ → ℝ) (hanti : Antitone E) (hnn : ∀ t, 0 ≤ E t) :
    Tendsto E atTop (𝓝 (⨅ t, E t)) := by
  apply tendsto_atTop_ciInf hanti
  refine ⟨0, ?_⟩
  exact fun x hx => by rcases hx with ⟨t, rfl⟩; exact hnn t

/-- Nonnegative infimum follows from nonnegative sequence values. -/
theorem ciInf_nonneg (E : ℕ → ℝ) (hnn : ∀ t, 0 ≤ E t) :
    0 ≤ ⨅ t, E t := le_ciInf hnn

/-- Scaling removes the common positive denominator in a weighted
finite budget without any infinite-sum or convergence premise. -/
theorem sum_le_of_sum_two_mul_div_le {κ A : ℝ} {f : ℕ → ℝ}
    (hκ : 0 < κ)
    (hbudget : ∀ T, ∑ t ∈ Finset.range T, 2 * f t / κ ≤ A)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, f t ≤ κ * A / 2 := by
  calc
    ∑ t ∈ Finset.range T, f t =
        κ / 2 * ∑ t ∈ Finset.range T, 2 * f t / κ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      field_simp [ne_of_gt hκ]
    _ ≤ κ / 2 * A :=
      mul_le_mul_of_nonneg_left (hbudget T) (by positivity)
    _ = κ * A / 2 := by ring

/-- Bounded nonnegative finite sums give summability and a sharper,
positive-scale total budget. -/
theorem summable_and_tsum_le_of_sum_two_mul_div_le
    {κ A : ℝ} {f : ℕ → ℝ} (hκ : 0 < κ)
    (hf : ∀ t, 0 ≤ f t)
    (hbudget : ∀ T, ∑ t ∈ Finset.range T, 2 * f t / κ ≤ A) :
    Summable f ∧ ∑' t, f t ≤ κ * A / 2 := by
  have hscaled : ∀ T, ∑ t ∈ Finset.range T, f t ≤ κ * A / 2 :=
    fun T => sum_le_of_sum_two_mul_div_le hκ hbudget T
  have hs : Summable f := summable_of_sum_range_le hf hscaled
  exact ⟨hs, hs.tsum_le_of_sum_range_le hscaled⟩

/-- A bounded finite average implies a best-index bound in every
nonempty finite range.  Nothing asserts that the last value is least. -/
theorem exists_le_of_sum_two_mul_div_le
    {κ A : ℝ} {f : ℕ → ℝ} (hκ : 0 < κ)
    (hbudget : ∀ T, ∑ t ∈ Finset.range T, 2 * f t / κ ≤ A)
    {T : ℕ} (hT : 0 < T) :
    ∃ t ∈ Finset.range T, f t ≤ κ * A / (2 * (T : ℝ)) := by
  have hscaled := sum_le_of_sum_two_mul_div_le hκ hbudget T
  by_contra h
  push Not at h
  have hstrict : (∑ _t ∈ Finset.range T, κ * A / (2 * (T : ℝ))) <
      ∑ t ∈ Finset.range T, f t :=
    Finset.sum_lt_sum_of_nonempty
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT)) (fun t ht => h t ht)
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hT
  have hconst : (∑ _t ∈ Finset.range T, κ * A / (2 * (T : ℝ))) =
      κ * A / 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [ne_of_gt hTpos]
  rw [hconst] at hstrict
  exact (not_lt_of_ge hscaled) hstrict

end Hagi.Contracts.ObjectiveTrajectory
