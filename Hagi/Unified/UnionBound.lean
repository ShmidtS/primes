/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Probability.CertifiedEstimator

/-!
# UnionBoundNonneg — объединение событий для мер с нулевой массой

Стандартный `union_bound_finite` требует строго положительных
весов (hq : 0 < q v); координатные произведения `prodDens p ω`
имеют нули (`p i v = 0`). Эта лемма — та же конечная ladder
union bound, но при `0 ≤ q v`: точечная индикаторная
надстройка + перестановка сумм (R555, часть 1).
-/

open scoped BigOperators

namespace Hagi.Unified

/-- **Union bound при неотрицательных весах (R555)**. -/
theorem union_bound_nonneg {W : Type*} [Fintype W]
    (q : W → ℝ) (hq : ∀ v, 0 ≤ q v) (S : ℕ → W → Prop)
    [∀ t, DecidablePred (S t)] (T : ℕ) :
    ∑ v ∈ Finset.filter (fun v => ∃ t < T, S t v) Finset.univ, q v
      ≤ ∑ t ∈ Finset.range T,
        ∑ v ∈ Finset.filter (S t) Finset.univ, q v := by
  classical
  have hRHS : ∑ t ∈ Finset.range T,
      ∑ v ∈ Finset.filter (S t) Finset.univ, q v
      = ∑ t ∈ Finset.range T, ∑ v : W, (if S t v then q v else 0) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.sum_filter]
  rw [Finset.sum_filter, hRHS, ← Finset.sum_comm]
  refine Finset.sum_le_sum (fun v _ => ?_)
  by_cases hE : ∃ t < T, S t v
  · have hEcopy := hE
    obtain ⟨t, ht, hSt⟩ := hEcopy
    have hmem : t ∈ Finset.range T := Finset.mem_range.mpr ht
    have hs := Finset.single_le_sum
      (f := fun t' : ℕ => (if S t' v then q v else 0))
      (fun x _ => by split <;> simp [hq v]) hmem
    rw [if_pos hSt] at hs
    simp only [if_pos hE]
    exact hs
  · rw [if_neg hE]
    refine le_trans (Finset.sum_nonneg (fun t _ => ?_)) (le_refl _)
    split <;> simp [hq v]

end Hagi.Unified
