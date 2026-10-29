import Mathlib

/-!
# Speculative Decoding: ожидаемый выигрыш (источник №27)

Источник №27: Chen et al., "Accelerating Large Language Model
Decoding with Speculative Sampling" (arXiv 2302.01318).
Драфт-модель генерирует k токенов, цель проверяет их за один
параллельный проход; α — вероятность приёмки одного токена.

Формализованное ядро (строгое):
- accept_chain_prob: вероятность принятия всех k драфт-
  токенов подряд = α^k (геометрическая цепочка);
- speculative_expected_tokens: ожидаемое число принятых
  токенов за цикл = (1 - α^{k+1})/(1 - α) при α ≠ 1
  (геометрическая серия);
- speculative_win: чистый выигрыш против k+1 последовательных
  полных проходов строго положителен при α > 0, k ≥ 1 —
  амортизация цели по k+1 токенам за один проход.
-/

namespace Hagi.Model.Speculative

/-- Вероятность принять всю цепочку из k драфт-токенов. -/
theorem accept_chain_prob (α : ℝ) (k : ℕ) :
    (∏ _i ∈ Finset.range k, α) = α ^ k := by
  simp

/-- Ожидаемое число принятых токенов за один цикл:
геометрическая серия E = ∑_{i=0}^{k} α^i. -/
theorem speculative_expected_tokens (α : ℝ) (hα : α ≠ 1)
    (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), α ^ i = (1 - α ^ (k + 1)) / (1 - α) := by
  have hden : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  induction k with
  | zero => rw [Finset.sum_range_one, pow_one]; field_simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow : α ^ (k + 1 + 1) = α ^ (k + 1) * α := by ring
    field_simp
    ring

/-- Чистый выигрыш спекулятивного цикла: (k+1) полных
проходов заменяются на один; при α > 0 и k ≥ 1 ожидаемое
число токенов за проход СТРОГО превышает 1 (порог
безубыточности одной цели = 1 токен/проход). -/
theorem speculative_win (α : ℝ) (hpos : 0 < α)
    (k : ℕ) (hk : 1 ≤ k) :
    1 < ∑ i ∈ Finset.range (k + 1), α ^ i := by
  have hsub : Finset.range 2 ⊆ Finset.range (k + 1) := by
    intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  have hkey : Finset.range (k + 1)
      = Finset.range 2 ∪ (Finset.range (k + 1) \ Finset.range 2) := by
    ext i; simp only [Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_range]; omega
  rw [hkey, Finset.sum_union (by simp [Finset.disjoint_iff_inter_eq_empty])]
  have hbase : ∑ i ∈ Finset.range 2, α ^ i = 1 + α := by simp; ring
  have hnn : 0 ≤ ∑ i ∈ Finset.range (k + 1) \ Finset.range 2, α ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg hpos.le i)
  rw [hbase]
  linarith

end Hagi.Model.Speculative
