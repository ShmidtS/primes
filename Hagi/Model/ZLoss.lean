import Mathlib

/-!
# Z-loss: стабилизация router-логитов (источник №43)

Источник №43: Zoph et al., "ST-MoE: Designing Stable and
Transferable Sparse Expert Models" (arXiv 2202.08906).
Z-loss z = (1/c)·(log Z)², Z = Σ exp(logit_i) — штраф
за рост нормы router-логитов MoE: удерживает логиты в
компактной зоне, предотвращая численные сбои attention и
роутинга.

Формализованное ядро (строгое):
- `zloss_bound`: если штраф удержан z ≤ B при весе c > 0,
  то |log Z| ≤ √(B·c) — логит-норма ограничена
  (квадратичный штраф ⟹ корневая граница);
- `zloss_zero`: минимум штрафа достигается ТОЧНО на
  log Z = 0 (Z = 1): сбалансированная нормировка —
  глобальный минимум, нулевой штраф несовместим с
  раскачкой логитов.
-/

namespace Hagi.Model.ZLoss

/-- Задержанный штраф ограничивает логит-норму. -/
theorem zloss_bound (c Z B : ℝ) (hc : 0 < c)
    (hpen : (1 / c) * (Real.log Z) ^ 2 ≤ B) :
    |Real.log Z| ≤ Real.sqrt (B * c) := by
  have hmul : c * ((1 / c) * (Real.log Z) ^ 2) ≤ c * B :=
    mul_le_mul_of_nonneg_left hpen hc.le
  rw [← mul_assoc, show c * (1 / c) = 1 from by field_simp,
    one_mul] at hmul
  have h2 : (Real.log Z) ^ 2 ≤ c * B := hmul
  have hB : 0 ≤ B :=
    le_trans (mul_nonneg (by positivity) (sq_nonneg _)) hpen
  have hs : Real.sqrt (B * c) ^ 2 = B * c :=
    Real.sq_sqrt (by positivity)
  have hcomm : c * B = B * c := mul_comm c B
  rw [hcomm] at h2
  apply abs_le.2
  constructor <;> nlinarith [h2, hs, Real.sqrt_nonneg (B * c)]

/-- Нулевой штраф ⟺ log Z = 0 (сбалансированная
нормировка). -/
theorem zloss_zero (c Z : ℝ) (hc : 0 < c) (_hZ : 0 < Z) :
    (1 / c) * (Real.log Z) ^ 2 = 0 ↔ Real.log Z = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 (by positivity)
    · exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  · intro h
    rw [h]
    norm_num

end Hagi.Model.ZLoss
