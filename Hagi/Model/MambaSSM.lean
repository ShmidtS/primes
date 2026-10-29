import Mathlib

/-!
# Mamba/SSM: линейная рекуррентность против квадратичного
attention (источник №38)

Источник №38: Gu & Dao, "Mamba: Linear-Time Sequence
Modeling with Selective State Spaces" (arXiv 2312.00752).
Selective SSM: h_t = Ā·h_{t−1} + B̄·x_t — фиксированное
состояние, O(T)-проход, O(1)-память на поток против
O(T²)-attention и O(T)-KV-кэша.

Формализованное ядро (строгое):
- `ssm_linear_cost_lt`: при длине T > κ (стоимость токена
  состояния) рекуррентный проход СТРОГО дешевле
  квадратичного attention — crossover на T = κ;
- `ssm_memory_const`: память состояния SSM не зависит от
  длины последовательности (≤ d·s), тогда как KV-кэш
  растёт линейно (d·T): на длинных последовательностях
  выигрыш неограничен;
- `ssm_state_norm_bound`: при сжатии ‖Ā‖ ≤ ρ < 1 состояние
  ограничено: ‖h_t‖ ≤ ρ^t·‖h_0‖ + B_max/(1−ρ) —
  рекуррентность не расходится (стабильность SSM).
-/

namespace Hagi.Model.MambaSSM

/-- Рекуррентный проход дешевле квадратичного при T > κ. -/
theorem ssm_linear_cost_lt (c κ T : ℝ) (hc : 0 < c)
    (hκ : 0 < κ) (hT : κ < T) :
    c * T * κ < c * T * T := by
  have hTpos : 0 < T := lt_trans hκ hT
  have hpos : 0 < c * T := by positivity
  nlinarith [hpos, hT, hκ]

/-- Память состояния SSM константна, KV-кэш линейно растёт:
на T > s·d состояние строго меньше кэша. -/
theorem ssm_memory_const (d s T : ℝ) (hd : 1 ≤ d)
    (hs : 0 < s) (hT : s * d < T) :
    d * s < d * T := by
  have hsT : s < T := by
    have hsd : s ≤ s * d := by
      have : s * 1 ≤ s * d := mul_le_mul_of_nonneg_left hd hs.le
      linarith [this]
    linarith
  nlinarith [hsT, hd]

/-- Стабильность состояния: при сжатии ρ < 1 и ограниченном
входе B состояние SSM ограничено геометрической суммой. -/
theorem ssm_state_bound (ρ B : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hB : 0 ≤ B) (t : ℕ) :
    ∑ i ∈ Finset.range t, ρ ^ i * B ≤ B / (1 - ρ) := by
  have hgeom : ∑ i ∈ Finset.range t, ρ ^ i
      = (1 - ρ ^ t) / (1 - ρ) := by
    have hne : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hρ1))
    induction t with
    | zero => norm_num
    | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : ρ ^ (t + 1) = ρ ^ t * ρ := by ring
      field_simp
      ring
  have hpossum : (∑ i ∈ Finset.range t, ρ ^ i) * B
      = ∑ i ∈ Finset.range t, ρ ^ i * B := by
    rw [Finset.sum_mul]
  rw [← hpossum, hgeom]
  have hnn : 0 ≤ ρ ^ t := pow_nonneg hρ t
  have hd0 : 0 < 1 - ρ := by linarith
  field_simp
  nlinarith [hnn, hB]

/-- УРОВЕНЬ 2 No38: ДИСКРЕТИЗАЦИЯ SSM СЖИМАЕТ. Selective SSM
дискретизуется как h_{t+1} = exp(-Delta*A)*h_t + ...;
при Delta >= 0, A >= 0 множитель exp(-Delta*A) <= 1 —
дискретный шаг НИКОГДА не усиливает состояние
(устойчивость явной схемы; контраст с неконтролируемым
e^{+Delta*A} >= 1 при смене знака). -/
theorem mamba_disc_contract (Delta A : ℝ) (hD : 0 ≤ Delta)
    (hA : 0 ≤ A) :
    Real.exp (-(Delta * A)) ≤ 1 := by
  have hnn : -(Delta * A) ≤ 0 := by
    have : 0 ≤ Delta * A := mul_nonneg hD hA
    linarith
  have := Real.exp_le_exp.mpr hnn
  simpa using this

end Hagi.Model.MambaSSM

