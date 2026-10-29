import Mathlib

/-!
# Adam bias correction (источник №28)

Источник №28: Loshchilov & Hutter, "Decoupled Weight Decay
Regularization" / Adam (arXiv 1711.05101, §2). Экспоненциальная
скользящая средняя градиента с нулевой инициализацией
m_{t+1} = β·m_t + (1−β)·g смещена к нулю на ранних шагах;
коррекция m̂_t = m_t/(1−β^t) устраняет смещение.

Формализованное ядро (строгое):
- `adamM_recur`: closed form (1−β)·g·∑_{i<t} β^i — это в
  точности рекуррентность m₀ = 0, m_{t+1} = β·m_t + (1−β)·g;
- `adam_unbiased_const`: на постоянном градиенте g коррекция
  ТОЧНА: m̂_t = m_t/(1−β^t) = g для всех t ≥ 1 при 0 ≤ β < 1;
- `adam_bias_bound`: без коррекции m_t = g − β^t·g —
  начальное смещение затухает геометрически.
-/

namespace Hagi.Optimization.AdamBias

/-- Closed form: (1−β)·∑_{i<t} β^i = 1 − β^t. -/
theorem one_sub_beta_geom (β : ℝ) (t : ℕ) :
    (1 - β) * ∑ i ∈ Finset.range t, β ^ i = 1 - β ^ t := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [Finset.sum_range_succ (fun i => β ^ i) t]
    have hp : β ^ (t + 1) = β ^ t * β := by ring
    have hp2 : β ^ (t + 1) = β * β ^ t := by ring
    nlinarith [hp, hp2]

/-- Геометрическое затухание степени: 0 ≤ β < 1, t ≥ 1
⟹ β^t < 1. -/
theorem pow_lt_one' (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1)
    (t : ℕ) (ht : 1 ≤ t) : β ^ t < 1 := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; norm_num; linarith
    · have hp : β ^ (t + 1) = β * β ^ t := by ring
      have hle : β ^ t ≤ 1 := le_of_lt (ih h0)
      rw [hp]
      nlinarith [hβ0, hβ, hle]

/-- Экспоненциальная средняя на постоянном градиенте g,
t шагов, нулевая инициализация. -/
def adamM (β g : ℝ) (t : ℕ) : ℝ :=
  (1 - β) * g * ∑ i ∈ Finset.range t, β ^ i

/-- Closed form удовлетворяет рекуррентности Адама. -/
theorem adamM_recur (β g : ℝ) :
    adamM β g 0 = 0 ∧ ∀ t : ℕ,
      adamM β g (t + 1) = β * adamM β g t + (1 - β) * g := by
  refine ⟨by unfold adamM; rw [Finset.sum_range_zero]; ring, fun t => ?_⟩
  unfold adamM
  rw [Finset.sum_range_succ (fun i => β ^ i) t]
  rcases eq_or_ne β 1 with hβ1 | hβ1
  · subst hβ1
    norm_num
  · have hg := one_sub_beta_geom β t
    have hS : ∑ i ∈ Finset.range t, β ^ i = (1 - β ^ t) / (1 - β) := by
      field_simp
      linarith
    rw [hS]
    field_simp
    ring

/-- Без коррекции смещение к нулю затухает геометрически:
m_t = g − β^t·g = (1−β^t)·g. -/
theorem adam_bias_bound (β g : ℝ) (t : ℕ) :
    adamM β g t = g - β ^ t * g := by
  unfold adamM
  have h2 : (1 - β) * g * ∑ i ∈ Finset.range t, β ^ i
      = g * ((1 - β) * ∑ i ∈ Finset.range t, β ^ i) := by ring
  rw [h2, one_sub_beta_geom]
  ring

/-- ЯДРО №28: на постоянном градиенте коррекция смещения
ТОЧНА: m̂_t = m_t/(1−β^t) = g. -/
theorem adam_unbiased_const (β g : ℝ) (hβ0 : 0 ≤ β)
    (hβ : β < 1) (t : ℕ) (ht : 1 ≤ t) :
    adamM β g t / (1 - β ^ t) = g := by
  have hlt : β ^ t < 1 := pow_lt_one' β hβ0 hβ t ht
  have hden : 1 - β ^ t ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (ne_of_lt hlt))
  have hb := adam_bias_bound β g t
  rw [hb]
  have hgg : g - β ^ t * g = g * (1 - β ^ t) := by ring
  rw [hgg]
  field_simp

end Hagi.Optimization.AdamBias
