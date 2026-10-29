import Mathlib

/-!
# PPO-clip: консервативная отсечка surrogate (источник №32)

Источник №32: Schulman et al., "Proximal Policy Optimization"
(arXiv 1707.06347). Clipped surrogate objective
L = min(r·A, clip(r, 1−ε, 1+ε)·A), где r = π_θ/π_old —
probability ratio (r ≥ 0), A — advantage. Клип удерживает
обновление политики в доверительной зоне вокруг r = 1.

Формализованное ядро (строгое):
- `ppoClip`: clip(r, lb, ub) = max lb (min ub r);
- `ppoClip_le_upper/lower`: клипнутый ratio в [lb, ub];
- `ppoClip_mono`: клип монотонен по r;
- `ppoClip_fixed`: lb ≤ r ≤ ub ⟹ клип тождествен;
- `ppo_clip_term_bound`: |clip(r,1−ε,1+ε)·A| ≤ (1+ε)·|A|;
- `ppo_surr_upper_bound`: L ≤ (1+ε)·|A| — клипнутый
  surrogate ОГРАНИЧЕН СВЕРХУ независимо от r: обновление
  политики не может дать неограниченный выигрыш
  (conservative bound ядра PPO; нижняя сторона не
  ограничивается — там штраф, а не выигрыш).
-/

namespace Hagi.Optimization.PPOClip

/-- Клип скаляра в отрезок [lb, ub]. -/
def ppoClip (r lb ub : ℝ) : ℝ := max lb (min ub r)

theorem ppoClip_le_upper (r lb ub : ℝ) (hlb : lb ≤ ub) :
    ppoClip r lb ub ≤ ub :=
  max_le hlb (min_le_left ub r)

theorem ppoClip_le_lower (r lb ub : ℝ) :
    lb ≤ ppoClip r lb ub := le_max_left lb (min ub r)

theorem ppoClip_mono (r r' lb ub : ℝ) (h : r ≤ r')
    (_hlb : lb ≤ ub) : ppoClip r lb ub ≤ ppoClip r' lb ub := by
  unfold ppoClip
  exact max_le_max (le_refl lb) (min_le_min (le_refl ub) h)

/-- Внутри отрезка клип тождествен. -/
theorem ppoClip_fixed (r lb ub : ℝ) (h1 : lb ≤ r) (h2 : r ≤ ub) :
    ppoClip r lb ub = r := by
  unfold ppoClip
  rw [min_eq_right h2]
  exact max_eq_right h1

/-- Абсолютное значение клипнутого члена ограничено. -/
theorem ppo_clip_term_abs_bound (r e A : ℝ) (he : 0 ≤ e) :
    |ppoClip r (1 - e) (1 + e) * A| ≤ (1 + e) * |A| := by
  have hlow : 1 - e ≤ ppoClip r (1 - e) (1 + e) :=
    ppoClip_le_lower r (1 - e) (1 + e)
  have hup : ppoClip r (1 - e) (1 + e) ≤ 1 + e :=
    ppoClip_le_upper r (1 - e) (1 + e) (by linarith)
  have habs : |ppoClip r (1 - e) (1 + e)| ≤ 1 + e := by
    apply abs_le.2
    constructor
    · have hn := neg_le_abs (ppoClip r (1 - e) (1 + e))
      linarith [hlow, hn, he]
    · linarith [hup]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right habs (abs_nonneg A)

/-- Surrogate L = min(r·A, clip·A) ограничен сверху:
обновление не может дать выигрыш больше (1+ε)|A|,
каким бы ни стало r. -/
theorem ppo_surr_upper_bound (r e A : ℝ) (he : 0 ≤ e) :
    min (r * A) (ppoClip r (1 - e) (1 + e) * A) ≤ (1 + e) * |A| :=
  le_trans (min_le_right _ _)
    (le_trans (le_abs_self _)
      (ppo_clip_term_abs_bound r e A he))

end Hagi.Optimization.PPOClip
