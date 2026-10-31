import Mathlib
import Hagi.System.GrowthState
import Hagi.Growth.StateBinding

/-!
# CapabilityLocal (такт №268, аудит №5 P1/K8): рост
привязан к ПОЛЕВОЙ capability через ЛОКАЛЬНОЕ условие.

Замечание аудита: MasterHAGI использует внешний канал
C : ℕ → ℝ, слабо связанный с (S t).capability. Правильная
форма (K8): из ЛОКАЛЬНОГО условия
  gain_t ≥ α · capability_t        (α > 0)
и полевой рекуррентности
  capability_{t+1} = capability_t + gain_t
напрямую следует геометрический рост ПОЛЕВОЙ величины:
  capability_T ≥ (1 + α)^T · capability_0.

Это чистая индукция без конуса/фронтира — минимальная
честная версия K8; capability_takeoff_state остаётся
усиленной конусной версией поверх той же привязки.
-/

namespace Hagi.Unified.CapabilityLocal

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- ГЛАВНАЯ ТЕОРЕМА (K8, минимальная версия): локальный
относительный прирост ⇒ геометрический рост полевой
capability. Внешний канал C не нужен — рост выводится из
рекуррентности поля и локального условия. -/
theorem capability_geometric_of_local
    (S : ℕ → Hagi.System.GrowthState X) (alpha : ℝ)
    (halpha : 0 < alpha)
    (hrec : ∀ t, (S (t + 1)).capability
      = (S t).capability + (S t).effects.growGain)
    (hlocal : ∀ t, alpha * (S t).capability
      ≤ (S t).effects.growGain)
    (T : ℕ) :
    (S 0).capability * (1 + alpha) ^ T ≤ (S T).capability := by
  induction T with
  | zero => norm_num
  | succ t ih =>
    have hstep := hrec t
    have hgain := hlocal t
    rw [hstep]
    have hfactor : (1 + alpha) * ((S t).capability)
        ≤ (S t).capability + (S t).effects.growGain := by
      rw [add_mul, one_mul]
      linarith [hgain]
    have hpow : (S 0).capability * (1 + alpha) ^ (t + 1)
        = (1 + alpha) * ((S 0).capability * (1 + alpha) ^ t) := by
      rw [pow_succ]
      ring
    rw [hpow]
    calc (1 + alpha) * ((S 0).capability * (1 + alpha) ^ t)
        ≤ (1 + alpha) * (S t).capability :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ (S t).capability + (S t).effects.growGain := hfactor

/-- СТРОГОСТЬ: при положительной начальной capability и
ненулевом gain на первом шаге рост СТРОГО геометрический
(нетривиальный witness привязки). -/
theorem capability_strict_first
    (S : ℕ → Hagi.System.GrowthState X) (alpha : ℝ)
    (halpha : 0 < alpha)
    (hc0 : 0 < (S 0).capability)
    (hrec0 : (S 1).capability
      = (S 0).capability + (S 0).effects.growGain)
    (hlocal0 : alpha * (S 0).capability
      < (S 0).effects.growGain) :
    (S 0).capability * (1 + alpha) < (S 1).capability := by
  rw [hrec0]
  nlinarith [hc0, halpha, hlocal0]

end Hagi.Unified.CapabilityLocal
