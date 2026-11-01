import Hagi.Examples.Nonvacuity

/-!
# Диагностический изолятор обструкций Gen-1

Формально доказанное ограничение модели первого поколения
(копируемые эффекты). Это утверждение — РЕГРЕССИОННЫЙ ТЕСТ
архитектуры: он фиксирует, почему Gen-1 не может быть
многошаговым, и мотивирует Gen-3 (CertifiedLoop с
HonestTransition). Импортировать в продакшн-модули не
следует: это диагностика, а не инструмент.
Продакшн-путь: `Hagi.Unified.CertifiedLoop`.
-/

namespace Hagi.Diagnostics.Obstructions

/-- Двухшаговый рост в модели копируемых эффектов
противоречив: регрессионный тест против возврата к
Gen-семантике. -/
theorem full_cycle_two_step_growth_inconsistent' {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : ℕ → Hagi.GenState X) (alpha : ℝ)
    (hα : 0 < alpha)
    (hC0 : 0 < (S 0).toGrowthState.capability)
    (h01 : (S 1).toGrowthState
      = Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (S 0).toGrowthState))))
    (h12 : (S 2).toGrowthState
      = Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (S 1).toGrowthState))))
    (hgain : ∀ t < 2, alpha * (S t).toGrowthState.capability
      <= (S t).toGrowthState.effects.growGain)
    (hcap : ∀ t < 2, (S (t + 1)).toGrowthState.capability
      <= (1 + alpha) * (S t).toGrowthState.capability) :
    False :=
  Hagi.Examples.full_cycle_two_step_growth_inconsistent S alpha hα hC0 h01 h12
    hgain hcap

end Hagi.Diagnostics.Obstructions
