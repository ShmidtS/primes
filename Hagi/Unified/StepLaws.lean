import Hagi.Step.ArmijoAcceptance
import Hagi.Step.CausalFilter
import Hagi.Step.Compound
import Hagi.Step.FrobeniusLMO
import Hagi.Step.GPM
import Hagi.Step.LazyAdam
import Hagi.Step.LazyAdamMomentum
import Hagi.Runtime.ControllerGates
import Hagi.Runtime.LiveDeltaQuant
import Hagi.Sparsity.SparseStep0

/-!
# Unified.StepLaws — фасад теории шага

Слой-6 фасад: условия Armijo, стабильный SGD-шаг, точный
lazy-decay, GQA-фильтрация, компаунд-стабилизация.
-/

open Real InnerProductSpace

namespace Hagi.Unified

export Hagi.Step (armijo_sufficient_decrease sgd_stable_step
  lazyDecay_exact compound_c_stabilizes)

/-- ТЕОРИЯ ШАГА (сводка): (1) условие Armijo с направлением
спуска и гладкостью даёт достаточное убывание; (2) SGD-шаг с
η < 2⟪G,G⟫/(λ‖G‖²) строго убывает. Шаг одновременно
согласован и стабилен. -/
theorem step_armijo_and_sgd_stable
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (J : X → ℝ) (g d : X)
    (L c1 alpha : ℝ) (hL : 0 ≤ L) (hc1 : 0 < c1)
    (halpha : 0 < alpha)
    (hdir : ⟪g, d⟫_ℝ ≤ -(c1 * ‖d‖ ^ 2))
    (hsmooth : J (0 + alpha • d) ≤ J 0 + ⟪g, alpha • d⟫_ℝ
      + L / 2 * ‖alpha • d‖^2)
    (L' G eta lam : ℝ)
    (heta_pos : 0 < eta) (hlam : 0 < lam) (hG : G ≠ 0)
    (hquad : L' ≤ L - eta * ⟪G, G⟫_ℝ
      + lam / 2 * eta ^ 2 * ‖G‖ ^ 2)
    (heta : eta < 2 * ⟪G, G⟫_ℝ / (lam * ‖G‖ ^ 2)) :
    J (0 + alpha • d) ≤ J 0 - (c1 - L * alpha / 2) * alpha * ‖d‖^2
      ∧ L' < L :=
  ⟨armijo_sufficient_decrease J g d L c1 alpha hL hc1 halpha
      hdir hsmooth,
    sgd_stable_step L L' G eta lam heta_pos hlam hG hquad heta⟩

end Hagi.Unified
