import Hagi.System.DiscreteStep
import Hagi.System.StepCertificate
import Hagi.System.UnifiedStep
import Hagi.Audit.EqualBudget
import Hagi.Audit.Exactness
import Hagi.Discovery.PPT
import Hagi.Numerics.SoftmaxFix
import Hagi.Omni.TemporalState
import Hagi.Ensemble.QFormerBridge
import Hagi.External.Diversity
import Hagi.Spectral.RankGrowth
import Hagi.Information.Pinsker

/-!
# Unified.MiscCore — фасад разрозненных теоремных модулей

Слой-6 фасад: дискретный шаг (квантованный телескоп),
сертификаты шага, Айкен-экстраполяция, PPT-норма,
softmax-фикс, временные состояния, QFormer-мост,
разнообразие, ранговый рост.
-/

namespace Hagi.Unified

export Hagi.System (quantized_descent_telescope)
export Hagi.Audit (aitken_exact exp_jensen)

/-- ЧИСЛЕННАЯ ДИСЦИПЛИНА (сводка): (1) квантованный
градиентный телескоп накапливает ошибку не более T·Δ/2;
(2) Айкен-экстраполяция геометрического убывания ТОЧНА.
Дискретизация контролируема, ускорение точно. -/
theorem misc_quantized_telescope_and_aitken
    (x g : ℕ → ℝ) (Δ γ : ℝ)
    (hΔ : 0 < Δ) (T : ℕ)
    (hstep : ∀ t < T, x (t + 1)
      = Hagi.Energy.gridQ Δ hΔ (x t - γ * g t))
    (Lstar d c L0 L1 L2 : ℝ)
    (h0 : L0 = Lstar + d) (h1 : L1 = Lstar + d * c)
    (h2 : L2 = Lstar + d * c^2) (hd : d ≠ 0) (hc : c ≠ 1) :
    x T ≤ x 0 - (∑ t ∈ Finset.range T, γ * g t) + (T : ℝ) * Δ / 2
      ∧ (L0 * L2 - L1^2) / (L0 + L2 - 2*L1) = Lstar
        ∧ (L2 - L1) / (L1 - L0) = c :=
  ⟨quantized_descent_telescope x g Δ γ hΔ T hstep,
    aitken_exact Lstar d c L0 L1 L2 h0 h1 h2 hd hc⟩

end Hagi.Unified
