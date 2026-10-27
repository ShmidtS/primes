import Mathlib.Tactic
import Hagi.Growth.AdaptiveQuery
import Hagi.Growth.ConeDynamics
import Hagi.Growth.FiberNecessity
import Hagi.Growth.FrontierProduction
import Hagi.Growth.GainCeiling
import Hagi.Growth.GammaDeficit
import Hagi.Growth.Grow
import Hagi.Growth.GrowthCeiling
import Hagi.Growth.GrowthGate
import Hagi.Growth.IntegrationOrder

/-!
# Unified.GrowthLaws — фасад законов роста

Слой-6 фасад: потенциал-телескоп (диссипативный баланс),
гамма-дефицит, конусная динамика данных.
-/

namespace Hagi.Unified

export Hagi.Growth (potential_telescope
  gamma_min_for_target cone_data_invariant)

/-- ЗАКОН РОСТА (сводка): (1) диссипативный баланс —
потенциал-телескоп W T + Σε ≤ W 0 + Σb; (2) конусная
инвариантность данных (k·C ≤ D сохраняется шагом). Рост
ограничен и структурно инвариантен. -/
theorem growth_balanced_and_conic
    (W eps b : ℕ → ℝ) (T : ℕ)
    (hVnn : ∀ t, 0 ≤ W t)
    (hstep : ∀ t, W (t + 1) ≤ W t - eps t + b t)
    (cd : Hagi.Growth.ConeData) (k : ℝ)
    (hk : 0 ≤ k) (hγ : 0 ≤ cd.γ) (hρ : 0 ≤ cd.ρ)
    (hCpos : 0 < cd.C T)
    (hcone : k * cd.C T ≤ cd.D T)
    (h_dyn : cd.ρ * cd.D T + cd.β * cd.C T - cd.ξ T
      ≤ cd.D (T + 1))
    (h_C_cap : cd.C (T + 1) ≤ (1 + cd.γ * k) * cd.C T)
    (hβ : k * (1 + cd.γ * k - cd.ρ) + cd.ξ T / cd.C T
      ≤ cd.β) :
    W T + ∑ t ∈ Finset.range T, eps t
      ≤ W 0 + ∑ t ∈ Finset.range T, b t
      ∧ k * cd.C (T + 1) ≤ cd.D (T + 1) :=
  ⟨potential_telescope W eps b T hVnn hstep,
    Hagi.Growth.cone_data_invariant cd k T hk hγ hρ hCpos
      hcone h_dyn h_C_cap hβ⟩

end Hagi.Unified
