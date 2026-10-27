import Hagi.Dynamics.CapabilityGain
import Hagi.Dynamics.ControllerPolicy
import Hagi.Dynamics.DistillationRate
import Hagi.Dynamics.EndpointContraction
import Hagi.Dynamics.FastGrowth
import Hagi.Dynamics.ProxyGap
import Hagi.Dynamics.UrgencyDepth
import Hagi.Dynamics.WallClockTakeoff
import Hagi.Omni.CapabilityMatrix
import Hagi.Omni.CrossModalGap
import Hagi.Omni.OmniInvariant
import Hagi.Omni.SharedStateComposition

/-!
# Unified.DynamicsLaws — фасад динамики и омнимодальности

Слой-6 фасад: счётный такофф (мультипликативный рост),
KL-контракция при дистилляции, endpoint-контракция,
wall-clock такофф, омни-инварианты.
-/

namespace Hagi.Unified

export Hagi.Dynamics (kl_contraction_budget
  capability_gain_transfer depth_capped_by_time)
export Hagi.Foundations (capability_takeoff_counted)

/-- ДИНАМИКА (сводка): (1) мультипликативный рост с
интенсивностями s t даёт C T ≥ C 0·(1+α)^{Σs}; (2)
KL-контракция с бюджетом: kl T ≤ δ при достаточном горизонте.
Рост и сжатие одновременно управляемы. -/
theorem dynamics_growth_and_distillation
    (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ)
    (kl : ℕ → ℝ) (κ_KL δ : ℝ)
    (hκ : 0 < κ_KL) (hκ1 : κ_KL < 1) (hδ : 0 < δ)
    (hstep : ∀ t, kl (t + 1) ≤ κ_KL * kl t)
    (hneed : kl 0 / δ ≤ (1 / κ_KL) ^ T) :
    C T ≥ C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t)
      ∧ kl T ≤ 0 + δ :=
  ⟨Hagi.Foundations.capability_takeoff_counted C s alpha halpha
      hmul T,
    Hagi.Dynamics.kl_contraction_budget kl κ_KL δ T hκ hκ1 hδ
      hstep hneed⟩

end Hagi.Unified
