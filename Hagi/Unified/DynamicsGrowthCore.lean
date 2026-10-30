import Mathlib
import Hagi.Dynamics.CapabilityGain
import Hagi.Dynamics.ControllerPolicy
import Hagi.Dynamics.DistillationRate
import Hagi.Dynamics.EndpointContraction
import Hagi.Dynamics.FastGrowth
import Hagi.Dynamics.ProxyGap
import Hagi.Dynamics.UrgencyDepth
import Hagi.Dynamics.WallClockTakeoff
import Hagi.Ensemble.Hoeffding
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
import Hagi.Omni.CapabilityMatrix
import Hagi.Omni.CrossModalGap
import Hagi.Omni.OmniInvariant
import Hagi.Omni.SharedStateComposition
import Mathlib.Tactic

/-!
# DynamicsGrowthCore — объединённый фасад слоёв-6
динамики и роста (слияние одно-теоремных фасадов
DynamicsLaws/GrowthLaws/GlobalDynamics, аудит v9 P3).
-/

namespace Hagi.Unified


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

/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
set_option linter.style.header false

/-!
# Global dynamics: idle behavior and the Fisher forgetting bound

* `safeqp_idle`: `dist 0 0 ≤ dist d 0` for every `d ∈ C` (the
  g₀ = 0 specialization of the SafeQP objective).
* `idle_merge_zero_gap`: at consensus logits the merge gap is
  exactly 0.
-/

open Real InnerProductSpace

namespace Hagi.Unified

/-- At a softmax distribution with all pairwise logit
deviations 0, `twoGap` is exactly 0. The compression stage's
idle behavior is not formalized here. -/

theorem idle_merge_zero_gap {k : Type} [Fintype k] [Nonempty k]
    (m : k → ℝ) (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1) :
    Hagi.twoGap (fun v => Real.exp (m v) / ∑ w, Real.exp (m w)) (fun _ => (0:ℝ)) = 0 :=
    (Hagi.twoGap_zero_iff hp hsum).mpr ⟨0, fun _ => rfl⟩

end Hagi.Unified


end Hagi.Unified
