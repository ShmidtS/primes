/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# GrowthDynamics — the single bundle of growth-premises

One structure collecting the 8-premise bundle consumed by the
cone/takeoff family. The empirical nature of each field is
visible in its name (`emp*`): conditional results carry their
conditionality in the signature.

* `hα hγ hρ` — sign hypotheses on the rates;
* `hC0` — the seed capability is positive;
* `empCone0` — the initial cone condition `(α/γ)·C₀ ≤ D₀`;
* `empStep` — the capability update law `C_{t+1} = C_t + G_t`;
* `empGainProd` — production `γ·D_t ≤ G_t`;
* `empDyn` — the D-dynamics with loss ξ: `ρ·D + β·C − ξ ≤ D′`;
* `empCCap` — the multiplicative capability cap;
* `empBeta` — the cone-sustaining β bound.
-/

namespace Hagi.Foundations

/-- The growth-dynamics premise bundle: one object instead of
eight positional hypotheses. All `emp*` fields are empirical
laws, not derived facts. -/
structure GrowthDynamics (C G D : ℕ → ℝ) (xi : ℕ → ℝ)
    (alpha gamma rho beta : ℝ) (T : ℕ) : Prop where
  /-- the growth rate is positive -/
  hα : 0 < alpha
  /-- production efficiency is positive -/
  hγ : 0 < gamma
  /-- the retention coefficient is nonnegative -/
  hρ : 0 ≤ rho
  /-- the seed capability is positive -/
  hC0 : 0 < C 0
  /-- EMPIRICAL: the initial cone condition -/
  empCone0 : alpha / gamma * C 0 ≤ D 0
  /-- EMPIRICAL: the capability update law -/
  empStep : ∀ t < T, C (t + 1) = C t + G t
  /-- EMPIRICAL: gain production from disagreement -/
  empGainProd : ∀ t < T, gamma * D t ≤ G t
  /-- EMPIRICAL: disagreement dynamics with loss xi -/
  empDyn : ∀ t < T, rho * D t + beta * C t - xi t ≤ D (t + 1)
  /-- EMPIRICAL: multiplicative capability cap -/
  empCCap : ∀ t < T, C (t + 1) ≤ (1 + alpha) * C t
  /-- EMPIRICAL: the cone-sustaining beta bound -/
  empBeta : ∀ t < T,
    alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta

end Hagi.Foundations
