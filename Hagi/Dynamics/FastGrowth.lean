/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Dynamics.CapabilityGain
set_option linter.style.header false

/-!
# R83: fast growth — the compute-normalized capability law

- `capability_cumulative`: T certified cycles each
  transferring Γ ≥ c > 0 accumulate external gain ≥ T·c
  (capability_gain_transfer telescoped).
- `growth_efficiency_lower`: the mul-form — (R0 − RT)·K ≥
  T·c·K.
- `growth_efficiency_div`: the division form — every unit of
  compute (FLOP budget K per cycle) buys ≥ c/K of external
  risk reduction: the honest "fast" of the audit's program
  (ΔC/FLOPs ≥ c > 0).

The remaining audit fronts: ImplementationRefinement,
CertifiedEstimator (probability layer), DiscoveryProbability
(Borel–Cantelli side), RecursiveImprovement, Universality,
MasterHAGI.
-/

open Real Finset

namespace Hagi

/-- **Cumulative capability gain**: T certified cycles each
transferring Γ ≥ c > 0 accumulate external capability gain
≥ T·c (capability_gain_transfer telescoped) — the linear
growth law of the loop. -/
theorem capability_cumulative (Rext : ℕ → ℝ) (Gamma c : ℝ)
    (hc : 0 < c)
    (hstep : ∀ t, Rext (t + 1) ≤ Rext t - Gamma)
    (hG : c ≤ Gamma) (T : ℕ) :
    Rext T ≤ Rext 0 - ∑ _t ∈ Finset.range T, c := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hstep T
      rw [Finset.sum_range_succ]
      calc Rext (T + 1) ≤ Rext T - Gamma := h1
        _ ≤ (Rext 0 - ∑ _t ∈ Finset.range T, c) - Gamma := by linarith
        _ ≤ Rext 0 - (∑ _t ∈ Finset.range T, c + c) := by linarith

/-- **Compute-normalized growth efficiency (the honest
"fast")**: T cycles at cost ≤ K each, each transferring
Γ ≥ c, give risk-reduction-per-compute ≥ c/K — every unit
of compute buys at least c/K of external capability. -/
theorem growth_efficiency_lower (Rext : ℕ → ℝ) (Gamma c K : ℝ)
    (hc : 0 < c) (hK : 0 < K)
    (hstep : ∀ t, Rext (t + 1) ≤ Rext t - Gamma)
    (hG : c ≤ Gamma) (T : ℕ) (hT : T ≠ 0) :
    (Rext 0 - Rext T) * K ≥ (T:ℝ) * c * K := by
  have hcum := capability_cumulative Rext Gamma c hc hstep hG T
  have hsumT : ∑ _t ∈ Finset.range T, c = (T:ℝ) * c := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsumT] at hcum
  have hmul : (Rext 0 - Rext T) * K ≥ ((T:ℝ) * c) * K :=
    mul_le_mul_of_nonneg_right (by linarith) hK.le
  linarith

/-- In the division form: risk-reduction per unit compute
is at least c/K — every FLOP buys ≥ c/K of external risk
reduction (K > 0, T > 0). -/
theorem growth_efficiency_div (Rext : ℕ → ℝ) (Gamma c K : ℝ)
    (hc : 0 < c) (hK : 0 < K)
    (hstep : ∀ t, Rext (t + 1) ≤ Rext t - Gamma)
    (hG : c ≤ Gamma) (T : ℕ) (hT : (0:ℝ) < (T:ℝ)) :
    c / K ≤ (Rext 0 - Rext T) / ((T:ℝ) * K) := by
  have hTne : T ≠ 0 := by
    cases T with
    | zero => exact absurd hT (by simp)
    | succ n => exact fun h => Nat.succ_ne_zero n h
  have hmain := growth_efficiency_lower Rext Gamma c K hc hK hstep hG T hTne
  rw [div_le_div_iff₀ hK (mul_pos hT hK)]
  nlinarith [hmain, hK, hT]

end Hagi
