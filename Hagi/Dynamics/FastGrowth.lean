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

/-- **The multiplicative capability law (the audit's
exponential takeoff core, deterministic half)**: if every
SUCCESSFUL event multiplies capability by ≥ (1+α) with
α > 0 (and failures never decrease it), then after T cycles
of which N are successful,

  C_T ≥ C_0 · (1 + α)^N

— exponential growth in the number of successes. With the
probability layer (success probability ≥ p per cycle,
h_util Σp = ∞), N ~ Binomial(T, p) makes log C_T = Ω(T) —
the true fast-growth form of the audit's Master theorem.
The deterministic core is here; the stochastic half stays
open. -/
theorem capability_multiplicative (C : ℕ → ℝ) (succ : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha) (hC0 : 0 ≤ C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha))
    (T : ℕ) :
    C T ≥ C 0 * (1 + alpha) ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hmul T
      have hbase : (1 + alpha) ^ (T + 1) = (1 + alpha) ^ T * (1 + alpha) := by
        rw [pow_succ]
      rw [hbase]
      calc C (T + 1) ≥ C T * (1 + alpha) := h1
        _ ≥ (C 0 * (1 + alpha) ^ T) * (1 + alpha) := by
            refine mul_le_mul_of_nonneg_right ih ?_
            linarith
        _ = C 0 * ((1 + alpha) ^ T * (1 + alpha)) := by ring

/-- **The counted takeoff law (the audit's fast-growth
Master theorem, deterministic core complete)**: each cycle
t multiplies capability by ≥ (1+α)^(s_t) where s_t is the
success indicator (1 = certified success, 0 = no harm).
Then

  C_T ≥ C_0 · (1+α)^(Σ_t s_t)

— exponential in the SUCCESS COUNT. With the probability
layer (P(s_t = 1) ≥ p, the DiscoveryProbability front),
Σs_t ~ pT gives log C_T = Ω(T): exponential takeoff.
Failures are neutral (s_t = 0 multiplies by 1) — safety and
growth in one law. -/
theorem capability_takeoff_counted (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T : ℕ) :
    C T ≥ C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 := hmul T
      have hsum : ∑ t ∈ Finset.range (T + 1), s t
          = (∑ t ∈ Finset.range T, s t) + s T :=
        Finset.sum_range_succ s T
      have hpow : (1 + alpha) ^ ((∑ t ∈ Finset.range T, s t) + s T)
          = (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) * (1 + alpha) ^ (s T) :=
        pow_add _ _ _
      rw [hsum, hpow]
      have hpowpos : (0:ℝ) < (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) := by
        positivity
      calc C (T + 1) ≥ C T * (1 + alpha) ^ (s T) := h1
        _ ≥ (C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t)) * (1 + alpha) ^ (s T) := by
            refine mul_le_mul_of_nonneg_right ih ?_
            positivity
        _ = C 0 * ((1 + alpha) ^ (∑ t ∈ Finset.range T, s t) * (1 + alpha) ^ (s T)) := by
            ring

/-- **Takeoff under a success-count floor (the bridge to the
probability layer)**: if the success count over T cycles is
at least N (h_emp_ — e.g. from DiscoveryProbability:
P(s_t=1) ≥ p concentrated to N ≥ ⌊pT⌋), the counted law
gives C_T ≥ C_0·(1+α)^N — exponential takeoff conditional
on the measured discovery rate. -/
theorem capability_takeoff_floor (C : ℕ → ℝ) (s : ℕ → ℕ)
    (alpha : ℝ) (halpha : 0 < alpha) (hC0 : 0 ≤ C 0)
    (hmul : ∀ t, C (t + 1) ≥ C t * (1 + alpha) ^ (s t))
    (T N : ℕ)
    (hcount : N ≤ ∑ t ∈ Finset.range T, s t) :
    C T ≥ C 0 * (1 + alpha) ^ N := by
  have hlaw := capability_takeoff_counted C s alpha halpha hmul T
  have hmono : (1 + alpha) ^ N ≤ (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) :=
    pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1 + alpha) hcount
  have hmul2 : C 0 * (1 + alpha) ^ N ≤ C 0 * (1 + alpha) ^ (∑ t ∈ Finset.range T, s t) :=
    mul_le_mul_of_nonneg_left hmono hC0
  linarith

end Hagi
