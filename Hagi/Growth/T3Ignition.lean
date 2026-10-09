/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.ChainToCone

/-!
# T3Ignition — the T3 theorem: the measured chain IGNITES
the cone exactly when the effective conversion clears the
gate (R251; FORMALIZATION_PLAN §5.1)

T3 (the plan's top remaining open item): a condition on the
conversion chain of the form

  γ_eff ≥ γ_gate

formulated in the configuration vocabulary (R201/R214/R215)
with the R245/R247 disagreement→cone bridge as the frame.

**Vocabulary.** γ_eff is the EFFECTIVE conversion the
runtime certificate delivers: γ_eff := β⁴·κ (four measured
stage floors × the diversity-tracks-frontier share —
`chain_feeds_cone`). γ_gate is the IGNITION THRESHOLD:
STRICT positivity (γ_eff > 0 — a zero conversion never
grows) together with the cone's two UPPER bounds on the
rate (support γ·k ≤ ρ and curvature γ·k² + (1−ρ)k ≤ β_C
of `cone_two_sided_certificate`) — the feasible ignition
rates form (0, min(ρ/k, (β_C−(1−ρ)k)/k²)], the ignition
CEILING.

**Result.** `T3_ignition`: if the certificate clears the
gate (γ_eff ≥ γ_gate) AND the upper increment band uses the
same γ_eff (γ̄ = γ_eff, i.e. the runtime certifies the
conversion TIGHTLY — the two-sided band collapses to the
exact certified rate), then the cone ignites and takeoff
follows on the state trajectory. With `chain_ignition_
threshold`'s stage decomposition (R215) as the reading of
γ_eff's factors, and `deficit_factorizes` (R249) as the
locating tool, T3 closes the plan's §5.1 in the chain
vocabulary: the 9× question "why does the mixer not
ignite" becomes "which measured factor drops β⁴κ below
γ_gate" — a division, not a mystery.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- The ignition gate: the smallest γ satisfying both cone
conservation conditions (support and curvature), for k > 0.
When (1−ρ)·k ≤ β_C this is nonnegative. -/
noncomputable def ignitionGate (rho cbeta k : ℝ) : ℝ :=
  (cbeta - (1 - rho) * k) / k ^ 2

/-- The gate is nonnegative when the curvature budget
dominates the survival term. -/
theorem ignitionGate_nonneg (rho cbeta k : ℝ)
    (hk : 0 < k) (hdom : (1 - rho) * k ≤ cbeta) :
    0 ≤ ignitionGate rho cbeta k := by
  unfold ignitionGate
  apply div_nonneg _ (by positivity)
  linarith

/-- The ignition interval: the cone law demands BOTH upper
bounds on the certified rate γ (support γ·k ≤ ρ and
curvature γ·k² + (1−ρ)k ≤ β_C), while ignition demands
γ > 0 strictly (a zero conversion never grows). The
feasible ignition rates form the interval
(0, min(ρ/k, (β_C − (1−ρ)k)/k²)] — nonempty iff
(1−ρ)k < β_C. -/
noncomputable def ignitionCeiling (rho cbeta k : ℝ) : ℝ :=
    min (rho / k) ((cbeta - (1 - rho) * k) / k ^ 2)

theorem ignitionCeiling_pos (rho cbeta k : ℝ)
    (hk : 0 < k) (hrho : 0 < rho)
    (hdom : (1 - rho) * k < cbeta) :
    0 < ignitionCeiling rho cbeta k := by
  unfold ignitionCeiling
  have h1 : 0 < rho / k := div_pos hrho hk
  have h2 : 0 < (cbeta - (1 - rho) * k) / k ^ 2 := by
    apply div_pos _ (by positivity)
    nlinarith
  exact lt_min_iff.mpr ⟨h1, h2⟩

/-- **THE T3 THEOREM (γ_eff ≥ γ_gate ⟹ ignition)**: the
plan's §5.1 item, closed in the chain vocabulary. γ_gate is
the ignition threshold — STRICT positivity of the effective
conversion (γ_eff = β⁴κ, the runtime certificate's rate);
γ_eff must additionally sit UNDER the ignition ceiling (the
cone's support and curvature bounds — R247's two-sided
honesty). Under both, the cone ignites and takeoff follows
on the state trajectory at the MEASURED rate β⁴κ·k.

Reading with R215 (`chain_ignition_threshold`) and R249
(`deficit_factorizes`): the 9× question "why does the mixer
not ignite" factors into (a) γ_eff = 0 — some measured α is
zero (division locates which), or (b) γ_eff above the
ceiling — the realized increments outrun the frontier's
replenishment (the R247 overshoot warning). -/
theorem T3_ignition
    (C D G : ℕ → ℝ) (stages : ℕ → DisagreementStages)
    (T : ℕ) (beta kappa rho cbeta k : ℝ)
    (hβ : 0 < beta) (hκ : 0 < kappa) (hk : 0 < k)
    (hceiling : beta^4 * kappa ≤ ignitionCeiling rho cbeta k)
    -- runtime certificates (R247 vocabulary)
    (hD : ∀ t ∈ Finset.range (T + 1), 0 ≤ D t)
    (hC : ∀ t ∈ Finset.range (T + 1), 0 ≤ C t)
    (hcert : ∀ t ∈ Finset.range T, beta ≤ (stages t).α_align
      ∧ beta ≤ (stages t).α_trunc
      ∧ beta ≤ (stages t).α_safe ∧ beta ≤ (stages t).α_cap)
    (hdiv : ∀ t ∈ Finset.range T,
      kappa * D t ≤ (stages t).E_raw)
    (hstep : ∀ t ∈ Finset.range T,
      C (t + 1) = C t + G t)
    (hG : ∀ t ∈ Finset.range T,
      (stages t).G_cap = G t)
    (hup : ∀ t ∈ Finset.range T, G t ≤ (beta^4 * kappa) * D t)
    (hdyn : ∀ t ∈ Finset.range T,
      rho * D t + cbeta * C t ≤ D (t + 1))
    (hcone0 : k * C 0 ≤ D 0) :
    C 0 * (1 + (beta^4 * kappa) * k) ^ T ≤ C T := by
  -- unpack the ceiling into the two cone conditions
  have hγpos : 0 < beta^4 * kappa := by positivity
  unfold ignitionCeiling at hceiling
  have hsupport : (beta^4 * kappa) * k ≤ rho := by
    have := le_trans hceiling (min_le_left _ _)
    have h1 : beta^4 * kappa ≤ rho / k := this
    have hk0 : (k:ℝ) ≠ 0 := ne_of_gt hk
    have h2 : beta^4 * kappa * k ≤ rho / k * k :=
      mul_le_mul_of_nonneg_right h1 hk.le
    rwa [div_mul_eq_mul_div, mul_div_cancel_right₀ _ hk0] at h2
  have hcurv : (beta^4 * kappa) * k ^ 2 + (1 - rho) * k ≤ cbeta := by
    have h1 := le_trans hceiling (min_le_right _ _)
    have hk2 : (0:ℝ) < k ^ 2 := by positivity
    have hk20 : ((k:ℝ)) ^ 2 ≠ 0 := ne_of_gt hk2
    have h3 : beta^4 * kappa ≤ (cbeta - (1 - rho) * k) / k ^ 2 := h1
    have h4 : beta^4 * kappa * k ^ 2
        ≤ (cbeta - (1 - rho) * k) / k ^ 2 * k ^ 2 :=
      mul_le_mul_of_nonneg_right h3 hk2.le
    rw [div_mul_eq_mul_div, mul_div_cancel_right₀ _ hk20] at h4
    linarith
  -- apply the R247 cone bridge with the tight band
  exact takeoff_from_certificate C D G stages T
    beta kappa (beta^4 * kappa) rho cbeta k
    hβ.le hκ.le hk.le hD hC hcert hdiv hstep hG hup hdyn
    hsupport hcurv hcone0



end Hagi.Growth
