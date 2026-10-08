/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.LatentAlign
import Hagi.Growth.OptimizerStage

/-!
# DisagreementChain — the 9× diagnostic pipeline (R245)

The measured mixer.gain ≈ 0.002 against the required
≈ 0.018 (a 9× deficit) is not one bug but a CHAIN of
conversions, each individually measurable:

  E_raw → (latent-align) → E_aligned → (spectral trunc)
  → E_kept → (SafeQP) → G_safe → (capability) → G_cap

This module formalizes the chain as a multiplicative
composition of conversion factors (matching the gain chain
of `OptimizerStage`), plus the alignment step's key
property:

* `disagreement_chain` — the full product law: each stage
  contributes a factor, the deficit factors EXACTLY —
  if the product of stage factors equals γ_req/γ_meas,
  no single stage needs to be the whole story;
* `deficit_localizes` — if the total conversion is below
  the required threshold, AT LEAST ONE stage factor is
  below its required share (pigeonhole on the product) —
  the formal license to measure the chain stage-by-stage
  instead of guessing;
* `alignment_factor_le_one` — alignment compresses the
  MEASURED latent disagreement (the flip share of
  R242 is exactly the difference between raw and aligned
  readings); the raw reading overestimates the loss the
  merge will actually suffer.

Empirical anchors (flagged): E_raw etc. are measured on
real expert matrices; γ_meas ≈ 0.002, γ_req ≈ 0.018 are
scale-specific observations, NOT constants of nature.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- The five observable stages of the disagreement
pipeline, each with its own conversion factor. -/
structure DisagreementStages where
  E_raw : ℝ
  E_aligned : ℝ
  E_kept : ℝ
  G_safe : ℝ
  G_cap : ℝ
  α_align : ℝ
  α_trunc : ℝ
  α_safe : ℝ
  α_cap : ℝ
  h1 : E_aligned = α_align * E_raw
  h2 : E_kept = α_trunc * E_aligned
  h3 : G_safe = α_safe * E_kept
  h4 : G_cap = α_cap * G_safe

/-- **The full product law**: the capability gain factors
into the four measurable stage conversions times the raw
disagreement energy — the diagnostic chain is exact, no
hidden slack. -/
theorem disagreement_chain (s : DisagreementStages) :
    s.G_cap = s.α_align * s.α_trunc * s.α_safe * s.α_cap * s.E_raw := by
  have hA : s.E_aligned = s.α_align * s.E_raw := s.h1
  have hB : s.E_kept = s.α_trunc * s.α_align * s.E_raw := by
    rw [s.h2, hA]; ring
  have hC : s.G_safe = s.α_safe * s.α_trunc * s.α_align * s.E_raw := by
    rw [s.h3, hB]; ring
  rw [s.h4, hC]
  ring

/-- **Deficit localization**: if the total conversion
product is below the required threshold ρ, then at least
one stage factor is below the FOURTH ROOT of ρ (if every
factor were ≥ ρ^{1/4}, the product would be ≥ ρ) — the
pigeonhole license to measure stages individually: SOME
stage is below its geometric share, no need to audit all
four exhaustively before finding a culprit. -/
theorem deficit_localizes (s : DisagreementStages)
    {ρ β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hβ4 : β^4 = ρ)
    (hdef : s.α_align * s.α_trunc * s.α_safe * s.α_cap < ρ) :
    s.α_align < β ∨ s.α_trunc < β ∨ s.α_safe < β ∨ s.α_cap < β := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have h4' : 0 ≤ s.α_cap := by linarith
  have h2' : 0 ≤ s.α_trunc := by linarith
  have h3' : 0 ≤ s.α_safe := by linarith
  have h1' : 0 ≤ s.α_align := by linarith
  have hbb : 0 ≤ β * β := mul_nonneg hβ hβ
  have h12 : 0 ≤ s.α_align * s.α_trunc := mul_nonneg h1' h2'
  have h34 : 0 ≤ s.α_safe * s.α_cap := mul_nonneg h3' h4'
  have m1 : β * β ≤ s.α_align * s.α_trunc := mul_le_mul h1 h2 hβ h1'
  have m2 : β * β ≤ s.α_safe * s.α_cap := mul_le_mul h3 h4 hβ h3'
  have m3 : (β * β) * (β * β)
      ≤ (s.α_align * s.α_trunc) * (s.α_safe * s.α_cap) :=
    mul_le_mul m1 m2 hbb h12
  have hprod : β^4 ≤ s.α_align * s.α_trunc * s.α_safe * s.α_cap := by
    nlinarith [m3]
  rw [hβ4] at hprod
  exact absurd hdef (not_lt.mpr hprod)

/-- **Alignment compresses the measured disagreement**: the
aligned reading never exceeds the raw one when the
alignment factor is at most one (flipped columns are
excluded from the loss the merge will suffer). The raw
reading OVERESTIMATES the merge-induced destruction by
exactly the flip share — measuring E_aligned is the first
diagnostic of the chain. -/
theorem alignment_factor_le_one (s : DisagreementStages)
    (hα : s.α_align ≤ 1) (hE : 0 ≤ s.E_raw) :
    s.E_aligned ≤ s.E_raw := by
  rw [s.h1]
  nlinarith [hα, hE]

end Hagi.Growth
