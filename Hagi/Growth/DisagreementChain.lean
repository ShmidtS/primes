/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.OptimizerStage

/-!
# DisagreementChain — the conversion pipeline as a product law

The pipeline `E_raw → E_aligned → E_kept → G_safe → G_cap` is
formalized as a multiplicative composition of conversion factors:

* `disagreement_chain`: `G_cap` equals the product of the four
  stage factors times `E_raw`;
* `deficit_localizes`: if the product of the four factors is below
  `ρ = β^4` (with `0 ≤ β`), then at least one factor is below `β`;
* `alignment_factor_le_one`: if `α_align ≤ 1` and `0 ≤ E_raw`, then
  `E_aligned ≤ E_raw`.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- The five observable stages of the disagreement pipeline,
each with its own conversion factor. -/
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

/-- For any `s : DisagreementStages`,
`s.G_cap = s.α_align * s.α_trunc * s.α_safe * s.α_cap * s.E_raw`. -/
theorem disagreement_chain (s : DisagreementStages) :
    s.G_cap = s.α_align * s.α_trunc * s.α_safe * s.α_cap * s.E_raw := by
  have hA : s.E_aligned = s.α_align * s.E_raw := s.h1
  have hB : s.E_kept = s.α_trunc * s.α_align * s.E_raw := by
    rw [s.h2, hA]; ring
  have hC : s.G_safe = s.α_safe * s.α_trunc * s.α_align * s.E_raw := by
    rw [s.h3, hB]; ring
  rw [s.h4, hC]
  ring

/-- If `0 ≤ ρ`, `0 ≤ β`, `β^4 = ρ`, and the product of the
four stage factors is `< ρ`, then at least one factor is
strictly below `β`. -/
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

/-- If `s.α_align ≤ 1` and `0 ≤ s.E_raw`, then
`s.E_aligned ≤ s.E_raw`. -/
theorem alignment_factor_le_one (s : DisagreementStages)
    (hα : s.α_align ≤ 1) (hE : 0 ≤ s.E_raw) :
    s.E_aligned ≤ s.E_raw := by
  rw [s.h1]
  nlinarith [hα, hE]

end Hagi.Growth
