/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.DisagreementChain

/-!
# ChainUnification — relating the two gain-pipeline vocabularies

* `training_core_is_measurement_tail`: if `s.G_cap` is expressed
  both via the measurement chain `disagreement_chain` and via the
  training factors `η_p * η_o * η_s * E_dev` with
  `E_dev = s.E_aligned`, `s.E_aligned ≠ 0`, and `s.α_align ≠ 0`,
  then `η_p * η_o * η_s = s.α_trunc * s.α_safe * s.α_cap`.
* `deficit_factorizes`: if all seven measured factors are nonzero,
  the ratio of the required product to the measured product equals
  the product of the per-stage ratios.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- If `s.G_cap = η_p * η_o * η_s * E_dev`, `E_dev = s.E_aligned`,
`s.E_aligned ≠ 0`, and `s.α_align ≠ 0`, then
`η_p * η_o * η_s = s.α_trunc * s.α_safe * s.α_cap`. -/
theorem training_core_is_measurement_tail (s : DisagreementStages)
    (η_p η_o η_s E_dev : ℝ)
    (hdev : E_dev = s.E_aligned)
    (hp : s.G_cap = η_p * η_o * η_s * E_dev)
    (hE : s.E_aligned ≠ 0)
    (ha : s.α_align ≠ 0) :
    η_p * η_o * η_s = s.α_trunc * s.α_safe * s.α_cap := by
  have hchain := disagreement_chain s
  have h1 : s.E_aligned = s.α_align * s.E_raw := s.h1
  -- substitute both G_cap expressions
  rw [hp, hdev, h1] at hchain
  -- hchain : ηηη · (αa · E_raw) = αa·αt·αs·αc · E_raw
  have hkey : (η_p * η_o * η_s) * (s.α_align * s.E_raw)
      = (s.α_trunc * s.α_safe * s.α_cap)
        * (s.α_align * s.E_raw) := by
    linarith [hchain]
  -- cancel the nonzero factor
  have hnz : s.α_align * s.E_raw ≠ 0 := by
    intro hcon
    apply hE
    rw [h1, hcon]
  exact mul_right_cancel₀ hnz hkey

/-- If all seven `m_*` factors are nonzero, the ratio of the
product of the `r_*` factors to the product of the `m_*`
factors equals the product of the per-stage ratios `r_i / m_i`. -/
theorem deficit_factorizes
    (r_align r_trunc r_safe r_cap r_p r_o r_s : ℝ)
    (m_align m_trunc m_safe m_cap m_p m_o m_s : ℝ)
    (hne : m_align ≠ 0 ∧ m_trunc ≠ 0 ∧ m_safe ≠ 0
      ∧ m_cap ≠ 0 ∧ m_p ≠ 0 ∧ m_o ≠ 0 ∧ m_s ≠ 0) :
    (r_align * r_trunc * r_safe * r_cap * r_p * r_o * r_s)
      / (m_align * m_trunc * m_safe * m_cap * m_p * m_o * m_s)
    = (r_align / m_align) * (r_trunc / m_trunc)
      * (r_safe / m_safe) * (r_cap / m_cap)
      * (r_p / m_p) * (r_o / m_o) * (r_s / m_s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hne
  field_simp

end Hagi.Growth
