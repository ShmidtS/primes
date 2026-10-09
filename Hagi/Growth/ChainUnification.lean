/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.DisagreementChain

/-!
# ChainUnification — one gain pipeline, two vocabularies
(R249; the unification refactor)

The repository carried TWO parallel formalizations of the
same multiplicative-conversion idea:

* `OptimizerStage` (R239): G_cap = η_policy·η_opt·η_state·E_dev
  — the TRAINING-side chain (what the optimizer does to the
  disagreement);
* `DisagreementStages` (R245): G_cap = α_align·α_trunc·
  α_safe·α_cap·E_raw — the MEASUREMENT-side chain (what the
  pipeline stages do to it).

They are not rivals: the measurement chain OPERATES the
object the training chain describes. This module pins the
composite:

* `training_core_is_measurement_tail` — the tail
coincidence: with E_dev = E_aligned ≠ 0 the training core
η_p·η_o·η_s EQUALS the measurement tail α_trunc·α_safe·
α_cap (the two chains constrain each other; a naive
seven-factor composition is FALSE and was caught during
proving);
* `deficit_factorizes` — THE 9× ARITHMETIC: the observed
deficit ratio γ_req/γ_meas equals the product of the seven
stage-factor ratios (required over measured) — a violated
requirement factors EXACTLY across the pipeline, so the
runtime can locate the bottleneck by division, stage by
stage.
-/

open scoped BigOperators

namespace Hagi.Growth

/-- **The two vocabularies coincide on the tail**: if the
optimizer-side chain (η) and the measurement-side chain (α)
describe the SAME system with E_dev = E_aligned (the
optimizer sees the ALIGNED disagreement — R242 alignment
runs before routing), then the training core IS the tail of
the measurement chain:

  η_p·η_o·η_s = α_trunc·α_safe·α_cap

(provided the aligned disagreement is nonzero, so the
equality is not vacuous). The two formalizations are one
pipeline: alignment is measurement-only, and the
spectral-truncation/SafeQP/capability factors ARE the
policy/optimizer/state conversions seen from the lab bench. -/
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

/-- **The 9× deficit factors exactly across the pipeline**:
if the required total conversion is γ_req and the measured
one is γ_meas (both as products of stage factors), then
the deficit ratio is the product of per-stage required/
measured ratios — locating the bottleneck is DIVISION,
stage by stage. -/
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
