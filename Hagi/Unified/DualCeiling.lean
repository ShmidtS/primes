/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.GrowthDynamics

/-!
# DualCeiling — двойной потолок термостата (R559)

Объединение двух ограничительных каналов: полоса-потолок
(R556) и γ-бюджет-потолок (R530-гейт). Capability ограничен
минимумом двух потолков.
-/

open scoped BigOperators

namespace Hagi.Unified

/-- **Двойной потолок (R559)**: при затухающей полосе прироста
и γ-гейте (α·C t ≤ G t ≤ γ·D̄) capability ограничен обоими
потолками сразу: C T ≤ C 0 + b/σ (полоса, R556) и
C T ≤ γ·D̄/α (γ-бюджет через гейт). -/
theorem dual_ceiling (C G D : ℕ → ℝ) (b σ Dbar alpha gamma : ℝ)
    (T : ℕ)
    (hstep : ∀ t, C (t + 1) = C t + G t)
    (hband : ∀ t, G t ≤ b * (1 - σ) ^ t)
    (hb : 0 ≤ b) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hgate : ∀ t, alpha * C t ≤ G t)
    (hgain : ∀ t, G t ≤ gamma * Dbar)
    (hα : 0 < alpha) :
    C T ≤ C 0 + b / σ ∧ C T ≤ gamma * Dbar / alpha := by
  classical
  obtain ⟨_, hceil⟩ := Hagi.Foundations.geometric_band_ceiling
    C G b σ T hstep hband hb hσ hσ1
  refine ⟨hceil, ?_⟩
  have hgateT : C T * alpha ≤ gamma * Dbar := by
    have h1 : alpha * C T ≤ G T := hgate T
    have h2 : G T ≤ gamma * Dbar := hgain T
    have h3 : alpha * C T ≤ gamma * Dbar := le_trans h1 h2
    rw [mul_comm] at h3
    exact h3
  exact (le_div_iff₀ hα).mpr hgateT

end Hagi.Unified
