/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.GainOperator

/-!
# GainDecomposition — разложение GainOp на измеримые стадии

Разложение конверсии disagreement → capability на две стадии:
`η_policy = G_policy / E_dev`, `η_state = G_cap / G_policy`.

* `gain_chain`: если `G_policy = η_p * E_dev` и
  `G_cap = η_s * G_policy`, то `G_cap = (η_p * η_s) * E_dev`;
* `zero_stage_kills_gain`: при `0 ≤ E_dev` и тех же посылках,
  если одна из `η_p`, `η_s` ≤ 0, а другая ≥ 0, то `G_cap ≤ 0`;
* `chain_ignition_threshold`: порог зажигания в терминах
  произведения `η_p * η_s`: если он ≤ `(η_p * η_s) * devEnergy dev`,
  то он ≤ `η * devEnergy dev` для `η = η_p * η_s`.
-/

namespace Hagi

open Finset

variable {N : ℕ} {V : Type*} [NormedAddCommGroup V]

/-- Стадия 1: `etaPolicy E_dev G_policy = G_policy / E_dev`. -/
noncomputable def etaPolicy (E_dev G_policy : ℝ) : ℝ :=
  G_policy / E_dev

/-- Стадия 2: `etaState G_policy G_cap = G_cap / G_policy`. -/
noncomputable def etaState (G_policy G_cap : ℝ) : ℝ :=
  G_cap / G_policy

/-- Если `G_policy = η_p * E_dev` и `G_cap = η_s * G_policy`,
то `G_cap = (η_p * η_s) * E_dev`. -/
theorem gain_chain (E_dev G_policy G_cap η_p η_s : ℝ)
    (h1 : G_policy = η_p * E_dev)
    (h2 : G_cap = η_s * G_policy) :
    G_cap = (η_p * η_s) * E_dev := by
  rw [h1] at h2
  rw [h2]
  ring

/-- Если `0 ≤ E_dev`, `G_policy = η_p * E_dev`,
`G_cap = η_s * G_policy` и одна из `η_p`, `η_s` ≤ 0 при
другой ≥ 0, то `G_cap ≤ 0`. -/
theorem zero_stage_kills_gain (E_dev G_policy G_cap η_p η_s : ℝ)
    (hE : 0 ≤ E_dev)
    (h1 : G_policy = η_p * E_dev) (h2 : G_cap = η_s * G_policy)
    (hzero : (η_p ≤ 0 ∧ 0 ≤ η_s) ∨ (0 ≤ η_p ∧ η_s ≤ 0)) :
    G_cap ≤ 0 := by
  have hchain : G_cap = (η_p * η_s) * E_dev :=
    gain_chain E_dev G_policy G_cap η_p η_s h1 h2
  rcases hzero with ⟨hp, hs⟩ | ⟨hp, hs⟩
  · have hprod : η_p * η_s ≤ 0 := by nlinarith [hp, hs]
    have h2' : (η_p * η_s) * E_dev ≤ 0 * E_dev :=
      mul_le_mul_of_nonneg_right hprod hE
    simp at h2'
    linarith
  · have hprod : η_p * η_s ≤ 0 := by nlinarith [hp, hs]
    have h2' : (η_p * η_s) * E_dev ≤ 0 * E_dev :=
      mul_le_mul_of_nonneg_right hprod hE
    simp at h2'
    linarith

/-- Если `γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
≤ (η_p * η_s) * devEnergy dev`, то существует `η`
(а именно `η_p * η_s`) с тем же неравенством. -/
theorem chain_ignition_threshold (C D C' D' : ℝ)
    (γ ρ k ξ η_p η_s : ℝ) (dev : Fin N → V)
    (hstep : C' = C + γ * D)
    (hrhogk : γ * k ≤ ρ) (hcone : k * C ≤ D)
    (hprod : γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ (η_p * η_s) * devEnergy dev) :
    ∃ η, γ * k ^ 2 * C + (1 - ρ) * k * C + ξ
      ≤ η * devEnergy dev ∧ η = η_p * η_s :=
  ⟨η_p * η_s, hprod, rfl⟩

end Hagi
