/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Omni.CrossModalGap

/-!
# TemporalState — the world-state drift tube

The drift tube `driftTube ρ e d0 t = ρ^t·d0 + e·Σ_{i<t} ρ^i`
for a contractive world model with contraction factor `ρ` and
per-step observation error `e`. Results: the closed form
(`driftTube_closed`), the uniform bound
`driftTube ≤ d0 + e/(1−ρ)` for `0 ≤ ρ < 1` (`drift_limit`), and
geometric decay to zero at `e = 0` (`drift_zero`).
-/

namespace Hagi.Omni

open Finset

/-! ### The drift tube of a contractive world model -/

/-- The tube value `ρ^t * d0 + e * Σ_{i<t} ρ^i`. -/
def driftTube (ρ e d0 : ℝ) (t : ℕ) : ℝ :=
  ρ ^ t * d0 + e * ∑ i ∈ Finset.range t, ρ ^ i

/-- The finite geometric sum: Σ_{i<t} ρ^i = (1−ρ^t)/(1−ρ) for
ρ ≠ 1. -/
theorem geom_sum_fin (ρ : ℝ) (hρ1 : ρ ≠ 1) (t : ℕ) :
    ∑ i ∈ Finset.range t, ρ ^ i = (1 - ρ ^ t) / (1 - ρ) := by
  have h := geom_sum_eq hρ1 t
  rw [h]
  field_simp
  ring

/-- **The closed-form drift tube**: the tube of driftTube is
ρ^t·d0 + e·(1−ρ^t)/(1−ρ). -/
theorem driftTube_closed (ρ e d0 : ℝ) (hρ1 : ρ ≠ 1) (t : ℕ) :
    driftTube ρ e d0 t = ρ ^ t * d0 + e * (1 - ρ ^ t) / (1 - ρ) := by
  unfold driftTube
  rw [geom_sum_fin ρ hρ1 t]
  ring

/-- For `0 ≤ ρ < 1`, `e ≥ 0`, `d0 ≥ 0` and any `t`:
`driftTube ρ e d0 t ≤ d0 + e / (1 - ρ)`. -/
theorem drift_limit (ρ e d0 : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (he : 0 ≤ e) (hd0 : 0 ≤ d0) (t : ℕ) :
    driftTube ρ e d0 t ≤ d0 + e / (1 - ρ) := by
  rw [driftTube_closed ρ e d0 (ne_of_lt hρ1) t]
  have h1 : 0 < 1 - ρ := by linarith
  have hρt : 0 ≤ ρ ^ t := pow_nonneg hρ0 t
  have hge : ρ ^ t ≤ 1 := pow_le_one₀ hρ0 (le_of_lt hρ1)
  have hB : e * (1 - ρ ^ t) / (1 - ρ) ≤ e * 1 / (1 - ρ) :=
    (div_le_div_iff_of_pos_right h1).mpr (by nlinarith [hge, he])
  have hA : ρ ^ t * d0 ≤ 1 * d0 := mul_le_mul_of_nonneg_right hge hd0
  have hR : e * 1 / (1 - ρ) = e / (1 - ρ) := by ring
  nlinarith [hA, hB]

/-- `driftTube ρ 0 d0 t = ρ ^ t * d0`. -/
theorem drift_zero (ρ d0 : ℝ) (t : ℕ) :
    driftTube ρ 0 d0 t = ρ ^ t * d0 := by
  unfold driftTube
  simp

end Hagi.Omni
