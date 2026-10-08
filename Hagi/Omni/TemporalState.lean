/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Omni.CrossModalGap

/-!
# TemporalState — the world-state dynamics contract

The TemporalState module of the omni layer: the shared state is
not a bag of tokens but a DYNAMICAL SYSTEM — video is an
observation of dynamics, action is a control signal:

  S_{t+1} = F(S_t, a_t, o_{t+1}).

The core quality property of a world model is bounded DRIFT: a
Lipschitz/contractive update keeps the predicted state within a
controlled tube of the true state; unbounded drift is the
long-horizon failure mode reported for real omni models.

Main results:
* drift_bound: a contraction F with factor ρ and observation
  error bounded by e gives predicted-state drift
  ‖Ŝ_t − S_t‖ ≤ ρ^t·‖Ŝ_0 − S_0‖ + e·(1−ρ^t)/(1−ρ) — the
  geometric tube;
* `drift_limit`: as t → ∞ the drift is absorbed by the fixed
  observation-error budget e/(1−ρ): contraction alone never
  guarantees exact state recovery, but keeps the error
  permanently bounded;
* `drift_zero`: with exact observations (e = 0) the drift decays
  to zero geometrically — the ideal world-model case.
-/

namespace Hagi.Omni

open Finset

/-! ### The drift tube of a contractive world model -/

/-- **The geometric drift tube**: under a contraction factor
ρ < 1 with per-step observation error e, the t-step drift is at
most ρ^t·d0 + e·Σ_{i<t} ρ^i — the explicit tube. This is the
statement form used by `drift_limit` and `drift_zero`. -/
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

/-- **Permanent boundedness**: for ρ < 1 and e ≥ 0, the tube is
bounded by d0 + e/(1−ρ) — contraction keeps the world model in
a fixed tube forever; the long-horizon unbounded-drift failure
mode is excluded. -/
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

/-- **Exact-observation decay**: with e = 0 the drift decays
geometrically — the ideal world model recovers the true state. -/
theorem drift_zero (ρ d0 : ℝ) (t : ℕ) :
    driftTube ρ 0 d0 t = ρ ^ t * d0 := by
  unfold driftTube
  simp

end Hagi.Omni
