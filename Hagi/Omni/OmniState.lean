/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Omni.CrossModalGap
import Hagi.Architecture.AlignedMerge
import Hagi.Architecture.CortexFiber
import Hagi.Optimization.Momentum

/-!
# Состояние омни-модальности (объединённое)

TemporalState (временная динамика), CapabilityMatrix
(матрица возможностей), SharedStateComposition (композиция
разделяемого состояния). Слит из трёх модулей; namespace
Hagi.Omni и имена деклараций сохранены.
-/

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
alias geom_sum_fin := _root_.Hagi.Optimization.geo_sum_eq

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

/-!
# CapabilityMatrix — group aggregation of the omni state

The pair-level cross-modal gap lifted to modality groups.
Results: `groupGap_nonneg` (the gap is nonnegative),
`groupGap_zero_iff_indep` (the gap is zero exactly at block
independence), and `admissionChain` (a chain of admissions each
gaining at least `deltaNet > 0` satisfies
`C 0 + t * deltaNet ≤ C t`).
-/

namespace Hagi.Omni

open Finset

/-! ### Group-level aggregation -/

/-- `0 ≤ crossModalGap p` for a positive joint law `p`
(delegation to `crossModalGap_nonneg`). -/
theorem groupGap_nonneg {X Y : Type} [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 < p z) (hsum : ∑ z, p z = 1) :
    0 ≤ crossModalGap p :=
  crossModalGap_nonneg p hp hsum

/-- `crossModalGap p = 0` iff `p` is the product of its
marginals. -/
theorem groupGap_zero_iff_indep {X Y : Type} [Fintype X]
    [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] (p : X × Y → ℝ) (hp : ∀ z, 0 < p z)
    (hsum : ∑ z, p z = 1) :
    crossModalGap p = 0
      ↔ ∀ x y, p (x, y) = margX p x * margY p y :=
  crossModalGap_zero_iff_indep p hp hsum

/-! ### The admission chain -/

/-- If `0 < deltaNet` and `C s + deltaNet ≤ C (s+1)` for all
`s < t`, then `C 0 + t * deltaNet ≤ C t`. -/
theorem admissionChain (t : ℕ) (C : ℕ → ℝ) (deltaNet : ℝ)
    (h0 : 0 < deltaNet)
    (hstep : ∀ s : ℕ, s < t → C s + deltaNet ≤ C (s + 1)) :
    C 0 + t * deltaNet ≤ C t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hlt : t < t + 1 := Nat.lt_succ_self t
    have h1 := hstep t hlt
    have h2 : C 0 + t * deltaNet ≤ C t := by
      refine ih ?_
      intro s hs
      exact hstep s (Nat.lt_of_lt_of_le hs (Nat.le_succ t))
    have h3 : C 0 + (t + 1) * deltaNet = (C 0 + t * deltaNet) + deltaNet := by
      ring
    push_cast
    linarith

end Hagi.Omni

/-!
# SharedStateComposition — energy and parameter cost of omni fusion

* `sharedStateEnergy`: for orthonormal leaves with `Uᵀ * V = 0`
  the composed-state energy is the exact sum of the leaf
  energies.
* `omniParamCost` / `sharedStateCostBound`: k rank-r leaves
  over a d-dim cortex cost `k·r·d` entries, below `d·d` when
  `k·r < d`.
* `sharedStatePerturbed`: the composed energy exceeds the
  Pythagorean sum by at most a term linear in the residual
  misalignment `frobSq (Vᵀ * W)`.
-/

namespace Hagi.Omni

open Matrix

/-! ### Exact composition at full alignment -/

/-- For orthonormal `U`, `V` with `Uᵀ * V = 0`:
`(U *ᵥ z + V *ᵥ w) ⬝ᵥ (U *ᵥ z + V *ᵥ w) = z ⬝ᵥ z + w ⬝ᵥ w`. -/
alias sharedStateEnergy := _root_.Hagi.Architecture.fiberPythagoras

/-! ### The parameter arithmetic of the omni state -/

/-- The entry count of a matrix. -/
def entryCount {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℕ := m * n

/-- **The leaf cost**: one rank-r modality leaf over a d-dim
cortex costs r·d entries. -/
theorem omniLeafCost {d r : ℕ} (V : Matrix (Fin d) (Fin r) ℝ) :
    entryCount V = r * d := by
  unfold entryCount
  exact Nat.mul_comm d r

/-- `∑ i : Fin k, r * d = k * (r * d)`. -/
theorem omniParamCost (k r d : ℕ) :
    ∑ i : Fin k, r * d = k * (r * d) := by
  rw [Finset.sum_const]
  simp

/-- If `0 < d` and `k * r < d` then the k-leaf parameter
count `k * (r * d)` is strictly below `d * d`. -/
theorem sharedStateCostBound (k r d : ℕ) (hd : 0 < d)
    (hkr : k * r < d) :
    ∑ i : Fin k, r * d < d * d := by
  rw [omniParamCost k r d]
  nlinarith [hkr, hd, Nat.succ_le_of_lt hd]

/-- For orthonormal `V`, `W`: the composed energy is at most
`r ⬝ᵥ r + s ⬝ᵥ s + 2 * √(frobSq (Vᵀ * W)) * ‖r‖ * ‖s‖`; at
`Vᵀ * W = 0` this is the equality of `sharedStateEnergy`. -/
alias sharedStatePerturbed := _root_.Hagi.Architecture.mergeEnergyPerturbed

end Hagi.Omni
