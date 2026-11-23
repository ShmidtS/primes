/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hagi.System.GrowthState
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
set_option linter.style.header false

/-!
# DerivedState — energy/effects as FUNCTIONS of weights (A18.6)

Answer to audit W1 (addendum A18): in the abstract `GrowthState` the
fields `weights`/`energy`/`effects` are independent and coupled only
through the h_emp_ premises of the stage theorems. This module adds the
CONSTRUCTIVE counterpart: `derivedGrowthState` — a `GrowthState` whose
`energy` and ALL effect fields are COMPUTED from the weights and a fixed
finite dataset (`FixedDataset`, a `Fintype` carrier):

* `energyOf ds θ := ∑ i, (⟪a i, θ⟫ − y i)² / 2` — the loss on the fixed
  dataset as a pure function of the weights;
* `gradOf` / `smoothL` — the matching gradient and smoothness constant;
* `derivedEffects ds η θ` — every `StageEffects` channel a function of
  (weights, dataset); the joint channel computes the real gradient step
  `θ − η • ∇`;
* `derived_emp_grow` / `derived_emp_smooth` / `derived_potential_joint`
  — the h_emp_ premises of `potential_grow` / `potential_joint` are
  DERIVED (discharged) for the derived state; the flagship
  `derived_potential_joint` needs no empirical premise at all: the
  potential decrease `η‖∇‖²/2` holds BY CONSTRUCTION under `η ≤ 1/L`.

The coherence invariant (`coherentGrowth`, weights = projection of
params) holds for `derivedGrowthState` by construction (`weights := θ`,
`params := θ`); the genuine C386-symbol tie lives in the layer-5 bridge
`Hagi/Semantics/DerivedStateCoherence.lean` (System layer 3 may not
import Semantics — LayerLint).

## Honest pins

* `energyOf` is the least-squares loss on the fixed dataset, NOT the
  token-KL CE of the abstract energy: the CE smoothness machinery lives
  at Model layer 4, unreachable from this System-layer module; the
  measured energy field of the abstract `GrowthState` stays for the
  general case (freeze identity, back-compat). The derived variant is
  the canonical COMPUTED representative (cf. `GrowthComputed.growthQuad`,
  the pure-ε representative of cycle 35).
* The derived grow/merge/compress stages do not move weights, so their
  gain/risk/cost effect channels are honest zeros and their energy
  channels equal `energyOf ds θ`; only the joint stage computes a real
  parameter step.
* Capability/verifier/gap channels remain abstract zeros — out of scope.
-/

open Finset Real InnerProductSpace

namespace Hagi.System.DerivedState

variable {d : ℕ} {I : Type} [Fintype I]

/-! ### The fixed finite dataset and the computed energy -/

/-- The fixed dataset: a finite `Fintype` carrier of feature vectors
`a i` with regression targets `y i`. The dataset is DATA, not state —
the energy is a function of the weights alone. -/
structure FixedDataset (I : Type) [Fintype I] (d : ℕ) where
  /-- Feature vector of sample `i`. -/
  a : I → EuclideanSpace ℝ (Fin d)
  /-- Regression target of sample `i`. -/
  y : I → ℝ

/-- The computed energy: the least-squares loss of the weights `θ` on
the fixed dataset — `energy θ := lossOn fixedData θ`. -/
noncomputable def energyOf (ds : FixedDataset I d)
    (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, (⟪ds.a i, θ⟫_ℝ - ds.y i) ^ 2 / 2

/-- The computed gradient of `energyOf` (exact for the quadratic
loss — no measurement involved). -/
noncomputable def gradOf (ds : FixedDataset I d)
    (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ i, (⟪ds.a i, θ⟫_ℝ - ds.y i) • ds.a i

/-- The smoothness constant of `energyOf`: `L = ∑ i, ‖a i‖²`. -/
noncomputable def smoothL (ds : FixedDataset I d) : ℝ :=
  ∑ i, ‖ds.a i‖ ^ 2

/-! ### The real math: quadratic identity and Cauchy–Schwarz smoothness -/

/-- The gradient pairing is the residual-feature sum (linear algebra
over the `Finset` sum). -/
theorem gradOf_inner (ds : FixedDataset I d)
    (θ δ : EuclideanSpace ℝ (Fin d)) :
    ⟪gradOf ds θ, δ⟫_ℝ
      = ∑ i, (⟪ds.a i, θ⟫_ℝ - ds.y i) * ⟪ds.a i, δ⟫_ℝ := by
  rw [gradOf, real_inner_comm, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [inner_smul_right, real_inner_comm]

/-- Cauchy–Schwarz in squared form. -/
theorem inner_sq_le (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, y⟫_ℝ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have h := abs_real_inner_le_norm x y
  have habs : (0:ℝ) ≤ |⟪x, y⟫_ℝ| := abs_nonneg _
  calc ⟪x, y⟫_ℝ ^ 2 = |⟪x, y⟫_ℝ| ^ 2 := (sq_abs _).symm
    _ ≤ (‖x‖ * ‖y‖) ^ 2 := by
        rw [sq, sq]; exact mul_self_le_mul_self habs h
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by ring

/-- The EXACT second-order expansion of the computed energy: no
inequality, no measurement — the residual algebra of the fixed
dataset. -/
theorem energyOf_quad_ident (ds : FixedDataset I d)
    (θ δ : EuclideanSpace ℝ (Fin d)) :
    energyOf ds (θ + δ)
      = energyOf ds θ + ⟪gradOf ds θ, δ⟫_ℝ
        + ∑ i, ⟪ds.a i, δ⟫_ℝ ^ 2 / 2 := by
  have hper : ∀ i : I, (⟪ds.a i, θ + δ⟫_ℝ - ds.y i) ^ 2 / 2
      = (⟪ds.a i, θ⟫_ℝ - ds.y i) ^ 2 / 2
        + (⟪ds.a i, θ⟫_ℝ - ds.y i) * ⟪ds.a i, δ⟫_ℝ
        + ⟪ds.a i, δ⟫_ℝ ^ 2 / 2 := by
    intro i
    rw [inner_add_right]
    ring
  have hg := gradOf_inner ds θ δ
  simp only [energyOf]
  rw [Finset.sum_congr rfl (fun i _ => hper i), hg]
  simp only [Finset.sum_add_distrib]

/-- The smoothness bound of the computed energy: the exact expansion is
bounded by `L/2 · ‖δ‖²` via per-term Cauchy–Schwarz — the DERIVED
counterpart of the smoothness premise class of `potential_joint`. -/
theorem energyOf_smooth_le (ds : FixedDataset I d)
    (θ δ : EuclideanSpace ℝ (Fin d)) :
    energyOf ds (θ + δ)
      ≤ energyOf ds θ + ⟪gradOf ds θ, δ⟫_ℝ
        + smoothL ds / 2 * ‖δ‖ ^ 2 := by
  have hident := energyOf_quad_ident ds θ δ
  have hcs : ∀ i : I, ⟪ds.a i, δ⟫_ℝ ^ 2 / 2
      ≤ ‖ds.a i‖ ^ 2 * ‖δ‖ ^ 2 / 2 := fun i => by
    have := inner_sq_le (ds.a i) δ
    linarith
  have hsum : ∑ i, ⟪ds.a i, δ⟫_ℝ ^ 2 / 2
      ≤ ∑ i, ‖ds.a i‖ ^ 2 * ‖δ‖ ^ 2 / 2 :=
    Finset.sum_le_sum (fun i _ => hcs i)
  have hsplit : ∑ i, ‖ds.a i‖ ^ 2 * ‖δ‖ ^ 2 / 2
      = smoothL ds / 2 * ‖δ‖ ^ 2 := by
    have hre : ∀ i : I, ‖ds.a i‖ ^ 2 * ‖δ‖ ^ 2 / 2
        = (‖δ‖ ^ 2 / 2) * ‖ds.a i‖ ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hre i), ← Finset.mul_sum, smoothL]
    ring
  rw [hsplit] at hsum
  linarith

/-! ### The derived growth state: energy and effects COMPUTED -/

/-- The derived effect record: every `StageEffects` channel a FUNCTION of
(weights, dataset). The grow/merge/compress stages do not move weights,
so their energy channels equal `energyOf ds θ` and their gain/risk/cost
channels are honest zeros; the joint channel computes the real gradient
step `θ − η • gradOf ds θ`. -/
noncomputable def derivedEffects (ds : FixedDataset I d) (η : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) : StageEffects where
  growGain := 0
  growCost := 0
  growRisk := 0
  growEnergy := energyOf ds θ
  mergeEnergy := energyOf ds θ
  mergeRisk := 0
  mergeCost := 0
  jointEnergy := energyOf ds (θ - η • gradOf ds θ)
  jointRisk := 0
  jointCost := 0
  quantErr := 0
  compressEnergy := energyOf ds θ
  compressRisk := 0
  compressCost := 0

/-- The derived growth state: `energy := energyOf ds θ` (computed, not
measured), `weights := θ`, `params := θ` (coherent by construction —
the invariant needs no repair theorem here), `grad = stepDir :=
gradOf ds θ`, smoothness `L := smoothL ds`, and the WHOLE effects record
computed. -/
noncomputable def derivedGrowthState (ds : FixedDataset I d) (η : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    GrowthState (EuclideanSpace ℝ (Fin d)) where
  weightDim := d
  weights := (θ : Fin d → ℝ)
  params := θ
  experts := 0
  energy := energyOf ds θ
  protectedRisk := 0
  budget := 1
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := gradOf ds θ
  grad := gradOf ds θ
  sp := { eta := η, L := smoothL ds, kappa := 0, s := 0 }
  effects := derivedEffects ds η θ

/-- The computed-energy channel: the state's energy field IS the loss of
its weights on the fixed dataset (the defining property of the derived
state, stated on the record). -/
theorem derived_energy_channel (ds : FixedDataset I d) (η : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    (derivedGrowthState ds η θ).energy = energyOf ds θ := by
  simp [derivedGrowthState]

/-- The weights/params coherence, construction level: the compressed
weights are the coordinate view of the parameters — the abstract state's
missing invariant (audit W1 /) holds for the derived state BY
CONSTRUCTION. -/
theorem derived_coe (ds : FixedDataset I d) (η : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (derivedGrowthState ds η θ).weights i
      = ((derivedGrowthState ds η θ).params : Fin d → ℝ) i := by
  simp [derivedGrowthState]

/-! ### The h_emp_ premises, DISCHARGED for the derived state -/

/-- The grow-stage h_emp_ premise of `potential_grow` DERIVED: in the
derived state the
grow stage does not move weights, so the grow-energy premise holds with
equality (gain zero) — an empirical premise becomes a theorem of the
construction. -/
theorem derived_emp_grow (ds : FixedDataset I d) (η : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    (derivedGrowthState ds η θ).effects.growEnergy
      ≤ (derivedGrowthState ds η θ).energy
        - gainGrow (derivedGrowthState ds η θ) := by
  simp [derivedEffects, derivedGrowthState, gainGrow]

/-- The joint-stage smoothness h_emp_ premise of `potential_joint`
DERIVED: the joint channel
`energyOf (θ − η • ∇)` satisfies the smoothness premise with the
computed constant `smoothL ds` — Cauchy–Schwarz mathematics, not a
measurement. -/
theorem derived_emp_smooth (ds : FixedDataset I d) (η : ℝ)
    (hη : 0 ≤ η) (θ : EuclideanSpace ℝ (Fin d)) :
    (derivedGrowthState ds η θ).effects.jointEnergy
      ≤ (derivedGrowthState ds η θ).energy
        - η * ⟪gradOf ds θ, gradOf ds θ⟫_ℝ
        + smoothL ds * η ^ 2 * ‖gradOf ds θ‖ ^ 2 / 2 := by
  have hsm := energyOf_smooth_le ds θ (-(η • gradOf ds θ))
  have h1 : ⟪gradOf ds θ, η • gradOf ds θ⟫_ℝ
      = η * ⟪gradOf ds θ, gradOf ds θ⟫_ℝ := by rw [inner_smul_right]
  have h2 : ‖η • gradOf ds θ‖ ^ 2 = η ^ 2 * ‖gradOf ds θ‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    ring
  have h3 : ⟪gradOf ds θ, -(η • gradOf ds θ)⟫_ℝ
      = -(η * ⟪gradOf ds θ, gradOf ds θ⟫_ℝ) := by
    rw [inner_neg_right, inner_smul_right]
  have h4 : ‖-(η • gradOf ds θ)‖ ^ 2 = η ^ 2 * ‖gradOf ds θ‖ ^ 2 := by
    rw [norm_neg]; exact h2
  simp only [derivedEffects, derivedGrowthState, sub_eq_add_neg] at hsm ⊢
  rw [h3, h4] at hsm
  linarith

/-- **The flagship**: NO empirical premise survives. For the derived
state with `η ≤ 1/L` (and any fixed dataset with `L > 0`), the
potential `Φ = energy + protectedRisk` decreases by at least
`η · ‖∇‖² / 2` under the joint step — every premise of
`potential_joint` (descent condition by the exact gradient pairing,
smoothness by Cauchy–Schwarz) is DISCHARGED by the construction. -/
theorem derived_potential_joint (ds : FixedDataset I d) (η : ℝ)
    (hη0 : 0 ≤ η) (hL : 0 < smoothL ds) (heta : η ≤ 1 / smoothL ds)
    (θ : EuclideanSpace ℝ (Fin d)) :
    potential (joint (derivedGrowthState ds η θ))
      - potential (derivedGrowthState ds η θ)
        ≤ -(η * ‖gradOf ds θ‖ ^ 2 / 2) := by
  have hd : ‖(derivedGrowthState ds η θ).stepDir‖ ^ 2
      ≤ ⟪(derivedGrowthState ds η θ).grad,
          (derivedGrowthState ds η θ).stepDir⟫_ℝ := by
    simp only [derivedGrowthState]
    rw [real_inner_self_eq_norm_sq]
  have hmain := potential_joint (derivedGrowthState ds η θ) hL heta hη0 hd
    (derived_emp_smooth ds η hη0 θ)
  have hgj : gainJoint (derivedGrowthState ds η θ)
      = η * ‖gradOf ds θ‖ ^ 2 / 2 := by
    simp [gainJoint, derivedGrowthState]
  have hrj : riskJoint (derivedGrowthState ds η θ) = 0 := by
    simp [riskJoint, derivedEffects, derivedGrowthState]
  have hp : potential (joint (derivedGrowthState ds η θ))
      = energyOf ds (θ - η • gradOf ds θ) := by
    simp [potential, joint, derivedGrowthState, derivedEffects]
  have hps : potential (derivedGrowthState ds η θ) = energyOf ds θ := by
    simp [potential, derivedGrowthState]
  rw [hp, hps, hgj, hrj] at hmain
  rw [hp, hps]
  linarith

end Hagi.System.DerivedState
