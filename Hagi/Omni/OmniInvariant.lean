/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Omni.OmniSafeStep

/-!
# OmniInvariant — the Φ-monotonicity of the omni cycle

The invariant module of the omni layer: the composite omni
cycle (admit a modality → merge into the shared state → train
jointly under the consensus guard) preserves the HAGI
invariant's core conjuncts. The potential view: Φ_omni = risk −
capability (lower is better). The capability cost of the cycle
(cComp + cRisk) is paid INSIDE omniStep; the risk increment
(eps, the SafeQP budget of the joint step) is covered by the
intra-modal gain.

Main results:
* `omniPhi_step`: Φ_omni is nonincreasing across an
  admitted-modality cycle when the SafeQP risk budget eps is
  covered by the intra gain (eps ≤ gIntra + G_cross − costs);
* `omniPhi_strict`: Φ strictly decreases when the coverage is
  strict — permanent progress;
* `omniInvariant_preserved`: the composite certificate — Φ
  nonincreasing, capability strictly growing, risk bounded by
  the SafeQP budget, budget nonnegative.
-/

namespace Hagi.Omni

/-! ### The omni potential -/

/-- The omni potential: Φ_omni = risk − capability (lower is
better; growth of capability pushes Φ down, risk pushes it up;
the capability cost of the cycle is paid inside omniStep, the
budget account is tracked separately). -/
def omniPhi (risk cap : ℝ) : ℝ := risk - cap

/-- Strict positivity of the cross-modal gap of a strictly
dependent pair (the R190 certificate, packaged). -/
theorem crossModalGap_pos_of_dep {Y1 Y2 : Type} [Fintype Y1]
    [DecidableEq Y1] [Nonempty Y1] [Fintype Y2] [DecidableEq Y2]
    [Nonempty Y2] (p : Y1 × Y2 → ℝ) (hp : ∀ z, 0 < p z)
    (hsum : ∑ z, p z = 1)
    (hdep : ¬ ∀ x y, p (x, y) = margX p x * margY p y) :
    0 < crossModalGap p := by
  by_contra hle
  have h0 : crossModalGap p = 0 := by
    have := crossModalGap_nonneg p hp hsum
    linarith [this, hle]
  exact hdep ((crossModalGap_zero_iff_indep p hp hsum).mp h0)

/-- **Φ-monotonicity across an admitted modality**: if the
SafeQP risk budget eps of the joint step is covered by the NET
capability gain (gIntra + G_cross − costs), the omni potential
does not increase across the cycle. -/
theorem omniPhi_step {Y1 Y2 : Type} [Fintype Y1] [DecidableEq Y1]
    [Nonempty Y1] [Fintype Y2] [DecidableEq Y2] [Nonempty Y2]
    (p : Y1 × Y2 → ℝ) (hp : ∀ z, 0 < p z) (hsum : ∑ z, p z = 1)
    (risk cap gIntra cComp cRisk eps : ℝ)
    (hdep : ¬ ∀ x y, p (x, y) = margX p x * margY p y)
    (hcover : eps ≤ gIntra + crossModalGap p - cComp - cRisk) :
    omniPhi (risk + eps)
        (omniStep cap gIntra (crossModalGap p) cComp cRisk)
      ≤ omniPhi risk cap := by
  have hpos := crossModalGap_pos_of_dep p hp hsum hdep
  unfold omniPhi omniStep
  linarith

/-- **Strict Φ-decrease**: strict coverage strictly lowers the
omni potential — permanent progress of the omni cycle. -/
theorem omniPhi_strict {Y1 Y2 : Type} [Fintype Y1] [DecidableEq Y1]
    [Nonempty Y1] [Fintype Y2] [DecidableEq Y2] [Nonempty Y2]
    (p : Y1 × Y2 → ℝ) (hp : ∀ z, 0 < p z) (hsum : ∑ z, p z = 1)
    (risk cap gIntra cComp cRisk eps : ℝ)
    (hdep : ¬ ∀ x y, p (x, y) = margX p x * margY p y)
    (hcover : eps < gIntra + crossModalGap p - cComp - cRisk) :
    omniPhi (risk + eps)
        (omniStep cap gIntra (crossModalGap p) cComp cRisk)
      < omniPhi risk cap := by
  have hpos := crossModalGap_pos_of_dep p hp hsum hdep
  unfold omniPhi omniStep
  linarith

/-- **The composite omni invariant**: across a full
admitted-modality cycle — strict cross-modal gain (R190),
strict capability growth (R191), the risk increment bounded by
the SafeQP budget with coverage (R194 + this module), and the
budget staying nonnegative — the omni invariant holds:
Φ nonincreasing, capability strictly growing, risk bounded,
budget nonnegative. -/
theorem omniInvariant_preserved {Y1 Y2 : Type} [Fintype Y1]
    [DecidableEq Y1] [Nonempty Y1] [Fintype Y2] [DecidableEq Y2]
    [Nonempty Y2] (p : Y1 × Y2 → ℝ) (hp : ∀ z, 0 < p z)
    (hsum : ∑ z, p z = 1)
    (risk cap budget gIntra cComp cRisk eps : ℝ)
    (hgIntra : 0 ≤ gIntra)
    (hdep : ¬ ∀ x y, p (x, y) = margX p x * margY p y)
    (hcost : cComp + cRisk ≤ gIntra)
    (hcover : eps ≤ gIntra + crossModalGap p - cComp - cRisk)
    (hbudget : 0 ≤ budget - (cComp + cRisk)) :
    omniPhi (risk + eps)
        (omniStep cap gIntra (crossModalGap p) cComp cRisk)
      ≤ omniPhi risk cap
      ∧ cap < omniStep cap gIntra (crossModalGap p) cComp cRisk
      ∧ eps ≤ gIntra + crossModalGap p - cComp - cRisk
      ∧ 0 ≤ budget - (cComp + cRisk) := by
  refine ⟨omniPhi_step p hp hsum risk cap gIntra cComp cRisk eps
      hdep hcover, ?_, ?_, hbudget⟩
  · exact omniGate_crossModal p hp hsum cap gIntra cComp cRisk
      hgIntra hdep hcost
  · exact hcover

end Hagi.Omni
