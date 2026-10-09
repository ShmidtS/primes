/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Omni.OmniSafeStep

/-!
# OmniInvariant — Φ-monotonicity of the omni cycle

The potential `omniPhi risk cap = risk - cap`. Results: the
potential is nonincreasing (`omniPhi_step`) / strictly
decreasing (`omniPhi_strict`) across an admitted-modality cycle
when the risk increment `eps` is covered by the net capability
gain; `omniInvariant_preserved` combines this with strict
capability growth and a nonnegative remaining budget.
-/

namespace Hagi.Omni

/-! ### The omni potential -/

/-- The omni potential: Φ_omni = risk − capability (lower is
better; growth of capability pushes Φ down, risk pushes it up;
the capability cost of the cycle is paid inside omniStep, the
budget account is tracked separately). -/
def omniPhi (risk cap : ℝ) : ℝ := risk - cap

/-- If `p` is not the product of its marginals then
`0 < crossModalGap p`. -/
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

/-- If `p` is dependent and
`eps ≤ gIntra + crossModalGap p - cComp - cRisk`, then
`omniPhi (risk + eps) (omniStep cap gIntra (crossModalGap p) cComp cRisk) ≤ omniPhi risk cap`. -/
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

/-- As `omniPhi_step` with strict coverage
`eps < gIntra + crossModalGap p - cComp - cRisk`: the potential
strictly decreases. -/
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

/-- Under the stated hypotheses (dependent `p`, nonnegative
`gIntra`, covered costs, covered `eps`, nonnegative remaining
budget): Φ is nonincreasing, capability strictly grows, the
coverage bound holds, and the budget remainder is nonnegative. -/
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
