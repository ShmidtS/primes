/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Omni.CrossModalGap

/-!
# Omni capability growth

The one-step capability update `omniStep C gIntra gCross cComp
cRisk = C + gIntra + gCross - cComp - cRisk` with admission
gates: nonnegative net gain preserves capability, strict net
gain strictly increases it, and a strictly dependent modality
pair (non-product joint law) with nonnegative intra gain and
costs bounded by the gains strictly grows capability.
-/

namespace Hagi.Omni

/-- The one-step omni capability update:
C + intra-modal gain + cross-modal gain − compression cost −
risk cost. -/
def omniStep (C gIntra gCross cComp cRisk : ℝ) : ℝ :=
  C + gIntra + gCross - cComp - cRisk

/-- If `cComp + cRisk ≤ gIntra + gCross` then
`C ≤ omniStep C gIntra gCross cComp cRisk`. -/
theorem omniGrowth_admits (C gIntra gCross cComp cRisk : ℝ)
    (hnet : cComp + cRisk ≤ gIntra + gCross) :
    C ≤ omniStep C gIntra gCross cComp cRisk := by
  unfold omniStep
  linarith

/-- If `cComp + cRisk < gIntra + gCross` then
`C < omniStep C gIntra gCross cComp cRisk`. -/
theorem omniGrowth_positive (C gIntra gCross cComp cRisk : ℝ)
    (hnet : cComp + cRisk < gIntra + gCross) :
    C < omniStep C gIntra gCross cComp cRisk := by
  unfold omniStep
  linarith

/-- If the joint law `p` is not a product of its marginals
(so `crossModalGap p > 0` by `crossModalGap_zero_iff_indep`),
`0 ≤ gIntra`, and `cComp + cRisk ≤ gIntra`, then
`C < omniStep C gIntra (crossModalGap p) cComp cRisk`. -/
theorem omniGate_crossModal {X Y : Type} [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 < p z) (hsum : ∑ z, p z = 1)
    (C gIntra cComp cRisk : ℝ)
    (hgIntra : 0 ≤ gIntra)
    (hdep : ¬ ∀ x y, p (x, y) = margX p x * margY p y)
    (hcost : cComp + cRisk ≤ gIntra) :
    C < omniStep C gIntra (crossModalGap p) cComp cRisk := by
  -- strict dependence ⟹ strictly positive gap
  have hpos : 0 < crossModalGap p := by
    by_contra hle
    have h0 : crossModalGap p = 0 := by
      have := crossModalGap_nonneg p hp hsum
      linarith [this, hle]
    exact hdep ((crossModalGap_zero_iff_indep p hp hsum).mp h0)
  exact omniGrowth_positive C gIntra (crossModalGap p) cComp cRisk
    (by linarith)

end Hagi.Omni
