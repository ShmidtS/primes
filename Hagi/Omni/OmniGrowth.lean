/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Omni.CrossModalGap

/-!
# OmniGrowth — the omni capability growth law

The growth-law composition of the omni-HAGI cycle: a new
capability (e.g. a new modality) is admitted when its gains
exceed its costs:

  C_{t+1} = C_t + G_intra + G_cross − C_compress − C_risk.

Main results:
* `omniGrowth_admits`: if the net gain is nonnegative
  (G_intra + G_cross ≥ compression cost + risk cost), capability
  does not decrease;
* `omniGrowth_positive`: if the inequality is strict, capability
  strictly increases — the omni gate for admitting a modality;
* `omniGate_crossModal`: combining with CrossModalGap — a strictly
  dependent modality pair (G_cross > 0) with positive intra gain
  and bounded costs strictly grows capability: the formal version
  of "a new modality is a legitimate growth source exactly when it
  brings genuinely joint information".
-/

namespace Hagi.Omni

/-- The one-step omni capability update:
C + intra-modal gain + cross-modal gain − compression cost −
risk cost. -/
def omniStep (C gIntra gCross cComp cRisk : ℝ) : ℝ :=
  C + gIntra + gCross - cComp - cRisk

/-- **The admission gate (non-strict)**: net gain nonnegative
⟹ capability does not decrease. -/
theorem omniGrowth_admits (C gIntra gCross cComp cRisk : ℝ)
    (hnet : cComp + cRisk ≤ gIntra + gCross) :
    C ≤ omniStep C gIntra gCross cComp cRisk := by
  unfold omniStep
  linarith

/-- **The admission gate (strict)**: net gain positive ⟹
capability strictly increases — the gate through which a new
modality (or any capability source) enters the omni state. -/
theorem omniGrowth_positive (C gIntra gCross cComp cRisk : ℝ)
    (hnet : cComp + cRisk < gIntra + gCross) :
    C < omniStep C gIntra gCross cComp cRisk := by
  unfold omniStep
  linarith

/-- **The cross-modal admission theorem**: if the new modality
pair carries strictly positive cross-modal information
(G_cross > 0, certified e.g. by crossModalGap_nonneg being
strict — see crossModalGap_zero_iff_indep for the degenerate
case), the intra-modal gain is nonnegative, and the costs are
bounded by the gains, then capability strictly grows. -/
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
