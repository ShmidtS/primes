/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.Dominate
import Hagi.Omni.OmniGrowth

/-!
# OmniSafeStep — protecting acquired modalities under joint training

If every modality gradient `gi` has nonnegative alignment with
the consensus direction `gs` and `d = c • gs` with `c ≥ 0`, then
every modality descends along `d` (`omniSafeStep`) and so does
their sum (`omniSafeStep_sum`); `omniGate_complete` combines
this with the strict capability growth of `omniGate_crossModal`.
-/

namespace Hagi.Omni

open Finset InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ### Harmlessness of the consensus step -/

/-- If `d = c • gs` with `c ≥ 0` and `0 ≤ ⟪gis i, gs⟫` for
every `i`, then `0 ≤ ⟪gis i, d⟫` for every `i`. -/
theorem omniSafeStep (d gs : X) (c : ℝ) (hc : 0 ≤ c)
    (hd : d = c • gs) {k : ℕ} (gis : Fin k → X)
    (halign : ∀ i, 0 ≤ ⟪gis i, gs⟫_ℝ) :
    ∀ i, 0 ≤ ⟪gis i, d⟫_ℝ := by
  intro i
  exact Hagi.safe_consensus_harmless d gs (gis i) (halign i)
    ⟨c, hc, hd⟩

/-- Under the hypotheses of `omniSafeStep`:
`0 ≤ ⟪∑ i, gis i, d⟫`. -/
theorem omniSafeStep_sum (d gs : X) (c : ℝ) (hc : 0 ≤ c)
    (hd : d = c • gs) {k : ℕ} (gis : Fin k → X)
    (halign : ∀ i, 0 ≤ ⟪gis i, gs⟫_ℝ) :
    0 ≤ ⟪∑ i, gis i, d⟫_ℝ := by
  have hterm : ∀ i : Fin k, 0 ≤ ⟪gis i, d⟫_ℝ :=
    omniSafeStep d gs c hc hd gis halign
  rw [sum_inner]
  exact Finset.sum_nonneg fun i _ => hterm i

/-! ### The complete omni admission cycle -/

/-- Combines `omniGate_crossModal` with `omniSafeStep` and
`omniSafeStep_sum`: under a dependent `p`, nonnegative
`gIntra`, costs covered by `gIntra`, and nonnegative alignments
with the consensus, capability strictly grows and every modality
gradient (and their sum) has nonnegative alignment with `d`. -/
theorem omniGate_complete {X' : Type*} [NormedAddCommGroup X']
    [InnerProductSpace ℝ X']
    (d gs : X') (c : ℝ) (hc : 0 ≤ c) {k : ℕ} (gis : Fin k → X')
    (halign : ∀ i, 0 ≤ ⟪gis i, gs⟫_ℝ) (hd : d = c • gs)
    {Y1 Y2 : Type} [Fintype Y1] [DecidableEq Y1] [Nonempty Y1]
    [Fintype Y2] [DecidableEq Y2] [Nonempty Y2]
    (p : Y1 × Y2 → ℝ) (hp : ∀ z, 0 < p z) (hsum : ∑ z, p z = 1)
    (C gIntra cComp cRisk : ℝ) (hgIntra : 0 ≤ gIntra)
    (hdep : ¬ ∀ x y, p (x, y) = margX p x * margY p y)
    (hcost : cComp + cRisk ≤ gIntra) :
    C < omniStep C gIntra (crossModalGap p) cComp cRisk
      ∧ (∀ i, 0 ≤ ⟪gis i, d⟫_ℝ)
      ∧ 0 ≤ ⟪∑ i, gis i, d⟫_ℝ := by
  refine ⟨omniGate_crossModal p hp hsum C gIntra cComp cRisk
      hgIntra hdep hcost, ?_, ?_⟩
  · exact omniSafeStep d gs c hc hd gis halign
  · exact omniSafeStep_sum d gs c hc hd gis halign

end Hagi.Omni
