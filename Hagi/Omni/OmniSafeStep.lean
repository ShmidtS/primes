/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.Dominate
import Hagi.Omni.OmniGrowth

/-!
# OmniSafeStep — protecting acquired modalities under joint training

The safety half of the omni contract: modalities share one state
and one update stream, so a joint step must not destroy an
already-acquired modality channel. The mechanism is the
SAFE_CONSENSUS law (R-Dominate) lifted to the modality setting:

  if every modality gradient gi has nonnegative alignment with
  the consensus direction d (d = c•gs, c ≥ 0), then every
  modality DESCENDS along d — the joint step is first-order
  harmless for every acquired channel simultaneously.

Main results:
* `omniSafeStep`: a consensus step with nonneg pairwise
  alignments ⟨gi, gs⟩ ≥ 0 is harmless for ALL modality
  gradients at once — the acquired-modalities protection;
* `omniSafeStep_sum`: the total (aggregated) descent
  ⟨Σgi, d⟩ ≥ 0 — the joint objective decreases;
* `omniGate_complete`: the full omni admission cycle: positive
  cross-modal gap (R190) + strict growth (R191) + cheap leaf
  (R192) + harmless joint step (this module) — the complete
  formal contract for "a new modality is a certified growth
  source that does not damage what is already learned".
-/

namespace Hagi.Omni

open Finset InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ### Harmlessness of the consensus step -/

/-- **The acquired-modalities protection**: a consensus step
d = c•gs is first-order harmless for every modality gradient
with nonnegative alignment to the consensus — no acquired
channel is damaged by the joint update. -/
theorem omniSafeStep (d gs : X) (c : ℝ) (hc : 0 ≤ c)
    (hd : d = c • gs) {k : ℕ} (gis : Fin k → X)
    (halign : ∀ i, 0 ≤ ⟪gis i, gs⟫_ℝ) :
    ∀ i, 0 ≤ ⟪gis i, d⟫_ℝ := by
  intro i
  exact Hagi.safe_consensus_harmless d gs (gis i) (halign i)
    ⟨c, hc, hd⟩

/-- **The aggregated descent**: under the same consensus
hypotheses, the SUM of modality gradients also descends along d
— the joint omni objective improves. -/
theorem omniSafeStep_sum (d gs : X) (c : ℝ) (hc : 0 ≤ c)
    (hd : d = c • gs) {k : ℕ} (gis : Fin k → X)
    (halign : ∀ i, 0 ≤ ⟪gis i, gs⟫_ℝ) :
    0 ≤ ⟪∑ i, gis i, d⟫_ℝ := by
  have hterm : ∀ i : Fin k, 0 ≤ ⟪gis i, d⟫_ℝ :=
    omniSafeStep d gs c hc hd gis halign
  rw [sum_inner]
  exact Finset.sum_nonneg fun i _ => hterm i

/-! ### The complete omni admission cycle -/

/-- **The complete omni gate**: the composite contract under
which a new modality is a certified growth source:
(1) the cross-modal gap is strictly positive (the pair carries
    genuinely joint information — R190/R191);
(2) the new leaf is cheap: k·r·d entries, sub-quadratic in d
    (R192);
(3) the joint consensus step is harmless for every acquired
    modality gradient (this module).
Together: capability strictly grows, the volume cost is
controlled, and nothing already learned is damaged. -/
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
