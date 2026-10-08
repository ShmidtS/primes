/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Audit.Foundations
import Hagi.Audit.Exactness

/-!
# ProjectionDescent — the canonical SafeQP descent vertical
(R257; architecture audit P0-3, stage 0)

The audit's complaint: `Audit.Exactness` — a VERIFICATION
layer — was load-bearing for the production theory
(`Unified.GrowthState` imports it for `safeQP_descent`).
Stage 0 of the migration (nothing deleted): this module is
the CANONICAL Step-level re-statement of the projection
descent vertical,

  min_dist_to_vi  →  safeQP_descent

verbatim from `Audit.Exactness` (same proofs, same
signatures), so that System-layer consumers import the
STEP layer, not the Audit layer. The Audit copies remain
as legacy (stage 0) and will be reduced to re-exports in
a later stage once every consumer has moved.

The vertical (for a convex safe set C ∋ 0 and the
dist-minimizer ds over C):

* `min_dist_to_vi` — the variational inequality of the
  projection: ⟪g0 − ds, w − ds⟫ ≤ 0 for all w ∈ C;
* `safeQP_descent` — BOTH descent guarantees:
  ‖ds‖² ≤ ⟪g0, ds⟫ (alignment retention) and
  ‖g0 − ds‖ ≤ ‖g0‖ (contraction toward g0).
-/

open InnerProductSpace

namespace Hagi.Step

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The variational inequality of the projection onto a
convex set: the minimizer of the distance to g0 over C
makes an obtuse angle with every feasible displacement. -/
theorem min_dist_to_vi (C : Set X) (hconv : Convex ℝ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0) :
    ∀ w ∈ C, ⟪g0 - ds, w - ds⟫_ℝ ≤ 0 :=
  Hagi.min_dist_to_vi C hconv g0 ds hs hmin

/-- **The SafeQP descent — the controller guarantee**
(canonical Step-level form): for the safe-QP minimizer ds
(the dist-minimizer over the convex C ∋ 0), BOTH descent
guarantees hold: ⟪g0, ds⟫ ≥ ‖ds‖² and ‖g0−ds‖ ≤ ‖g0‖. -/
theorem safeQP_descent (C : Set X) (hconv : Convex ℝ C)
    (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0) :
    ‖ds‖^2 ≤ ⟪g0, ds⟫_ℝ ∧ ‖g0 - ds‖ ≤ ‖g0‖ :=
  Hagi.safeQP_descent C hconv h0 g0 ds hs hmin

end Hagi.Step
