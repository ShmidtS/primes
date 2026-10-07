/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Omni.CrossModalGap

/-!
# CapabilityMatrix — the group-aggregation calculus of the omni state

The capability-matrix module: the omni theory lifted from
modality PAIRS to GROUPS of modalities. The shared state of an
omni model aggregates modalities; merging two modality groups
into one joint state obeys exactly the R190 pair law:

  G(X-block; Y-block) = H(X) + H(Y) − H(X,Y) = KL ≥ 0.

Main results:
* `groupGap_nonneg` (via `crossModalGap_nonneg`): merging two
  blocks of modalities never destroys information — the
  group-level subadditivity;
* `groupGap_zero_iff_indep`: the merged group is information-
  redundant exactly at block independence;
* `admissionChain`: a chain of t admissions, each with strictly
  positive group gap and covered cost, strictly grows the
  capability at EVERY step — the growing omni state never
  stalls: C_t ≥ C_0 + t·(net gain floor) under uniform floors.
-/

namespace Hagi.Omni

open Finset

/-! ### Group-level aggregation -/

/-- **Group-level subadditivity**: merging two blocks of
modalities (represented as finite types X and Y) into one
shared state never destroys information — R190 lifted to
groups. -/
theorem groupGap_nonneg {X Y : Type} [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 < p z) (hsum : ∑ z, p z = 1) :
    0 ≤ crossModalGap p :=
  crossModalGap_nonneg p hp hsum

/-- **Group-redundancy certificate**: the group gap vanishes
exactly at block independence. -/
theorem groupGap_zero_iff_indep {X Y : Type} [Fintype X]
    [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] (p : X × Y → ℝ) (hp : ∀ z, 0 < p z)
    (hsum : ∑ z, p z = 1) :
    crossModalGap p = 0
      ↔ ∀ x y, p (x, y) = margX p x * margY p y :=
  crossModalGap_zero_iff_indep p hp hsum

/-! ### The admission chain -/

/-- **The growing omni state never stalls**: a chain of t
admissions with per-step net gain at least deltaNet > 0
(each admission satisfies the R191 gate with cross-modal gain ≥
gmin and covered costs) grows capability at every step:
C_t ≥ C_0 + t·deltaNet. -/
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
