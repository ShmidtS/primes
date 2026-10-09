/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Omni.CrossModalGap

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
