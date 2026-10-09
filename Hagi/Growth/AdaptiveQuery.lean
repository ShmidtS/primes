/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.SelfDevelopment

/-!
# AdaptiveQuery — averaged selection radius

Given a per-query error bound `e`, `avgRadius e K = e / √K` is the
radius used when K queries per candidate are averaged.

Main results:

* `avgRadius_shrinks`: if `0 ≤ e` and `0 < K ≤ L`, then
  `avgRadius e L ≤ avgRadius e K` and `avgRadius e 1 = e`;
* `certified_gain_select_avg`: if every estimate deviates from the
  true gain by at most `avgRadius e K` and some safe candidate `a₀`
  has gain above `3 * avgRadius e K`, then some safe candidate has
  positive gain within `2 * avgRadius e K` of `g a₀`.
-/

namespace Hagi.Growth

open Finset

/-- The averaged-estimator radius: e/√K for K queries. -/
noncomputable def avgRadius (e : ℝ) (K : ℕ) : ℝ := e / Real.sqrt K

/-- The radius function is nonincreasing in `K` over positive
integers and `avgRadius e 1 = e` (given `0 ≤ e`). -/
theorem avgRadius_shrinks (e : ℝ) (he : 0 ≤ e) (K L : ℕ)
    (hK : 0 < K) (hKL : K ≤ L) :
    avgRadius e L ≤ avgRadius e K ∧
      avgRadius e 1 = e := by
  constructor
  · unfold avgRadius
    have hs : (Real.sqrt K : ℝ) ≤ Real.sqrt L :=
      Real.sqrt_le_sqrt (by exact_mod_cast hKL)
    exact div_le_div_of_nonneg_left he (Real.sqrt_pos.mpr (by exact_mod_cast hK)) hs
  · unfold avgRadius
    norm_num

/-- Averaged certified selection: assuming every estimate
`Ghat a` deviates from `g a` by at most `avgRadius e K`, if the
safe candidate `a₀` has `3 * avgRadius e K < g a₀`, then some
safe candidate `a'` satisfies `0 < g a'` and
`g a₀ - 2 * avgRadius e K ≤ g a'`. -/
theorem certified_gain_select_avg {A : Type} [Fintype A] [Nonempty A]
    (g Ghat : A → ℝ) (safe : A → Prop) [DecidablePred safe]
    (e : ℝ) (he : 0 ≤ e) (K : ℕ) (hK : 0 < K)
    (hconc : ∀ a, |Ghat a - g a| ≤ avgRadius e K)
    (a₀ : A) (h₀ : a₀ ∈ safeCandidates safe)
    (hgap : 3 * avgRadius e K < g a₀) :
    ∃ a' ∈ safeCandidates safe,
      0 < g a' ∧ g a₀ - 2 * avgRadius e K ≤ g a' :=
  have hrad : 0 ≤ avgRadius e K := by
    unfold avgRadius
    apply div_nonneg he (Real.sqrt_nonneg _)
  certified_gain_select g Ghat safe (avgRadius e K) hrad hconc a₀ h₀
    hgap

end Hagi.Growth
