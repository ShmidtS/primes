/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Growth.SelfDevelopment

/-!
# AdaptiveQuery — averaging shrinks the controller's selection penalty

The openai/math 139 core (subpolynomial queries suffice:
ADAPTIVE multi-query estimation beats single evaluation),
specialized to the HAGI controller vocabulary: the selection
penalty of `certified_gain_select` scales LINEARLY with the
estimation radius ε, and the K-draw averaging radius shrinks
as ε/√K (the Dust population law `dustVarianceDecay`). Hence
spending K queries per candidate buys a √K reduction of the
selection threshold — the adaptive-search brick: the
controller should not trust single measurements.

Main results:

* `avgRadius`: the averaged-estimator radius e/√K — the
  query-allocation function (decreasing in K);
* `avgRadius_shrinks`: K ≥ 1 queries never increase the
  radius, and the radius is the single-draw error exactly at
  K = 1;
* `certified_gain_select_avg`: `certified_gain_select`
  instantiated at the averaged radius: a candidate pool
  served with K queries per candidate admits certified
  selection at threshold 3e/√K — the 139-style saving.
-/

namespace Hagi.Growth

open Finset

/-- The averaged-estimator radius: e/√K for K queries. -/
noncomputable def avgRadius (e : ℝ) (K : ℕ) : ℝ := e / Real.sqrt K

/-- The radius function is 1-anchored (K = 1 recovers the
single-draw error) and nonincreasing in K over the positive
integers. -/
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

/-- **Averaged certified selection**: with K queries per
candidate the averaged measurements deviate by at most
e/√K (premise — the Dust population law), so the controller
selects a strictly positive TRUE gain whenever some safe
candidate has g ≥ 3e/√K: the selection threshold shrinks by
√K against the single-query controller. -/
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
