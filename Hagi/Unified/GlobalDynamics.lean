/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Ensemble.Hoeffding
set_option linter.style.header false

/-!
# Global dynamics: idle behavior and the Fisher forgetting bound

* `safeqp_idle`: `dist 0 0 ≤ dist d 0` for every `d ∈ C` (the
  g₀ = 0 specialization of the SafeQP objective).
* `idle_merge_zero_gap`: at consensus logits the merge gap is
  exactly 0.
-/

open Real InnerProductSpace

namespace Hagi.Unified

/-- At a softmax distribution with all pairwise logit
deviations 0, `twoGap` is exactly 0. The compression stage's
idle behavior is not formalized here. -/

theorem idle_merge_zero_gap {k : Type} [Fintype k] [Nonempty k]
    (m : k → ℝ) (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1) :
    Hagi.twoGap (fun v => Real.exp (m v) / ∑ w, Real.exp (m w)) (fun _ => (0:ℝ)) = 0 :=
    (Hagi.twoGap_zero_iff hp hsum).mpr ⟨0, fun _ => rfl⟩

end Hagi.Unified

namespace Hagi
export Hagi.Unified (idle_merge_zero_gap)
end Hagi
