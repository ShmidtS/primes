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
* `forgetting_kl_bound`: `kl ≤ eps` whenever
  `kl ≤ ⟪dW, F dW⟫ / 2` and `⟪dW, F dW⟫ ≤ 2 * eps`.
-/

open Real InnerProductSpace

namespace Hagi.Unified

/-- `dist 0 0 ≤ dist d 0` for every `d ∈ C`; the `g₀ = 0`
specialization of the SafeQP objective. Not a
characterization of the solution for a general gradient. -/
theorem safeqp_idle {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (C : Set X) (_hconv : Convex ℝ C) (_h0 : (0:X) ∈ C) :
    ∀ d ∈ C, dist (0:X) (0:X) ≤ dist d (0:X) := by
  intro d hd
  simp

/-- At a softmax distribution with all pairwise logit
deviations 0, `twoGap` is exactly 0. The compression stage's
idle behavior is not formalized here. -/

theorem idle_merge_zero_gap {k : Type} [Fintype k] [Nonempty k]
    (m : k → ℝ) (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1) :
    Hagi.twoGap (fun v => Real.exp (m v) / ∑ w, Real.exp (m w)) (fun _ => (0:ℝ)) = 0 :=
    (Hagi.twoGap_zero_iff hp hsum).mpr ⟨0, fun _ => rfl⟩

/-- If `kl ≤ ⟪dW, F dW⟫_ℝ / 2` (h_emp_ curvature) and
`⟪dW, F dW⟫_ℝ ≤ 2 * eps`, then `kl ≤ eps`. -/
theorem forgetting_kl_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (F : X →L[ℝ] X) (dW : X) (kl eps : ℝ)
    (h_emp_second : kl ≤ ⟪dW, F dW⟫_ℝ / 2)
    (hball : ⟪dW, F dW⟫_ℝ ≤ 2 * eps) :
    kl ≤ eps := by
  linarith

end Hagi.Unified

namespace Hagi
export Hagi.Unified (safeqp_idle idle_merge_zero_gap forgetting_kl_bound)
end Hagi
