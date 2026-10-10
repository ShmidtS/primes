/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.Distill
import Hagi.Audit.Exactness
import Hagi.Unified.GlobalDynamics
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The insight channel

* `insight_kl_descent`: the CE gap between student and insight-teacher equals the corresponding KL gap.
* `insight_consolidation_safe`: SafeQP consolidation gives per-domain drift bounded by `ε` and preserved descent.
* `experience_cycle_bound`: a one-cycle Lyapunov budget inequality for the experience gate.
* `tldr_drift_null`, `tldr_two_tier_safety`: low-rank insight adapters act as zero on the adapter's kernel; combined with the Fisher KL budget this gives two-tier safety.
-/

open Real Finset InnerProductSpace

namespace Hagi.Autonomy

section Insight

variable {V : Type*} [Fintype V]

/-- For strictly positive distributions q, pI, pTheta:
crossEntropy q pTheta − crossEntropy q pI
= klDiv q pTheta − klDiv q pI.
-/
theorem insight_kl_descent (q pI pTheta' : V → ℝ)
    (hq : ∀ v, 0 < q v) (hI : ∀ v, 0 < pI v) (hT : ∀ v, 0 < pTheta' v) :
    crossEntropy q pTheta' - crossEntropy q pI
      = klDiv q pTheta' - klDiv q pI :=
  ce_gap_kl_identity q pI pTheta' hq hI hT

/-- Given the stage inequality `Enext ≤ Et - Gins - Gmerge - eta * dnorm2 / 2 + Cquant + Cexp`, the next-cycle energy satisfies `Enext ≤ Et - (Gins + Gmerge + eta * dnorm2 / 2 - Cexp - Cquant)`.
-/
theorem experience_cycle_bound (Et Enext Gins Gmerge dnorm2 eta Cexp Cquant : ℝ)
    (hstage : Enext ≤ Et - Gins - Gmerge - eta * dnorm2 / 2 + Cquant + Cexp) :
    Enext ≤ Et - (Gins + Gmerge + eta * dnorm2 / 2 - Cexp - Cquant) := by
  linarith


section Consolidation

/-- If `ds` minimizes the distance to `gI` over a convex set `C ∋ 0` contained in the cone `{d | ⟨gold, d⟫ ≥ -heps}`, then `⟨gold, ds⟫ ≥ -heps` and `‖ds‖ ^ 2 ≤ ⟨gI, ds⟫`.
-/
theorem insight_consolidation_safe {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    (C : Set X) (hconv : Convex ℝ C) (h0 : (0:X) ∈ C)
    (gI ds : X) (hs : ds ∈ C)
    (hmin : ∀ d ∈ C, dist ds gI ≤ dist d gI)
    (gold : X) (heps : ℝ)
    (hcone : C ⊆ {d : X | ⟪gold, d⟫_ℝ ≥ -heps}) :
    ⟪gold, ds⟫_ℝ ≥ -heps ∧ ‖ds‖^2 ≤ ⟪gI, ds⟫_ℝ := by
  exact ⟨hcone hs, (Hagi.safeQP_descent C hconv h0 gI ds hs hmin).1⟩

end Consolidation
end Insight

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- If `B.mulVec x = 0` then `(A * B).mulVec x = 0`: a low-rank adapter acts as zero on the kernel of `B`. -/
theorem tldr_drift_null {m n r : Type} [Fintype m] [Fintype n] [Fintype r]
    (A : Matrix r m ℝ) (B : Matrix m n ℝ) (x : n → ℝ)
    (hx : B.mulVec x = 0) :
    (A * B).mulVec x = 0 := by
  rw [show (A * B).mulVec x = A.mulVec (B.mulVec x) from
      (Matrix.mulVec_mulVec x A B).symm]
  rw [hx]
  simp [Matrix.mulVec_zero]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- Combines `tldr_drift_null` with `forgetting_kl_bound`: under `B.mulVec x = 0`, `kl ≤ ⟨dW, F dW⟫ / 2`, and `⟨dW, F dW⟫ ≤ 2 * eps`, the adapter output on `x` is zero and `kl ≤ eps`. -/
theorem tldr_two_tier_safety {m n r : Type} [Fintype m] [Fintype n] [Fintype r]
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (A : Matrix r m ℝ) (B : Matrix m n ℝ) (x : n → ℝ)
    (hx : B.mulVec x = 0)
    (F : X →L[ℝ] X) (dW : X) (kl eps : ℝ)
    (h_emp_second : kl ≤ ⟪dW, F dW⟫_ℝ / 2)
    (hball : ⟪dW, F dW⟫_ℝ ≤ 2 * eps) :
    (A * B).mulVec x = 0 ∧ kl ≤ eps :=
  ⟨tldr_drift_null A B x hx, forgetting_kl_bound F dW kl eps h_emp_second hball⟩

end Hagi.Autonomy

namespace Hagi
export Hagi.Autonomy (insight_kl_descent experience_cycle_bound insight_consolidation_safe tldr_drift_null tldr_two_tier_safety)
end Hagi
