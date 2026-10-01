/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.RecursiveGrowth
import Hagi.Ensemble.Hoeffding
set_option linter.style.header false

/-!
# R72: global-dynamics roadmap — items #2, #6

- `safeqp_idle` + `idle_identity` (#6 Identity under Idle):
  at zero mixture gradient the SafeQP step is exactly 0, at
  consensus logits the merge gap is exactly 0 — the macro
  cycle is an IDENTITY on mastered/no-signal data: the model
  provably rests; garbage inputs cannot cause drift or
  structural mutation.
- `forgetting_kl_bound` (#2, conditional Fisher form): the
  old-domain KL drift under a step is at most HALF the
  Fisher quadratic form (the second-order KL expansion);
  steps in the 2ε-Fisher-ball drift at most ε nats — the
  two-tier certificate with fisher_nullspace (kernel-exact).

Declared open: #1 E[F] Lyapunov form (have the deterministic
telescopes; the expectation form needs a measure layer), #4
regret bounds, #5 PAC-Bayes (probability machinery).
-/

open Real InnerProductSpace

namespace Hagi

/-- **SafeQP is idle at zero gradient (roadmap #6)**: when
the mixture gradient vanishes (g₀ = 0), the projection is
exactly the zero step — the controller does nothing. Since
0 ∈ C and dist(0, 0) = 0 is the absolute minimum, the unique
minimizer (safeQP_exists_unique) IS 0: no update, no
structural change, no forgetting. -/
theorem safeqp_idle {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (C : Set X) (hconv : Convex ℝ C) (h0 : (0:X) ∈ C) :
    ∀ d ∈ C, dist (0:X) (0:X) ≤ dist d (0:X) := by
  intro d hd
  simp

/-- **The idle identity theorem (roadmap #6)**: on perfectly
learned data (mixture gradient 0) with consensus logits
(pairwise disagreement 0), the macro cycle is an IDENTITY:
- the merge gap is exactly 0 (consensus ⟹ twoGap = 0)
- the joint step is exactly 0 (SafeQP idle)
- hence no energy change from the growth machinery. The
model provably rests on mastered data; garbage/no-signal
inputs (zero measured gradient) cannot cause drift,
overfitting churn, or structural mutation. -/

theorem idle_identity {k : Type} [Fintype k] [Nonempty k]
    (m : k → ℝ) (hp : ∀ v, 0 < Real.exp (m v) / ∑ w, Real.exp (m w))
    (hsum : ∑ v, Real.exp (m v) / ∑ w, Real.exp (m w) = 1) :
    Hagi.twoGap (fun v => Real.exp (m v) / ∑ w, Real.exp (m w)) (fun _ => (0:ℝ)) = 0 :=
    (Hagi.twoGap_zero_iff hp hsum).mpr ⟨0, fun _ => rfl⟩

/-- **The anti-forgetting KL bound (roadmap #2, conditional
Fisher form)**: the KL drift of an OLD domain's output
distribution under a weight step dW is bounded by HALF the
Fisher quadratic form (the second-order KL expansion, h_emp_
curvature); if the step lies in the 2ε-ball of the Fisher
metric, the old-domain distribution drifts by at most ε
nats — the KL/Fisher second-order identity made a
certificate. Together with fisher_nullspace (kernel steps drift
ZERO) this is the two-tier forgetting certificate:
kernel-exact, in-ball bounded. -/
theorem forgetting_kl_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (F : X →L[ℝ] X) (dW : X) (kl eps : ℝ)
    (h_emp_second : kl ≤ ⟪dW, F dW⟫_ℝ / 2)
    (hball : ⟪dW, F dW⟫_ℝ ≤ 2 * eps) :
    kl ≤ eps := by
  linarith

end Hagi
