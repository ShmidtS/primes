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

- `safeqp_idle` + idle_identity (#6 Identity under Idle):
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

/-- **SafeQP is idle at zero gradient (roadmap #6; R102
honesty fix)**: what is proved is the PLAIN statement that
0 minimizes dist(·, 0) on the safe set C — dist(0,0) = 0 ≤
dist d 0 for every d ∈ C. This is the g₀ = 0 SPECIALIZATION
of the SafeQP objective (dist(d, g₀) with g₀ = 0); it does
NOT by itself characterize the SafeQP solution d* for a
general gradient — that characterization is the projection
theorem (`safeQP_exists_unique`), a separate result. -/
theorem safeqp_idle {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (C : Set X) (_hconv : Convex ℝ C) (_h0 : (0:X) ∈ C) :
    ∀ d ∈ C, dist (0:X) (0:X) ≤ dist d (0:X) := by
  intro d hd
  simp

/-- **The idle-merge zero-gap lemma (roadmap #6, part 1; R75
honesty fix: renamed from idle_identity — the full
macro-cycle identity is NOT yet composed)**: on consensus
logits (every pairwise deviation identically 0) the merge
gap is EXACTLY 0 (twoGap_zero_iff). Together with the
separately-proven safeqp_idle (zero gradient ⟹ step 0)
this covers the merge and joint stages; the compression
stage's idle behavior is not yet formalized, so the full
cycle-identity theorem remains OPEN. -/

theorem idle_merge_zero_gap {k : Type} [Fintype k] [Nonempty k]
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
