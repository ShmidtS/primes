/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.Unified

set_option linter.style.header false

/-!
# SafeQPRobust: perturbation-robust feasibility (round 49, block 1.1)

The stochastic-Gram core: the batch-estimated inner product
⟨ĝ_i, d̂⟩ differs from the exact ⟨g_i, d⟩ by at most m (the
sub-Gaussian batch noise bound). Theorem: if the TRUE margin
is eps + m (the guard set one noise-bound tighter), the
NOISY check still certifies eps — the adaptive protective
threshold: run the QP with ε_i + m and the step is safe
under batch noise.

NOT PROVED this round (reported, not assumed): the full
projection-perturbation bound ‖d̂*−d*‖ ≤ C·σ/(√B·σ_min(G))
— requires matrix perturbation theory for projections.

**Prescription**: set the QP margins to ε_i + m with
m = c·σ/√B from the measured gradient noise (two-batch
estimator); the safety guarantee survives the noise.
-/

open Finset

namespace Hagi

/-- **The robust-feasibility margin theorem**: with the true
inner product at least ε + m above zero and the estimation
error at most m, the noisy inner product still certifies ε —
the guard threshold ε + m absorbs the batch noise. -/
theorem robust_feasibility (g d gdhat : ℝ) (eps m : ℝ)
    (htrue : eps + m ≤ g * d) (hpert : |g * d - gdhat| ≤ m) :
    eps ≤ gdhat := by
  nlinarith [abs_le.mp hpert]

end Hagi
