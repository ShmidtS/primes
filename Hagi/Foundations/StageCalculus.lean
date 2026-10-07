/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# StageCalculus — pure stage-arithmetic of the macro cycle

`compress_stage`: if the empirical distortion is bounded by
1/2 and the third-order span obeys the Lipschitz empirical
law, then the compress-stage energy increase is at most
kappa·s/2 — pure arithmetic, no dependencies.

Extracted from Unified/MacroCycle (R207 layer-hygiene): the
fact is layer-0 arithmetic consumed by Energy/QuantBridge (2);
the old edge Energy → Unified is thereby removed.
-/

namespace Hagi.Foundations

/-- **Compress stage arithmetic**: distortion ≤ 1/2 and the
empirical Lipschitz span law give the compress-stage bound. -/
theorem compress_stage (kappa s dnorm E3 E2pre : ℝ)
    (hkappa : 0 ≤ kappa) (hs : 0 ≤ s) (_hdn : 0 ≤ dnorm)
    (h_emp_dist : dnorm ≤ 1 / 2)
    (h_emp_lip : E3 - E2pre ≤ kappa * s * dnorm) :
    E3 - E2pre ≤ kappa * s / 2 := by
  have h1 : kappa * s * dnorm ≤ kappa * s * (1/2) :=
    mul_le_mul_of_nonneg_left h_emp_dist (by positivity)
  have h3 : kappa * s * (1/2) = kappa * s / 2 := by ring
  rw [h3] at h1
  linarith

end Hagi.Foundations
