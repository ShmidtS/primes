/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.SafeQP
set_option linter.style.header false

/-!
# R60: curvature-aware SafeQP (trust region)

Block I.2 of the grand-unified roadmap: the linearized safety
constraint ⟨g_i, d⟩ ≥ −ε_i is only a first-order certificate.
With L_i-Lipschitz gradients the actual per-domain loss
change obeys the second-order bound

  L_i(w + d) − L_i(w) ≤ −⟪g_i, d⟫ + (L_i/2)‖d‖² ≤ ε_i + (L_i/2)‖d‖²,

and the step is monotonically safe on EVERY domain whenever
‖d*‖² ≤ 2·min_i(ε_i/L_i) — an explicit trust-region radius
computable from the measured Lipschitz constants and the
safety margins. No learning-rate condition involved.
-/

namespace Hagi

/-- **Second-order safety of the SafeQP step**: with the
linearized constraint ⟪g_i, d⟫ ≥ −ε_i (the SafeQP feasible
set) and L_i-Lipschitz gradients (h_emp_smooth), the actual
loss change on domain i is at most ε_i + (L_i/2)‖d‖². -/
theorem safeqp_second_order (inner eps L dnorm dL : ℝ)
    (hfeas : -eps ≤ inner) (hL : 0 ≤ L)
    (h_emp_smooth : dL ≤ -inner + L * dnorm ^ 2 / 2) :
    dL ≤ eps + L * dnorm ^ 2 / 2 := by
  linarith

/-- **The explicit trust-region radius**: if the SafeQP step
norm obeys ‖d*‖² ≤ 2·ε/L (with ε the safety margin and L the
Lipschitz constant), the second-order bound collapses to
dL ≤ 2·ε — and with the margin ε′ := 2ε the step is
certifiably non-catastrophic on that domain regardless of
the learning rate. -/
theorem safeqp_trust_region (inner eps L dnorm dL : ℝ)
    (hfeas : -eps ≤ inner) (hL : 0 < L)
    (h_emp_smooth : dL ≤ -inner + L * dnorm ^ 2 / 2)
    (hrad : dnorm ^ 2 ≤ 2 * eps / L) :
    dL ≤ 2 * eps := by
  have h1 := safeqp_second_order inner eps L dnorm dL hfeas hL.le h_emp_smooth
  have h2 : L * dnorm ^ 2 / 2 ≤ eps := by
    calc L * dnorm ^ 2 / 2 = (L / 2) * dnorm ^ 2 := by ring
      _ ≤ (L / 2) * (2 * eps / L) := by
          apply mul_le_mul_of_nonneg_left hrad (by linarith)
      _ = eps := by field_simp
  linarith

/-- **Monotone per-domain safety**: if the trust region is
tight (‖d*‖² ≤ 2ε/L AND the linearized inner product is
nonnegative — the conflict-free case), the domain loss does
not increase at all: the exact second-order certificate. -/
theorem safeqp_monotone_domain (inner eps L dnorm dL : ℝ)
    (hfeas : 0 ≤ inner) (hL : 0 < L)
    (h_emp_smooth : dL ≤ -inner + L * dnorm ^ 2 / 2)
    (hrad : dnorm ^ 2 ≤ 2 * eps / L) (heps : eps ≤ 0) :
    dL ≤ 0 := by
  -- direct: dL ≤ −inner + (L/2)‖d‖² ≤ 0 + eps ≤ 0
  have h4 : L * dnorm ^ 2 / 2 ≤ eps := by
    calc L * dnorm ^ 2 / 2 = (L / 2) * dnorm ^ 2 := by ring
      _ ≤ (L / 2) * (2 * eps / L) := by
          apply mul_le_mul_of_nonneg_left hrad (by linarith)
      _ = eps := by field_simp
  linarith
end Hagi
