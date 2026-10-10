/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Step.SafeQP
set_option linter.style.header false

/-!
# CurvatureSafe — учитывающий кривизну SafeQP (trust region)

Второпорядковая оценка при L-Lipschitz градиентах:
`L_i(w+d) − L_i(w) ≤ −⟪g i, d⟫ + (L_i/2)·‖d‖²`.

* `safeqp_second_order`: при `−eps ≤ inner` и гладкости —
  `dL ≤ eps + L·dnorm²/2`;
* `safeqp_trust_region`: при `dnorm² ≤ 2·eps/L` —
  `dL ≤ 2·eps` (явный радиус trust-региона);
* `safeqp_monotone_domain`: при `0 ≤ inner`, `L > 0`,
  `dnorm² ≤ 2·slack/L` и `slack ≤ 0` — `dL ≤ 0`
  (точный сертификат, вырожденный случай: посылки влекут
  `‖d‖² = 0`).
-/

namespace Hagi.Dynamics

/-- При `−eps ≤ inner` и `dL ≤ −inner + L·dnorm²/2` —
`dL ≤ eps + L·dnorm²/2`. -/
theorem safeqp_second_order (inner eps L dnorm dL : ℝ)
    (hfeas : -eps ≤ inner) (_hL : 0 ≤ L)
    (h_emp_smooth : dL ≤ -inner + L * dnorm ^ 2 / 2) :
    dL ≤ eps + L * dnorm ^ 2 / 2 := by
  linarith

/-- При `0 < L`, `−eps ≤ inner`, гладкости и
`dnorm² ≤ 2·eps/L` — `dL ≤ 2·eps`. -/
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

/-- При `0 ≤ inner`, `0 < L`, `dnorm² ≤ 2·slack/L` и
`slack ≤ 0` — `dL ≤ 0`. Посылки вынуждают `dnorm² = 0`
(вырожденный точный случай, не аргумент о марже). -/
theorem safeqp_monotone_domain (inner slack L dnorm dL : ℝ)
    (hfeas : 0 ≤ inner) (hL : 0 < L)
    (h_emp_smooth : dL ≤ -inner + L * dnorm ^ 2 / 2)
    (hrad : dnorm ^ 2 ≤ 2 * slack / L) (hslack : slack ≤ 0) :
    dL ≤ 0 := by
  -- direct: dL ≤ −inner + (L/2)‖d‖² ≤ 0 + slack ≤ 0
  have h4 : L * dnorm ^ 2 / 2 ≤ slack := by
    calc L * dnorm ^ 2 / 2 = (L / 2) * dnorm ^ 2 := by ring
      _ ≤ (L / 2) * (2 * slack / L) := by
          apply mul_le_mul_of_nonneg_left hrad (by linarith)
      _ = slack := by field_simp
  linarith
end Hagi.Dynamics

namespace Hagi
export Hagi.Dynamics (safeqp_second_order safeqp_trust_region safeqp_monotone_domain)
end Hagi
