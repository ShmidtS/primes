/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic

set_option linter.style.header false

/-!
# SafeQPRobust — устойчивая к возмущениям допустимость

* `robust_feasibility`: при `eps + m ≤ g*d` и
  `|g*d − gdhat| ≤ m` — `eps ≤ gdhat` (запас eps + m
  поглощает шум батча);
* `stochastic_safeqp_feasible`: построчная версия для всех
  доменов i;
* `stochastic_safeqp_descent`: при `dnorm² ≤ inner_true`,
  `|inner_est − inner_true| ≤ m0`, `0 < L`, `eta ≤ 1/L` и
  гладкости — `E₂ ≤ E₁ − eta·dnorm²/2 + eta·m0`
  (чистый спуск при `m0 < dnorm²`).

Полная проекционно-возмущенческая оценка `‖d̂*−d*‖` — не
доказана (матричная теория возмущений).
-/

open Finset

namespace Hagi

/-- При `eps + m ≤ g*d` и `|g*d − gdhat| ≤ m`:
`eps ≤ gdhat`. -/
theorem robust_feasibility (g d gdhat : ℝ) (eps m : ℝ)
    (htrue : eps + m ≤ g * d) (hpert : |g * d - gdhat| ≤ m) :
    eps ≤ gdhat := by
  nlinarith [abs_le.mp hpert]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- Если для всех i выполнено `eps i + m i ≤ g i * d i` и
`|g i * d i − gdhat i| ≤ m i`, то `eps i ≤ gdhat i` для
всех i. -/
theorem stochastic_safeqp_feasible {K : Type} [Fintype K]
    (g d gdhat : K → ℝ) (eps m : K → ℝ)
    (htrue : ∀ i, eps i + m i ≤ g i * d i)
    (h_emp_conc : ∀ i, |g i * d i - gdhat i| ≤ m i) :
    ∀ i, eps i ≤ gdhat i :=
  fun i => Hagi.robust_feasibility (g i) (d i) (gdhat i) (eps i) (m i)
    (htrue i) (h_emp_conc i)

/-- При `dnorm² ≤ inner_true`, `|inner_est − inner_true| ≤ m0`,
`0 < L`, `0 ≤ eta ≤ 1/L` и гладкости
`E₂ ≤ E₁ − eta·inner_est + L·eta²·dnorm²/2` —
`E₂ ≤ E₁ − eta·dnorm²/2 + eta·m0`. -/
theorem stochastic_safeqp_descent (inner_true inner_est dnorm m0 eta L E1 E2 : ℝ)
    (hdescent : dnorm ^ 2 ≤ inner_true)
    (h_emp_conc : |inner_est - inner_true| ≤ m0)
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (h_emp_smooth : E2 ≤ E1 - eta * inner_est + L * eta ^ 2 * dnorm ^ 2 / 2) :
    E2 ≤ E1 - eta * dnorm ^ 2 / 2 + eta * m0 := by
  have heff : dnorm ^ 2 - m0 ≤ inner_est := by
    rw [abs_le] at h_emp_conc
    have h1 : -(m0) ≤ inner_est - inner_true := h_emp_conc.1
    have h2 : inner_est - inner_true ≤ m0 := h_emp_conc.2
    have h3 : inner_true - m0 ≤ inner_est := by linarith
    linarith
  have hsecond : L * eta ^ 2 * dnorm ^ 2 / 2 ≤ eta * dnorm ^ 2 / 2 := by
    have hLe : L * eta ≤ 1 := by
      have hmono : L * eta ≤ L * (1 / L) := mul_le_mul_of_nonneg_left heta (by linarith)
      have hdiv : L * (1 / L) = 1 := by field_simp
      linarith
    by_cases hd : dnorm ^ 2 = 0
    · rw [hd]
      norm_num
    · have hd2 : 0 < dnorm ^ 2 := by
        have hnn : 0 ≤ dnorm ^ 2 := sq_nonneg dnorm
        by_contra hc
        push Not at hc
        apply hd
        linarith
      have hsplit : L * eta ^ 2 * dnorm ^ 2 = (L * eta) * (eta * dnorm ^ 2) := by ring
      rw [hsplit]
      have hmono : (L * eta) * (eta * dnorm ^ 2) ≤ 1 * (eta * dnorm ^ 2) :=
        mul_le_mul_of_nonneg_right hLe (by nlinarith)
      calc L * eta * (eta * dnorm ^ 2) / 2
          = (L * eta) * (eta * dnorm ^ 2) / 2 := by ring
        _ ≤ 1 * (eta * dnorm ^ 2) / 2 := by
            have hd2' : 2 * ((L * eta) * (eta * dnorm ^ 2) / 2)
                = (L * eta) * (eta * dnorm ^ 2) := by ring
            have hd3' : 2 * (1 * (eta * dnorm ^ 2) / 2) = eta * dnorm ^ 2 := by ring
            nlinarith [hmono, hd2', hd3']
        _ = eta * dnorm ^ 2 / 2 := by ring
  nlinarith [h_emp_smooth, heff, hsecond, heta0]

end Hagi
