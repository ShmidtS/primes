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

/-- **Stochastic SafeQP: the safety certificate survives
minibatch noise**. If the TRUE inner product on every domain
clears the safety margin with the robust reserve
(⟪gᵢ,d⟫ ≥ εᵢ + mᵢ) and the minibatch estimate is within mᵢ
of the truth (the h_emp_ concentration radius — the
subgaussian form m = σ·√(2·log(K/δ)/B)), then EVERY domain's
estimated inner product still clears its margin: the QP
feasibility check on estimated Gram rows is sound. -/
theorem stochastic_safeqp_feasible {K : Type} [Fintype K]
    (g d gdhat : K → ℝ) (eps m : K → ℝ)
    (htrue : ∀ i, eps i + m i ≤ g i * d i)
    (h_emp_conc : ∀ i, |g i * d i - gdhat i| ≤ m i) :
    ∀ i, eps i ≤ gdhat i :=
  fun i => Hagi.robust_feasibility (g i) (d i) (gdhat i) (eps i) (m i)
    (htrue i) (h_emp_conc i)

/-- **Noisy SafeQP: the descent certificate degrades
gracefully (R75 honesty fix)**. The certified descent
⟪g₀,d*⟫ ≥ ‖d*‖² holds for the TRUE inner product; the
minibatch ESTIMATE deviates by at most m₀ (the concentration
radius, h_emp_conc — a REAL two-quantity hypothesis, not the
degenerate |x−x| of the pre-R75 version). The smooth lemma
applied at the estimated inner product then gives
E₂ ≤ E₁ − η‖d*‖²/2 + η·m₀. Net descent whenever m₀ < ‖d*‖²;
the batch condition B ≥ 2σ²·log(1/δ)/‖d*‖⁴ supplies the
concentration radius (external subgaussian form, h_emp_). -/
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
        push_neg at hc
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
