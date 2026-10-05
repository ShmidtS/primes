/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.SafeQPRobust
import Hagi.Foundations.Recurrence

set_option linter.style.header false

/-!
# LazyAdamMomentum: the β₁ > 0 dense-moment decay (round 49, block 1.2)

For an INACTIVE row (zero gradient for d steps), the dense
first moment decays EXACTLY geometrically: m_{t} = β₁^d · m_τ
— so the lazy approximation (holding m = 0) errs by at most
β₁^d · |m_τ| ≤ β₁^d · M given the moment bound M. At
β₁ = 0.9, 50 inactive steps shrink the drift below 0.01·M.

NOT PROVED: the full trajectory-equivalence bound
‖w_lazy − w_dense‖ ≤ O(β₁^k·η/(1−β₂)) with the O(1/√T)
rate preserved — the composition over interleaved touches.

**Prescription**: lazy tables with β₁ > 0 are SAFE whenever
the row's inactivity stretches exceed log(δ/M)/log(β₁) —
computable from the token-arrival statistics (Zipf gives the
distances almost for free).
-/

open Finset

namespace Hagi

/-- **The dense first moment decays geometrically** on zero
gradients: m_k = β₁^k · m_0 under the recurrence m' = β₁·m
(the dense-momentum evolution of an untouched row). -/
theorem dense_m_decay (beta1 : ℝ) (m : ℕ → ℝ)
    (hstep : ∀ t, m (t+1) = beta1 * m t) (k : ℕ) :
    m k = (beta1^k) * m 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [hstep, ih, pow_succ]; ring

/-- **The lazy-drift bound**: if the dense moment magnitude
is bounded by M and the row was last touched d steps ago,
the lazy approximation (m := 0) errs by at most β₁^d · M. -/
theorem lazy_moment_drift (beta1 M : ℝ) (m : ℕ → ℝ) (hb : 0 ≤ beta1)
    (hM0 : |m 0| ≤ M) (hstep : ∀ t, m (t+1) = beta1 * m t) (d : ℕ) :
    |m d| ≤ |beta1^d| * M := by
  rw [dense_m_decay beta1 m hstep d, abs_mul, abs_of_nonneg (pow_nonneg hb d)]
  exact mul_le_mul_of_nonneg_left hM0 (pow_nonneg hb d)

/-- The momentum-decay trajectory bound (P1): the cumulative
skipped-step contribution over any gap d is at most
η·(‖m_t‖/(√v+ε))·β₁/(1−β₁); stated with the effective
per-step magnitude c := η·‖m_t‖/(√v_min+ε) as h_emp input. -/
theorem lazy_momentum_bound (beta c : ℝ)
    (hbeta : 0 < beta) (hbeta1 : beta < 1) (hc : 0 ≤ c)
    (d : ℕ) :
    c * (∑ s ∈ Finset.range d, beta ^ (s + 1))
      ≤ c * (beta / (1 - beta)) := by
  have hgeom : ∑ s ∈ Finset.range d, beta ^ (s + 1) ≤ beta / (1 - beta) := by
    have hsplit : ∑ s ∈ Finset.range d, beta ^ (s + 1)
        = beta * ∑ s ∈ Finset.range d, beta ^ s := by
      rw [show ∑ s ∈ Finset.range d, beta ^ (s + 1)
          = ∑ s ∈ Finset.range d, beta * beta ^ s from
          Finset.sum_congr rfl (fun s _ => by ring)]
      exact (Finset.mul_sum (s := Finset.range d) (f := fun s => beta ^ s) (a := beta)).symm
    rw [hsplit]
    have hsum := Hagi.Foundations.geom_sum_le_inv beta d hbeta.le hbeta1
    have hmul : beta * ∑ s ∈ Finset.range d, beta ^ s
        ≤ beta * (1 / (1 - beta)) :=
      mul_le_mul_of_nonneg_left hsum hbeta.le
    have hconv : beta * (1 / (1 - beta)) = beta / (1 - beta) := by field_simp
    linarith
  exact mul_le_mul_of_nonneg_left hgeom hc
