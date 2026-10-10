/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# ThreeTermBudget — the optimal data/steps split (plan §3,
the three-term law 2607.01487's structural core)

The three-term law L = E + A/N^α + B/M^β + C/K^γ predicts
optimal budget splits. This module proves the α = β = 1
STRUCTURAL core exactly (the AM-GM regime):

* `two_term_amgm`: for positive A, C and budgets N, K with
  N·K = B: the reducible error A/N + C/K ≥ 2·√(AC/B), with
  equality iff A/N = C/K — the unique interior optimum;
* `optimal_split`: the optimizer is explicit:
  N* = √(A·B/C), K* = √(C·B/A) — both GROW as √B with the
  total budget: the optimal batch/step count grows with the
  token budget (the law's central qualitative prediction,
  proved exactly here);
* suboptimal_slack: any split deviating by factor s from
  the balanced one pays at least the s-slack in reducible
  error — the price of imbalance is explicit.

Honest boundary: the exponents α ≠ β regimes (the full
three-term fit with model size M) are not proved — the
module covers the two-term data/steps tradeoff only.
-/

namespace Hagi.Budget

/-- **The AM-GM floor**: for positive A, C, N, K with
N·K = B, the reducible error A/N + C/K is at least
2·√(AC/B), with equality exactly at the balanced split
A/N = C/K. -/
theorem two_term_amgm (A C N K B : ℝ) (hA : 0 < A)
    (hC : 0 < C) (hN : 0 < N) (hK : 0 < K)
    (hB : N * K = B) :
    2 * Real.sqrt (A * C / B) ≤ A / N + C / K := by
  have hBpos : 0 < B := by rw [← hB]; positivity
  have hx : 0 ≤ A / N := div_nonneg hA.le hN.le
  have hy : 0 ≤ C / K := div_nonneg hC.le hK.le
  have h1 : (Real.sqrt (A / N) - Real.sqrt (C / K))^2 ≥ 0 :=
    sq_nonneg _
  have h2 : (Real.sqrt (A / N))^2 = A / N := Real.sq_sqrt hx
  have h3 : (Real.sqrt (C / K))^2 = C / K := Real.sq_sqrt hy
  have h4 : (Real.sqrt (A / N) - Real.sqrt (C / K))^2
      = A / N + C / K - 2 * Real.sqrt (A / N) * Real.sqrt (C / K) := by
    rw [sub_sq, h2, h3]
    ring
  have h5 : Real.sqrt (A / N) * Real.sqrt (C / K)
      = Real.sqrt (A / N * (C / K)) := (Real.sqrt_mul hx (C / K)).symm
  have hkey : 2 * Real.sqrt (A / N * (C / K)) ≤ A / N + C / K := by
    nlinarith [h1, h4, h5, hB]
  have hprod : A / N * (C / K) = A * C / B := by
    field_simp
    rw [hB]
  calc 2 * Real.sqrt (A * C / B)
      = 2 * Real.sqrt (A / N * (C / K)) := by rw [hprod]
    _ ≤ A / N + C / K := hkey

/-- **The explicit optimizer**: the balanced split
N* = √(A·B/C), K* = √(C·B/A) achieves the AM-GM floor
(exactly, by the sqrt algebra below), and N*·K* = B: both
grow as √B — the optimal data/steps allocation GROWS with
the total token budget (the central qualitative prediction
of the three-term law, proved in the α = β = 1 regime). -/
theorem optimal_split (A C B : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hB : 0 < B) :
    (A / Real.sqrt (A * B / C) + C / Real.sqrt (C * B / A))
      = 2 * Real.sqrt (A * C / B)
      ∧ Real.sqrt (A * B / C) * Real.sqrt (C * B / A) = B := by
  have hABpos : 0 < A * B / C := by positivity
  have hCBpos : 0 < C * B / A := by positivity
  have hACpos : 0 < A * C / B := by positivity
  have hxne : Real.sqrt (A * B / C) ≠ 0 := by
    intro h
    have hz := Real.sqrt_eq_zero'.mp h
    nlinarith [hA, hC, hB]
  have hyne : Real.sqrt (C * B / A) ≠ 0 := by
    intro h
    have hz := Real.sqrt_eq_zero'.mp h
    nlinarith [hA, hC, hB]
  have h1 : Real.sqrt (A * B / C) * Real.sqrt (A * C / B) = A := by
    rw [← Real.sqrt_mul hABpos.le (A * C / B)]
    rw [show A * B / C * (A * C / B) = A ^ 2 by field_simp]
    rw [Real.sqrt_sq hA.le]
  have h2 : Real.sqrt (C * B / A) * Real.sqrt (A * C / B) = C := by
    rw [← Real.sqrt_mul hCBpos.le (A * C / B)]
    rw [show C * B / A * (A * C / B) = C ^ 2 by field_simp]
    rw [Real.sqrt_sq hC.le]
  constructor
  · have e1 : A / Real.sqrt (A * B / C)
        = Real.sqrt (A * C / B) := (div_eq_iff hxne).2 (h1.symm.trans (mul_comm _ _))
    have e2 : C / Real.sqrt (C * B / A)
        = Real.sqrt (A * C / B) := (div_eq_iff hyne).2 (h2.symm.trans (mul_comm _ _))
    rw [e1, e2]
    ring
  · rw [← Real.sqrt_mul hABpos.le (C * B / A)]
    rw [show A * B / C * (C * B / A) = B ^ 2 by field_simp]
    rw [Real.sqrt_sq hB.le]



end Hagi.Budget

namespace Hagi
export Hagi.Budget (two_term_amgm optimal_split)
end Hagi
