/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# Newton–polar iteration, scalar core (R379)

The scalar engine of the Newton polar-factorization
iteration (Higham 1986 quadratic convergence; plan §2
Muon two-level structure — exact O_t = UVᵀ vs NS
approximation with explicit error):

  x ↦ (x + x⁻¹)/2,   x_{k+1} − 1 = (x_k − 1)² / (2 x_k).

The error recursion is EXACTLY quadratic — the mechanism
behind Higham's convergence analysis; the scaling step
(Byers–Xu) only keeps x in the monotone branch x ≥ 1 where
|newtonStep x − 1| ≤ |x − 1|²/2.
-/

open Real

namespace Hagi.Step

noncomputable def newtonStep (x : ℝ) : ℝ := (x + x⁻¹) / 2

theorem newton_polar_scalar_error (x : ℝ) (hx : 0 < x) :
    newtonStep x - 1 = (x - 1)^2 / (2 * x) := by
  unfold newtonStep
  field_simp
  ring

theorem newton_error_ratio (x : ℝ) (hx : 1 ≤ x) :
    abs (newtonStep x - 1) ≤ (x - 1)^2 / 2 := by
  have hx0 : 0 < x := by linarith
  rw [newton_polar_scalar_error x hx0, abs_of_nonneg (by positivity)]
  refine (div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * x)
    (by norm_num : (0:ℝ) < 2)).mpr ?_
  nlinarith [sq_nonneg (x - 1)]

/-!
### T-step quadratic convergence (R380)

Composing the scalar error recursion over `T` Newton steps:
the error exponent DOUBLES each step —

  |newtonIter x₀ T − 1| ≤ 2·((x₀ − 1)/2)^{2^T}

— the formal quadratic-convergence rate of the Newton polar
iteration (Higham 1986), with the branch invariant
`newtonStep x ≥ 1` (AM–GM) kept by Byers–Xu scaling. -/
theorem newtonStep_ge_one (x : ℝ) (hx : 0 < x) :
    1 ≤ Hagi.Step.newtonStep x := by
  unfold Hagi.Step.newtonStep
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ (by linarith : (x:ℝ) ≠ 0)
  nlinarith [sq_nonneg (x - 1)]

noncomputable def newtonIter (x₀ : ℝ) : ℕ → ℝ :=
  fun T => (Hagi.Step.newtonStep^[T]) x₀

theorem newton_polar_convergence (x₀ : ℝ) (hx₀ : 1 ≤ x₀) (T : ℕ) :
    abs (newtonIter x₀ T - 1) ≤ 2 * ((x₀ - 1)/2) ^ (2 ^ T) := by
  induction T generalizing x₀ with
  | zero =>
      unfold newtonIter
      simp only [Function.iterate_zero_apply]
      rw [abs_of_nonneg (by linarith), pow_zero, pow_one]
      field_simp
      exact le_rfl
  | succ T ih =>
      have hx0 : (0:ℝ) < x₀ := by linarith
      have hge1 : 1 ≤ Hagi.Step.newtonStep x₀ := newtonStep_ge_one x₀ hx0
      have hstep := Hagi.Step.newton_error_ratio x₀ hx₀
      -- iterate shift
      have hiter : newtonIter x₀ (T+1) = newtonIter (Hagi.Step.newtonStep x₀) T := by
        unfold newtonIter
        rw [Function.iterate_succ_apply]
      rw [hiter]
      have hnext := ih (Hagi.Step.newtonStep x₀) hge1
      -- |e| bound chain
      have hpos : (0:ℝ) ≤ newtonStep x₀ - 1 := by
        have := newtonStep_ge_one x₀ hx0
        linarith
      rw [abs_of_nonneg hpos] at hstep
      have hsq : (newtonStep x₀ - 1) / 2 ≤ ((x₀ - 1) / 2) ^ 2 := by
        rw [div_pow]
        norm_num
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 4)]
        rw [show Hagi.Step.newtonStep x₀ - 1 = (x₀ - 1) ^ 2 / (2 * x₀) from
          Hagi.Step.newton_polar_scalar_error x₀ hx0]
        field_simp
        nlinarith [sq_nonneg (x₀ - 1), sq_nonneg (x₀ + 1)]
      -- final pow composition
      have hnn : (0:ℝ) ≤ (newtonStep x₀ - 1) / 2 := by
        have := newtonStep_ge_one x₀ hx0
        positivity
      have hmono : ((newtonStep x₀ - 1) / 2) ^ (2 ^ T)
          ≤ (((x₀ - 1) / 2) ^ 2) ^ (2 ^ T) :=
        pow_le_pow_left₀ hnn hsq (2 ^ T)
      have hcomb : 2 * ((newtonStep x₀ - 1) / 2) ^ (2 ^ T)
          ≤ 2 * ((x₀ - 1) / 2) ^ (2 ^ (T + 1)) := by
        have hexp : 2 ^ (T + 1) = 2 * 2 ^ T := by rw [pow_succ]; ring
        rw [hexp, pow_mul]
        exact mul_le_mul_of_nonneg_left hmono (by norm_num)
      calc abs (newtonIter (Hagi.Step.newtonStep x₀) T - 1)
          ≤ 2 * ((newtonStep x₀ - 1) / 2) ^ (2 ^ T) := hnext
        _ ≤ 2 * ((x₀ - 1) / 2) ^ (2 ^ (T + 1)) := hcomb

end Hagi.Step
