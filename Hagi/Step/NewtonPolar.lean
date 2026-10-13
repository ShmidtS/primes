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

end Hagi.Step
