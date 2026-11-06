/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.GatedCEGradient

/-!
# Global second-order control for the scalar hyperbolic tangent

This module defines `sechSq x = 1 - tanh(x)^2`, identifies it with the
reciprocal squared hyperbolic cosine, and bounds its derivative globally.
Two mean-value arguments then give a conservative second-order Taylor
remainder bound for `tanh`.  These are scalar analytic estimates only; no
optimizer safe-step or convergence claim is made.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.TanhTaylor

open Hagi.Model.GatedCEGradient

/-- The derivative of `Real.tanh`, written without a denominator. -/
noncomputable def sechSq (x : ℝ) : ℝ :=
  1 - Real.tanh x ^ 2

/-- `sechSq` agrees with the reciprocal squared hyperbolic cosine. -/
theorem sechSq_eq_coshInvSq (x : ℝ) :
    sechSq x = 1 / (Real.cosh x) ^ 2 := by
  unfold sechSq
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- The exact derivative of `sechSq`. -/
theorem hasDerivAt_sechSq (x : ℝ) :
    HasDerivAt sechSq (-2 * Real.tanh x * sechSq x) x := by
  change HasDerivAt (fun z => 1 - Real.tanh z ^ 2)
    (-2 * Real.tanh x * sechSq x) x
  rw [sechSq_eq_coshInvSq]
  convert (hasDerivAt_tanh_coshInvSq x).pow 2 |>.const_sub 1 using 1
  ring

/-- The derivative of `sechSq` has global norm bound `2`. -/
theorem norm_deriv_sechSq_le (x : ℝ) : ‖deriv sechSq x‖ ≤ (2 : ℝ) := by
  rw [(hasDerivAt_sechSq x).deriv, Real.norm_eq_abs, sechSq_eq_coshInvSq]
  have ht := Real.abs_tanh_lt_one x
  have hs0 : 0 ≤ 1 / (Real.cosh x) ^ 2 := by positivity
  have hs1 : 1 / (Real.cosh x) ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity : (0 : ℝ) < (Real.cosh x) ^ 2)).2
    nlinarith [Real.cosh_sq_sub_sinh_sq x, sq_nonneg (Real.sinh x)]
  have habs : |1 / (Real.cosh x) ^ 2| = 1 / (Real.cosh x) ^ 2 := abs_of_nonneg hs0
  rw [abs_mul, abs_mul, habs]
  norm_num
  calc
    2 * |Real.tanh x| * (Real.cosh x ^ 2)⁻¹
        ≤ 2 * 1 * (Real.cosh x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht.le (by norm_num)) (by simpa [one_div] using hs0)
    _ ≤ 2 * 1 * 1 :=
      mul_le_mul_of_nonneg_left (by simpa [one_div] using hs1) (by positivity)
    _ = 2 := by norm_num

/-- `sechSq` is globally `2`-Lipschitz. -/
theorem abs_sechSq_sub_le (x y : ℝ) :
    |sechSq x - sechSq y| ≤ 2 * |x - y| := by
  have hdiff (z : ℝ) : DifferentiableAt ℝ sechSq z :=
    (hasDerivAt_sechSq z).differentiableAt
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _hz => hdiff z) (fun z _hz => norm_deriv_sechSq_le z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa [Real.norm_eq_abs, abs_sub_comm, mul_comm] using h

/-- Second-order Taylor remainder for `tanh`, with global constant `2`. -/
theorem abs_tanh_taylor_sub_le (x y : ℝ) :
    |Real.tanh y - Real.tanh x - sechSq x * (y - x)| ≤ 2 * (y - x) ^ 2 := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · obtain ⟨c, hc, hmean⟩ := exists_hasDerivAt_eq_slope Real.tanh sechSq hxy
      (fun z _hz => (hasDerivAt_tanh_coshInvSq z).continuousAt.continuousWithinAt)
      (fun z _hz =>
        (hasDerivAt_tanh_coshInvSq z).congr_deriv (sechSq_eq_coshInvSq z).symm)
    have hyx : 0 < y - x := sub_pos.mpr hxy
    have htanh : Real.tanh y - Real.tanh x = sechSq c * (y - x) := by
      calc
        Real.tanh y - Real.tanh x =
            ((Real.tanh y - Real.tanh x) / (y - x)) * (y - x) :=
          (div_mul_cancel₀ _ (sub_ne_zero.mpr hxy.ne')).symm
        _ = sechSq c * (y - x) := by rw [← hmean]
    have hid : Real.tanh y - Real.tanh x - sechSq x * (y - x) =
        (sechSq c - sechSq x) * (y - x) := by
      rw [htanh]
      ring
    rw [hid, abs_mul]
    have hcx : |c - x| ≤ |y - x| := by
      rw [abs_of_pos (sub_pos.mpr hc.1), abs_of_pos hyx]
      exact sub_le_sub_right hc.2.le x
    calc
      |sechSq c - sechSq x| * |y - x| ≤ (2 * |c - x|) * |y - x| :=
        mul_le_mul_of_nonneg_right (abs_sechSq_sub_le c x) (abs_nonneg _)
      _ ≤ (2 * |y - x|) * |y - x| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcx (by norm_num)) (abs_nonneg _)
      _ = 2 * (y - x) ^ 2 := by
        calc
          (2 * |y - x|) * |y - x| = 2 * |y - x| ^ 2 := by ring
          _ = 2 * (y - x) ^ 2 := by rw [sq_abs]
  · subst y
    simp
  · obtain ⟨c, hc, hmean⟩ := exists_hasDerivAt_eq_slope Real.tanh sechSq hxy
      (fun z _hz => (hasDerivAt_tanh_coshInvSq z).continuousAt.continuousWithinAt)
      (fun z _hz =>
        (hasDerivAt_tanh_coshInvSq z).congr_deriv (sechSq_eq_coshInvSq z).symm)
    have hyx : 0 < x - y := sub_pos.mpr hxy
    have htanh : Real.tanh x - Real.tanh y = sechSq c * (x - y) := by
      calc
        Real.tanh x - Real.tanh y =
            ((Real.tanh x - Real.tanh y) / (x - y)) * (x - y) :=
          (div_mul_cancel₀ _ (sub_ne_zero.mpr hxy.ne')).symm
        _ = sechSq c * (x - y) := by rw [← hmean]
    have htanhyx : Real.tanh y - Real.tanh x = sechSq c * (y - x) := by
      calc
        Real.tanh y - Real.tanh x = -(Real.tanh x - Real.tanh y) := by ring
        _ = -(sechSq c * (x - y)) := by rw [← htanh]
        _ = sechSq c * (y - x) := by ring
    have hid : Real.tanh y - Real.tanh x - sechSq x * (y - x) =
        (sechSq c - sechSq x) * (y - x) := by
      rw [htanhyx]
      ring
    rw [hid, abs_mul]
    have hcx : |c - x| ≤ |y - x| := by
      rw [abs_of_neg (sub_neg.mpr hc.2), abs_of_neg (sub_neg.mpr hxy)]
      linarith [hc.1]
    calc
      |sechSq c - sechSq x| * |y - x| ≤ (2 * |c - x|) * |y - x| :=
        mul_le_mul_of_nonneg_right (abs_sechSq_sub_le c x) (abs_nonneg _)
      _ ≤ (2 * |y - x|) * |y - x| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcx (by norm_num)) (abs_nonneg _)
      _ = 2 * (y - x) ^ 2 := by
        calc
          (2 * |y - x|) * |y - x| = 2 * |y - x| ^ 2 := by ring
          _ = 2 * (y - x) ^ 2 := by rw [sq_abs]

end Hagi.Model.TanhTaylor
