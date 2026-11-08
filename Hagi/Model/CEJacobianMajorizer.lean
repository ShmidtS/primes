/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Model.CEQuantized

/-!
# Local cross-entropy majorizer from a Jacobian remainder

This module combines the proved finite-sup cross-entropy
perturbation bound with the sharp finite-range log-sum-exp majorizer and
the exact cross-entropy chain rule.  The endpoint is capped inside the
explicit local remainder ball.  Only the linearized logit displacement's
range is used; no range bound for the full nonlinear increment is assumed.
-/

set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Model.CEJacobianMajorizer

/-- A local second-order line majorizer for one-hot cross-entropy.

The linear term has the sign `A = -D(CE ∘ f)[d]`.  The quadratic term uses
the range of `J d` and the finite-sup norm of the nonlinear remainder at
`θ + η • d`; `η` is constrained to the supplied local ball. -/
theorem ceOneHot_local_line_majorize_of_jacobian_remainder
    {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype V] [Nonempty V]
    (f : E → V → ℝ) (J : E →L[ℝ] (V → ℝ)) (θ d : E) (y : V)
    (r R ρ A η : ℝ)
    (hf : HasFDerivAt f J θ)
    (hA : A = -(fderiv ℝ (fun w => Hagi.ceOneHot y (f w)) θ d))
    (hR : ∀ u v, (J d) u - (J d) v ≤ R)
    (hrem : ∀ w ∈ Metric.closedBall θ r,
      ‖f w - f θ - J (w - θ)‖ ≤ ρ * ‖w - θ‖ ^ 2)
    (hη : 0 ≤ η) (hcap : η * ‖d‖ ≤ r) :
    Hagi.ceOneHot y (f (θ + η • d)) ≤
      Hagi.ceOneHot y (f θ) - η * A +
        η ^ 2 * (R ^ 2 / 8 + 2 * ρ * ‖d‖ ^ 2) := by
  classical
  let q : V → ℝ := η • J d
  let e : V → ℝ := f (θ + η • d) - f θ - q
  have hw : θ + η • d ∈ Metric.closedBall θ r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hη] using hcap
  have he_norm : ‖e‖ ≤ ρ * η ^ 2 * ‖d‖ ^ 2 := by
    have h := hrem (θ + η • d) hw
    simpa only [e, q, add_sub_cancel_left, map_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hη, mul_pow, mul_assoc] using h
  have he_abs (v : V) : |e v| ≤ ρ * η ^ 2 * ‖d‖ ^ 2 := by
    calc
      |e v| = ‖e v‖ := (Real.norm_eq_abs (e v)).symm
      _ ≤ ‖e‖ := norm_le_pi_norm e v
      _ ≤ ρ * η ^ 2 * ‖d‖ ^ 2 := he_norm
  have hperturb :
      Hagi.ceOneHot y (f (θ + η • d)) ≤
        Hagi.ceOneHot y (fun v => f θ v + q v) +
          2 * (ρ * η ^ 2 * ‖d‖ ^ 2) := by
    apply CEQuantized.ceOneHot_le_of_abs_sub_le y
      (f (θ + η • d)) (fun v => f θ v + q v)
      (ρ * η ^ 2 * ‖d‖ ^ 2)
    intro v
    have hdiff : f (θ + η • d) v - (f θ v + q v) = e v := by
      simp only [e, Pi.sub_apply]
      ring
    rw [hdiff]
    exact he_abs v
  have hrange : ∀ u v,
      ((f θ u + q u) - f θ u) - ((f θ v + q v) - f θ v) ≤ η * R := by
    intro u v
    calc
      ((f θ u + q u) - f θ u) - ((f θ v + q v) - f θ v) =
          η * ((J d) u - (J d) v) := by
        simp only [q, Pi.smul_apply, smul_eq_mul]
        ring
      _ ≤ η * R := mul_le_mul_of_nonneg_left (hR u v) hη
  have hlse := Hagi.Energy.lse_shift_upper (f θ)
    (fun v => f θ v + q v) (η * R) hrange
  have hmid :
      Hagi.ceOneHot y (fun v => f θ v + q v) ≤
        Hagi.ceOneHot y (f θ) +
          (∑ v, (Hagi.Prelude.softDef (f θ) v -
            if v = y then 1 else 0) * q v) + (η * R) ^ 2 / 8 := by
    have hone : (∑ v, (if v = y then (1 : ℝ) else 0) * q v) = q y := by
      simp
    simp only [Hagi.ceOneHot, Hagi.Core.ceOneHot, Hagi.Core.lse,
      sub_mul, Finset.sum_sub_distrib, hone]
    change Real.log (∑ v, Real.exp (f θ v + q v)) ≤ _ at hlse
    simp only [Hagi.Energy.smax, add_sub_cancel_left] at hlse
    linarith
  have hlinear :
      (∑ v, (Hagi.Prelude.softDef (f θ) v -
        if v = y then 1 else 0) * q v) = -η * A := by
    calc
      (∑ v, (Hagi.Prelude.softDef (f θ) v -
          if v = y then 1 else 0) * q v) =
          η * ∑ v, (Hagi.Prelude.softDef (f θ) v -
            if v = y then 1 else 0) * (J d) v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        simp only [q, Pi.smul_apply, smul_eq_mul]
        ring
      _ = η * fderiv ℝ (fun w => Hagi.ceOneHot y (f w)) θ d := by
        rw [CEGradient.fderiv_ceOneHot_comp_apply f J θ d y hf]
      _ = -η * A := by
        rw [hA]
        ring
  calc
    Hagi.ceOneHot y (f (θ + η • d)) ≤
        Hagi.ceOneHot y (fun v => f θ v + q v) +
          2 * (ρ * η ^ 2 * ‖d‖ ^ 2) := hperturb
    _ ≤ (Hagi.ceOneHot y (f θ) +
          (∑ v, (Hagi.Prelude.softDef (f θ) v -
            if v = y then 1 else 0) * q v) + (η * R) ^ 2 / 8) +
          2 * (ρ * η ^ 2 * ‖d‖ ^ 2) :=
      add_le_add hmid (le_refl _)
    _ = Hagi.ceOneHot y (f θ) - η * A +
          η ^ 2 * (R ^ 2 / 8 + 2 * ρ * ‖d‖ ^ 2) := by
      rw [hlinear]
      ring

end Hagi.Model.CEJacobianMajorizer
