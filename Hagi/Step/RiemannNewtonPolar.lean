/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# Riemannian (covariant) Newton in polar coordinates (R385)

Polar metric `g = diag(1, r²)`; the covariant Hessian of a
function `f(r, θ)` carries the Christoffel correction
`+ r·∂f/∂r` in the θθ-entry (`Γ^θ_{rθ} = 1/r`, `Γ^r_{θθ} =
−r`). The naive coordinate Hessian (∂²θθ f = 0 for radial
f) is degenerate — the source of artificial oscillations
near the origin; the geometric step needs the correction.

**Formalized kernel** (no tensor API in Mathlib — verified
through Euclidean geometry): restrict the radial function
`F(x,y) = φ(‖(x,y)‖)` to the tangent line `s ↦ (x,y) + s·t`
(`t ⊥ (x,y)`, unit). Then `‖(x,y)+s·t‖ = √(r² + s²)` and

  h(s) := φ(√(r² + s²))  ⟹  h''(0) = φ'(r)/r.

This is exactly the covariant θθ-entry per unit arc length:
`(r·φ'(r)) / g_θθ = (r·φ'(r))/r² = φ'(r)/r` — the Christoffel
term is not an artifact but the true tangential curvature.

**Honest boundary**: the full covariant-Hessian matrix
identity (all four entries, coordinate-invariance) and the
oscillation theorem for the naive vs covariant Newton
dynamics are not formalized here; this file fixes the
essential θθ-correction. -/
theorem radial_tangential_curvature (φ : ℝ → ℝ) (g gg : ℝ → ℝ)
    (r : ℝ) (hr : 0 < r)
    (hφ : ∀ x, HasDerivAt φ (g x) x)
    (hg : ∀ x, HasDerivAt g (gg x) x) :
    HasDerivAt
      (fun s => deriv (fun s' => φ (Real.sqrt (r ^ 2 + s' ^ 2))) s)
      (g r / r) 0 := by
  set q : ℝ → ℝ := fun s => Real.sqrt (r ^ 2 + s ^ 2) with hqdef
  have hqpos : ∀ s, 0 < q s := by
    intro s
    have hsum : (0:ℝ) < r ^ 2 + s ^ 2 := by positivity
    simpa [hqdef] using Real.sqrt_pos.mpr hsum
  have hq : ∀ s, HasDerivAt q (s / q s) s := by
    intro s
    have hin : HasDerivAt (fun s' => r ^ 2 + s' ^ 2) (2 * s) s := by
      have h1 : HasDerivAt (fun x => x ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      simpa [sq] using h1.add_const (r ^ 2)
    have hc := (Real.hasDerivAt_sqrt (by positivity : (r ^ 2 + s ^ 2 : ℝ) ≠ 0)).comp s hin
    have hval : (1 / (2 * Real.sqrt (r ^ 2 + s ^ 2))) * (2 * s)
        = s / Real.sqrt (r ^ 2 + s ^ 2) := by
      field_simp
    rw [hval] at hc
    exact hc
  have hq0 : q 0 = r := by
    have : (0:ℝ) ≤ r ^ 2 := by positivity
    show Real.sqrt (r ^ 2 + 0 ^ 2) = r
    have h0 : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [h0, add_zero]
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg hr.le
  have hderiv : ∀ s, HasDerivAt (fun s' => φ (q s'))
      (g (q s) * (s / q s)) s := by
    intro s
    have hc := (hφ (q s)).comp s (hq s)
    simpa [Function.comp_def] using hc
  have hf1 : HasDerivAt (fun s => g (q s)) (gg r * (0 / r)) 0 := by
    have hc := (hg (q 0)).comp 0 (hq 0)
    rw [hq0] at hc
    rw [Function.comp_def] at hc
    exact hc
  have hf2 : HasDerivAt (id / q)
      ((1 * q 0 - id 0 * (0 / q 0)) / q 0 ^ 2) 0 :=
    (hasDerivAt_id 0).div (hq 0) (hqpos 0).ne'
  have heq : (fun s => deriv (fun s' => φ (q s')) s)
      = fun s => g (q s) * (s / q s) := funext fun s => (hderiv s).deriv
  rw [heq]
  have hmul := hf1.mul hf2
  simp only [Pi.mul_apply, Pi.div_apply, Function.id_def,
    zero_div, mul_zero, sub_zero, zero_mul, div_zero,
    mul_zero] at hmul
  convert hmul using 1
  rw [hq0]
  field_simp
  ring

