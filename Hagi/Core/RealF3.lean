/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.DFT3

set_option linter.style.header false

/-!
# The real 6x6 lift of the F3 transform: the interleaving isometry

The complex F₃ transform of `Hagi.Core.DFT3` transported to real
(re, im)-interleaved coordinates: `interleave z = ![z.re, z.im]`,
lifted branch-major to `interleave3 : (Fin 3 → ℂ) → (Fin 3 × Fin 2 → ℝ)`.

* `interleave_norm` — the lift is an isometry: the real inner
  product of the interleaved images equals `∑ a, ‖z a‖ ^ 2`.
* `reCharMat` — the canonical 6×6 real character matrix built
  from `chi3`, with the conjugation identity `interleave_char_mul`:
  the interleaved image of the character multiplication equals
  `reCharMat *ᵥ interleave3 z`; `reUnitMat` is its scaling by
  `1 / Real.sqrt 3`.
* `reBlock_mul_transpose` — block algebra
  `reBlock c * (reBlock d)ᵀ = reBlock (c * star d)`.

The orthogonality of `reUnitMat` is not yet proven here.
-/

open scoped Matrix

namespace Hagi

namespace RealF3

open Hagi

/-- The interleaving of a complex number as a real pair. -/
def interleave (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

/-- The branch-major, pair-interleaved lift of a complex 3-vector
to ℝ⁶: coordinate `(a, p)` is `p = 0 → re`, `p = 1 → im` of branch
`a`. -/
def interleave3 (z : Fin 3 → ℂ) : Fin 3 × Fin 2 → ℝ :=
  fun ab => interleave (z ab.1) ab.2

/-- The isometry: the real inner product of the interleaved
vectors is the real part of the complex inner product. -/
theorem interleave_norm (z : Fin 3 → ℂ) :
    (∑ ab : Fin 3 × Fin 2, interleave3 z ab * interleave3 z ab)
      = ∑ a, ‖z a‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hpair : ∑ p : Fin 2, interleave3 z (a, p) * interleave3 z (a, p)
      = (z a).re * (z a).re + (z a).im * (z a).im := by
    simp only [interleave3, interleave]
    rw [Fin.sum_univ_two]
    rfl
  rw [hpair]
  have hmod : ‖z a‖ ^ 2 = (z a).re * (z a).re + (z a).im * (z a).im := by
    have hnnsq : (0:ℝ) ≤ (z a).re * (z a).re + (z a).im * (z a).im :=
      add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    rw [Complex.norm_def, Complex.normSq_apply, pow_two,
      Real.mul_self_sqrt hnnsq]
  rw [hmod]

/-- The canonical real 6×6 block for one character value: the
2×2 block `c.re • (1 0; 0 1) + c.im • (0 -1; 1 0)` — the real
representation of multiplication by the complex number `c`. -/
noncomputable def reBlock (c : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c.re, -c.im; c.im, c.re]

/-- The coercion of a branch index into the character domain. -/
def branchZ (a : Fin 3) : ZMod 3 := (a.val : ZMod 3)

/-- The real 6×6 *character* matrix (no F₃ normalization): the
transported basis-change action, branch-major blocks
`reBlock (chi3 (a - b))`. -/
noncomputable def reCharMat : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ :=
  fun ab cd =>
    reBlock (chi3 (-(branchZ ab.1 * branchZ cd.1))) ab.2 cd.2

/-- The real 6×6 transport scaled by the F₃ normalization
`1 / Real.sqrt 3`. -/
noncomputable def reUnitMat : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ :=
  (1 / Real.sqrt 3) • reCharMat

/-- **The conjugation identity (the transported basis change).**
The interleaved image of the full character multiplication
`w a = ∑_c chi3 (a - c) * z c` equals the real character matrix
applied to the interleaved input — the real matrix realizes the
complex character action. -/
theorem interleave_char_mul (z : Fin 3 → ℂ) :
    interleave3 (fun a => ∑ c, chi3 (-(branchZ a * branchZ c)) * z c)
      = reCharMat *ᵥ interleave3 z := by
  ext ⟨a, p⟩
  fin_cases p
  · -- p = 0 (the re-coordinate)
    change (∑ c, chi3 (-(branchZ a * branchZ c)) * z c).re
      = ∑ cd : Fin 3 × Fin 2,
          reBlock (chi3 (-(branchZ a * branchZ (cd : Fin 3 × Fin 2).1))) 0 cd.2
            * interleave3 z cd
    rw [Fintype.sum_prod_type]
    have hsumre : (∑ c, chi3 (-(branchZ a * branchZ c)) * z c).re
        = ∑ c, (chi3 (-(branchZ a * branchZ c)) * z c).re := by
      rw [Fin.sum_univ_three, Fin.sum_univ_three, Complex.add_re,
        Complex.add_re]
    rw [hsumre]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fin.sum_univ_two]
    simp only [interleave3, interleave,
      Matrix.cons_val_one]
    simp [reBlock]
    ring
  · -- p = 1 (the im-coordinate)
    change (∑ c, chi3 (-(branchZ a * branchZ c)) * z c).im
      = ∑ cd : Fin 3 × Fin 2,
          reBlock (chi3 (-(branchZ a * branchZ (cd : Fin 3 × Fin 2).1))) 1 cd.2
            * interleave3 z cd
    rw [Fintype.sum_prod_type]
    have hsumim : (∑ c, chi3 (-(branchZ a * branchZ c)) * z c).im
        = ∑ c, (chi3 (-(branchZ a * branchZ c)) * z c).im := by
      rw [Fin.sum_univ_three, Fin.sum_univ_three, Complex.add_im,
        Complex.add_im]
    rw [hsumim]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fin.sum_univ_two]
    simp only [interleave3, interleave,
      Matrix.cons_val_one]
    simp [reBlock]
    ring

/-!
The orthogonality of `reUnitMat` is documented here but not yet
proven: the block algebra reduces `R Rᵀ` to
`(1/3) ∑_c reBlock (chi3 (c * (a - b)))`, and the character
orthogonality (`sum_chi3_eq_zero`) collapses the sum to `3` at
`a = b` and `0` otherwise, giving `R Rᵀ = 1`.
-/

/-- Block algebra: `reBlock c * (reBlock d)ᵀ = reBlock (c * star d)`
— the 2×2 real blocks compose under complex multiplication. -/
theorem reBlock_mul_transpose (c d : ℂ) :
    (reBlock c : Matrix (Fin 2) (Fin 2) ℝ) * (reBlock d)ᵀ = reBlock (c * star d) := by
  ext i j
  simp only [reBlock, Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    ring

end RealF3

end Hagi
