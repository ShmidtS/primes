/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Step.NewtonSchulzMatrix

/-!
# Newton–Schulz spectral-norm SVD transport (C297)

The documented follow-up of C296 (design note: the orthogonal
invariance of the spectral norm was the missing transport piece).
Route: the pinned Mathlib DOES provide a spectral-norm Matrix API
— the scoped `Matrix.Norms.L2Operator` norm transported from
`EuclideanSpace` operator norms (`Mathlib/Analysis/CStarAlgebra/
Matrix.lean`, a `CStarRing`: `‖Aᴴ * A‖ = ‖A‖²`). C296's "absent
from Mathlib" verdict was stale for this pin.

* `nsOrthogonal_mul_star_self` — companion `V Vᵀ = 1` of an
  orthogonal `VᵀV = 1` (det/unit route, as in C296);
* `nsSpectralNorm_orth_inv` — THE C296 missing piece: the L2
  operator (spectral) norm is invariant under orthogonal left/right
  multiplication, `‖U A Vᵀ‖₂ = ‖A‖₂` for `UᵀU = VᵀV = 1`;
* `ns_contraction_svd` — SVD-premise transport: for
  `A = U Σ Vᵀ` with singular values in the scalar bracket `[0,1]`
  the NS iterate has spectral norm ≤ 1 (C296 equivariance +
  invariance + the diagonal case);
* `muon_step_bound_ns_svd` — CONSUMER: the Muon step bound on
  `EuclideanSpace ℝ n` with `hP` discharged under the SVD premise.

Honest boundary: the SVD is a PREMISE (no real-SVD existence
formalized here); one NS step only (iterate-lifting is a
mechanical induction on `nsMatrixStep_orth`, not claimed); the
norm is the scoped `Matrix.Norms.L2Operator` instance (the
ambient default matrix norm elsewhere in Hagi is untouched).
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Hagi.Step

variable {n : Type} [Fintype n] [DecidableEq n]

/-- ORTHOGONAL COMPANION: `Vᵀ V = 1` implies `V Vᵀ = 1`
(determinant/unit bookkeeping, the C296 `nsMatrixStep_orth`
route). -/
theorem nsOrthogonal_mul_star_self (V : Matrix n n ℝ) (hV : Vᵀ * V = 1) :
    V * Vᵀ = 1 := by
  have hdet : IsUnit V.det := Matrix.isUnit_det_of_left_inverse hV
  rw [← Matrix.inv_eq_left_inv hV]
  exact Matrix.mul_nonsing_inv V hdet

/-- ORTHOGONAL INVARIANCE (the C296 missing piece): the spectral
(L2 operator) norm is invariant under orthogonal left and right
factors — `‖U A Vᵀ‖₂ = ‖A‖₂` for `UᵀU = VᵀV = 1`. Route: C*
identity `‖XᴴX‖ = ‖X‖²` (left factor peeling, square
cancellation) + adjoint symmetry `‖Aᴴ‖ = ‖A‖` (right factor
peeling). -/
theorem nsSpectralNorm_orth_inv (A U V : Matrix n n ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ‖U * A * Vᵀ‖ = ‖A‖ := by
  have hU' : Uᴴ * U = 1 := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hU
  have hleft : ∀ Y X : Matrix n n ℝ, Yᴴ * Y = 1 → ‖Y * X‖ = ‖X‖ := by
    intro Y X hY
    have hkey : ‖Y * X‖ * ‖Y * X‖ = ‖X‖ * ‖X‖ := by
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self,
        ← Matrix.l2_opNorm_conjTranspose_mul_self]
      have hstep : (Y * X)ᴴ * (Y * X) = Xᴴ * X := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc Xᴴ Yᴴ (Y * X),
          ← Matrix.mul_assoc Yᴴ Y X, hY, Matrix.one_mul]
      rw [hstep]
    have h1 : 0 ≤ ‖Y * X‖ := norm_nonneg _
    have h2 : 0 ≤ ‖X‖ := norm_nonneg _
    nlinarith [h1, h2, sq_nonneg (‖Y * X‖ - ‖X‖), hkey]
  -- right peeling: ‖X * W‖ = ‖X‖ from W * Wᴴ = 1
  have hright : ∀ X W : Matrix n n ℝ, W * Wᴴ = 1 → ‖X * W‖ = ‖X‖ := by
    intro X W hW
    rw [← Matrix.l2_opNorm_conjTranspose, Matrix.conjTranspose_mul,
      hleft Wᴴ Xᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hW),
      Matrix.l2_opNorm_conjTranspose]
  -- the right factor here is Vᵀ, whose companion is VᵀV = 1 itself
  have hW : Vᵀ * (Vᵀ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    exact hV
  exact (hright (U * A) Vᵀ hW).trans (hleft U A hU')

/-- SVD TRANSPORT CONTRACTION: for an input with a (premise-form)
SVD `A = U Σ Vᵀ` (`UᵀU = VᵀV = 1`, Σ diagonal with entries in the
scalar bracket `[0,1]`), the NS iterate has spectral norm ≤ 1.
Composition: C296 equivariance `nsMatrixStep_orth` first, then
peel `Vᵀ` (right), then peel `U` (left), then collapse via
`nsMatrixStep_diagonal` + `l2_opNorm_diagonal` (sup-norm RHS) +
the C231 scalar bracket. -/
theorem ns_contraction_svd (A U V : Matrix n n ℝ) (σ : n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i ∧ σ i ≤ 1)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hA : A = U * Matrix.diagonal σ * Vᵀ) :
    ‖nsMatrixStep A‖ ≤ 1 := by
  rw [hA, nsMatrixStep_orth (Matrix.diagonal σ) U V hU hV,
    nsSpectralNorm_orth_inv (nsMatrixStep (Matrix.diagonal σ)) U V hU hV,
    nsMatrixStep_diagonal, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  have hnn : 0 ≤ nsStep (σ i) := nsStep_nonneg _ (hσ i).1
    (by nlinarith [(hσ i).1, (hσ i).2])
  have hle : nsStep (σ i) ≤ 1 := nsStep_le_one _ (hσ i).1
    (by nlinarith [(hσ i).1, (hσ i).2])
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

/-- CONSUMER: the Muon step bound on `EuclideanSpace ℝ n` with
`hP` DISCHARGED under the SVD premise — the honest spectral Muon
bound. `P` is the NS iterate acting as a continuous linear map;
contraction follows from the operator-norm bound
`ns_contraction_svd` (one step; general Muon statements with `hP`
as an explicit hypothesis are untouched). -/
theorem muon_step_bound_ns_svd (A U V : Matrix n n ℝ) (σ : n → ℝ)
    (hσ : ∀ i, 0 ≤ σ i ∧ σ i ≤ 1)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1)
    (hA : A = U * Matrix.diagonal σ * Vᵀ)
    (g : EuclideanSpace ℝ n) :
    ‖muonDir
      (fun z => (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)
        (nsMatrixStep A)) z) g‖
      ≤ ‖g‖ := by
  refine muon_step_bound _ g fun z => ?_
  have h1 := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)
    (nsMatrixStep A)).le_opNorm z
  have h2 : ‖nsMatrixStep A‖ * ‖z‖ ≤ ‖z‖ :=
    mul_le_of_le_one_left (norm_nonneg z) (ns_contraction_svd A U V σ hσ hU hV hA)
  exact h1.trans h2

end Hagi.Step
