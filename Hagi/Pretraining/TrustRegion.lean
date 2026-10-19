/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
import Hagi.Core.Hadamard

open scoped Matrix

set_option linter.style.header false

/-!
# Spectral trust region — orthogonalized optimizer steps (Muon/ANVIL)

The speedrun recipe trains its block matrices with an
orthogonalized-momentum update (`anvil_lr` on block matrices). The
theory anchor (ask.sciencemadereadable: "Muon Optimizes Under
Spectral Norm Constraints", arXiv:2506.15054; "A Note on the
Convergence of Muon", arXiv:2502.02900): the orthogonalized step
lives under a SPECTRAL trust region — the update direction has
unit operator norm, so the step radius IS the step size.

Exact statements (elementary, no approximation):

* `hadamardRows_sup_bound` — for row-orthonormal `Q`
  (`Q * Qᵀ = 1`), every coordinate of the update direction
  `Q *ᵥ δ` is bounded in absolute value by the L2 norm of `δ`
  (rows have unit length; Cauchy–Schwarz via
  `sum_mul_sq_le_sq_mul_sq`): the orthogonalized step moves each
  weight coordinate by at most `η * ‖δ‖₂`;
* `orthonormal_mulVec_isometry` — full Parseval: a row-orthonormal
  square `Q` preserves the L2 norm of the credit vector
  (`Qᵀ * Q = 1` by invertibility): orthogonalized momentum neither
  amplifies nor damps any direction it moves.
-/

namespace Hagi.Pretraining

/-- Auxiliary: a row-orthonormal square matrix satisfies
`Qᵀ * Q = 1` (columns are orthonormal too — invertibility). -/
theorem transpose_mul_self_of_mul_transpose {m : Type*} [Fintype m]
    [DecidableEq m] (Q : Matrix m m ℝ) (hQ : Q * Qᵀ = 1) :
    Qᵀ * Q = 1 := by
  classical
  have hdet : Q.det ≠ 0 := by
    intro h0
    have h2 : (Q * Qᵀ).det = 1 := by rw [hQ]; simp
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at h2
    norm_num at h2
  have hUd : IsUnit Q.det := IsUnit.mk0 Q.det hdet
  have hU : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr hUd
  have hinv : Qᵀ = Q⁻¹ := by
    rw [← Matrix.mul_one Q⁻¹, ← hQ, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul Q hUd, Matrix.one_mul]
  rw [hinv, Matrix.nonsing_inv_mul Q hUd]

/-- **Per-coordinate trust-region bound** (run.py/ANVIL: the
orthogonalized update direction moves each weight coordinate by at
most the L2 norm of the credit vector): for row-orthonormal `Q`,
every coordinate of `Q *ᵥ δ` satisfies
`|(Q *ᵥ δ) i| ≤ ‖δ‖₂`. -/
theorem hadamardRows_sup_bound {m : Type*} [Fintype m] [DecidableEq m]
    (Q : Matrix m m ℝ) (δ : m → ℝ) (hQ : Q * Qᵀ = 1) (i : m) :
    |(Q *ᵥ δ) i| ≤ Real.sqrt (∑ j, δ j * δ j) := by
  classical
  have hdiag : ∑ j, Q i j * Q i j = 1 := by
    have h := congrArg (fun M : Matrix m m ℝ => M i i) hQ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
      at h
    simpa using h
  have hnn : (0:ℝ) ≤ ∑ j, δ j * δ j :=
    Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hcs : ((Q *ᵥ δ) i) ^ 2 ≤ ∑ j, δ j * δ j := by
    have hx : (Q *ᵥ δ) i = ∑ j, Q i j * δ j := rfl
    have hcsl := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (fun j => Q i j) (fun j => δ j)
    rw [hx]
    have hcsl' : (∑ j, Q i j * δ j) ^ 2
        ≤ (∑ j, Q i j * Q i j) * ∑ j, δ j * δ j := by
      simpa [sq, mul_pow] using hcsl
    rw [hdiag, one_mul] at hcsl'
    exact hcsl'
  have hkey : ((Q *ᵥ δ) i) ^ 2 ≤ (Real.sqrt (∑ j, δ j * δ j)) ^ 2 := by
    rw [Real.sq_sqrt hnn]
    exact hcs
  have h2 := sq_le_sq.mp hkey
  rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at h2

/-- **Orthogonalized momentum is an isometry** (Parseval): for a
row-orthonormal square `Q`, the update direction `Q *ᵥ δ` has
exactly the same L2 norm as the credit vector `δ`. -/
theorem orthonormal_mulVec_isometry {m : Type*} [Fintype m]
    [DecidableEq m] (Q : Matrix m m ℝ) (δ : m → ℝ) (hQ : Q * Qᵀ = 1) :
    ∑ i, (Q *ᵥ δ) i * (Q *ᵥ δ) i = ∑ j, δ j * δ j := by
  classical
  have hTQ := transpose_mul_self_of_mul_transpose Q hQ
  have hstep : ∑ i, (Q *ᵥ δ) i * (Q *ᵥ δ) i
      = δ ⬝ᵥ (Qᵀ * Q) *ᵥ δ := by
    have hdot : ∑ i, (Q *ᵥ δ) i * (Q *ᵥ δ) i
        = (Q *ᵥ δ) ⬝ᵥ (Q *ᵥ δ) := rfl
    rw [hdot]
    rw [← Matrix.dotProduct_transpose_mulVec Q δ (Q *ᵥ δ),
      ← Matrix.mulVec_mulVec]
  rw [hstep, hTQ, Matrix.one_mulVec]
  rfl

end Hagi.Pretraining
