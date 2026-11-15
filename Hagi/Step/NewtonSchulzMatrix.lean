/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Step.NewtonPolar
import Hagi.Step.Muon

/-!
# Newton–Schulz matrix iterate — diagonal contraction (C296)

The matrix Newton–Schulz polar iterate `X ← X(3I − XᵀX)/2`
(cycle C296, tech-debt TD A8-F6-C254). The scalar certificate is
C231 (`Hagi.Step.nsStep`); this module lifts it to matrices on
the DIAGONAL subspace and proves orthogonal equivariance of the
iterate:

* `nsMatrixStep_diagonal` — on a diagonal input the iterate is
  diagonal with entries the scalar NS map of the input entries
  (honest matrix-multiplication computation, no functional
  calculus);
* `nsMatrixStep_diagonal_contraction` — for input entries in the
  scalar bracket `[0, 1]` the iterate acts as a contraction on
  `(n → ℝ)` with the sup norm: the hypothesis `hP` of the Muon
  bounds is DISCHARGED in the diagonal case;
* `nsMatrixStep_orth` — the iterate commutes with orthogonal
  left/right factors (`UᵀU = VᵀV = 1`), the transport ingredient
  for the general spectral route (see design note: the full
  spectral-norm statement needs a spectral-norm Matrix API absent
  from Mathlib here; NOT claimed);
* `muon_step_bound_ns_diagonal` — the consumer corollary:
  `muon_step_bound` with `P` the NS iterate of a bounded diagonal
  input, `hP` discharged.

Honest boundary: the contraction is stated for the sup norm on
`n → ℝ` (the operator norm of a diagonal matrix there is the max
of its entries' absolute values). The spectral-norm statement used
by the real Muon analyzer remains the documented follow-up.
-/

open Matrix

namespace Hagi.Step

/-- The matrix Newton–Schulz polar iterate
`X ← X(3I − XᵀX)/2`, entrywise-halved form
(defeq to the scalar-multiple form, see `nsMatrixStep_eq_smul`). -/
noncomputable def nsMatrixStep {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => (A * ((3 : ℝ) • (1 : Matrix n n ℝ) - Aᵀ * A)) i j / 2

/-- Bridge to the scalar-multiple form of the iterate. -/
theorem nsMatrixStep_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    nsMatrixStep A
      = (1 / 2 : ℝ) • (A * ((3 : ℝ) • (1 : Matrix n n ℝ) - Aᵀ * A)) := by
  ext i j
  simp [nsMatrixStep, Matrix.smul_apply, div_eq_mul_inv]
  ring

/-- DIAGONAL ACTION: on a diagonal input the NS iterate is diagonal
with entries the scalar NS map `Hagi.Step.nsStep` of the diagonal
entries — the scalar→matrix lift as a matrix-multiplication
computation. -/
theorem nsMatrixStep_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) :
    nsMatrixStep (Matrix.diagonal d)
      = Matrix.diagonal (fun i => Hagi.Step.nsStep (d i)) := by
  ext i j
  simp only [nsMatrixStep, Matrix.of_apply, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply, mul_ite]
  by_cases h : i = j
  · subst h
    simp only [ite_true]
    simp [Hagi.Step.nsStep, pow_two]
  · simp [h, Ne.symm h]

/-- DIAGONAL CONTRACTION: for a diagonal input with entries in the
scalar bracket `[0, 1]` the NS iterate is a contraction on
`(n → ℝ)` with the sup norm — the `hP` hypothesis of the Muon
bounds, discharged for the diagonal NS case. -/
theorem nsMatrixStep_diagonal_contraction {n : Type*} [Fintype n]
    [DecidableEq n] (d : n → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (z : n → ℝ) :
    ‖nsMatrixStep (Matrix.diagonal d) *ᵥ z‖ ≤ ‖z‖ := by
  have hentries : ∀ i, 0 ≤ Hagi.Step.nsStep (d i)
      ∧ Hagi.Step.nsStep (d i) ≤ 1 :=
    fun i =>
      ⟨Hagi.Step.nsStep_nonneg _ (hd i).1 (by nlinarith [(hd i).1, (hd i).2]),
       Hagi.Step.nsStep_le_one _ (hd i).1
         (by nlinarith [(hd i).1, (hd i).2])⟩
  rw [nsMatrixStep_diagonal]
  have hvec : (Matrix.diagonal (fun i => Hagi.Step.nsStep (d i)) *ᵥ z)
      = fun i => Hagi.Step.nsStep (d i) * z i := by
    funext i
    exact Matrix.mulVec_diagonal _ _ i
  rw [hvec]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr ?_
  intro i
  have habs : |Hagi.Step.nsStep (d i) * z i| ≤ |z i| := by
    have h0 : 0 ≤ Hagi.Step.nsStep (d i) := (hentries i).1
    have h1 : Hagi.Step.nsStep (d i) ≤ 1 := (hentries i).2
    have hmulle : |Hagi.Step.nsStep (d i)| * |z i| ≤ 1 * |z i| := by
      apply mul_le_mul_of_nonneg_right
      · rw [abs_of_nonneg h0]; exact h1
      · exact abs_nonneg _
    calc |Hagi.Step.nsStep (d i) * z i|
        ≤ |Hagi.Step.nsStep (d i)| * |z i| :=
          le_of_eq (abs_mul _ _)
      _ ≤ 1 * |z i| := hmulle
      _ = |z i| := by rw [one_mul]
  exact habs.trans (norm_le_pi_norm z i)

/-- ORTHOGONAL EQUIVARIANCE: the NS iterate commutes with
orthogonal left/right factors — the iterate of `U A Vᵀ` is
`U (iterate A) Vᵀ`. Pure ring bookkeeping (the transpose product
folds to `V (AᵀA) Vᵀ`; the scalar identity matrix commutes past an
orthogonal `V`). The transport ingredient for the general spectral
route; no existence claims here. -/
theorem nsMatrixStep_orth {n : Type*} [Fintype n] [DecidableEq n]
    (A U V : Matrix n n ℝ) (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    nsMatrixStep (U * A * Vᵀ) = U * nsMatrixStep A * Vᵀ := by
  have hVV : V * Vᵀ = 1 := by
    have hdet : IsUnit V.det := Matrix.isUnit_det_of_left_inverse hV
    rw [← Matrix.inv_eq_left_inv hV]
    exact Matrix.mul_nonsing_inv V hdet
  have hT : (U * A * Vᵀ)ᵀ * (U * A * Vᵀ) = V * (Aᵀ * A) * Vᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U (A * Vᵀ), hU, one_mul]
  have h3 : (3 : ℝ) • (1 : Matrix n n ℝ) - V * (Aᵀ * A) * Vᵀ
      = V * ((3 : ℝ) • (1 : Matrix n n ℝ) - Aᵀ * A) * Vᵀ := by
    have hV1 : V * ((3 : ℝ) • (1 : Matrix n n ℝ)) * Vᵀ
        = (3 : ℝ) • (1 : Matrix n n ℝ) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hVV]
    rw [Matrix.mul_sub, Matrix.sub_mul, hV1]
  rw [nsMatrixStep_eq_smul, nsMatrixStep_eq_smul, hT, h3]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Vᵀ V
      (((3 : ℝ) • (1 : Matrix n n ℝ) - Aᵀ * A) * Vᵀ),
    hV, one_mul, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

/-- CONSUMER: the Muon step bound with `P` the NS iterate of a
diagonal input with entries in the scalar bracket `[0, 1]` — the
`hP` hypothesis is discharged by
`nsMatrixStep_diagonal_contraction` (sup-norm statement). -/
theorem muon_step_bound_ns_diagonal {n : Type} [Fintype n]
    [DecidableEq n] (d : n → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (g : n → ℝ) :
    ‖muonDir (fun z => nsMatrixStep (Matrix.diagonal d) *ᵥ z) g‖
      ≤ ‖g‖ :=
  muon_step_bound _ g (fun z => nsMatrixStep_diagonal_contraction d hd z)

end Hagi.Step
