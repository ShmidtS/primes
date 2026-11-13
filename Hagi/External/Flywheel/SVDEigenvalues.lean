import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup
import Hagi.External.Flywheel.SVDCore

/-!
# SVDEigenvalues

Singular-value properties and eigenvalue machinery: charpoly similarity-invariance helpers and eigenvalues of Hermitian squares `Aᴴ A`.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

namespace Matrix.SVD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Properties of Singular Values -/

/-- The eigenvalues of A * Aᴴ equal the eigenvalues of Aᴴ * A.
    This is a direct consequence of `charpoly_mul_comm` which states that
    (A * B).charpoly = (B * A).charpoly for any square matrices A, B.
    Combined with `eigenvalues_eq_eigenvalues_iff` for Hermitian matrices,
    this gives pointwise equality of eigenvalues. -/
theorem eigenvalues_self_mul_conjTranspose_eq_conjTranspose_mul_self (A : Matrix n n ℂ) :
    (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvalues =
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues := by
  rw [IsHermitian.eigenvalues_eq_eigenvalues_iff]
  exact charpoly_mul_comm A Aᴴ

/-- The singular values of Aᴴ equal the singular values of A.

    **Proof outline:**
    - singularValues(Aᴴ) = sqrt(eigenvalues((Aᴴ)ᴴ * Aᴴ)) = sqrt(eigenvalues(A * Aᴴ))
    - singularValues(A) = sqrt(eigenvalues(Aᴴ * A))
    - By `charpoly_mul_comm`: (A * Aᴴ).charpoly = (Aᴴ * A).charpoly
    - For Hermitian matrices with equal charpoly, eigenvalues are equal pointwise
    - Therefore singularValues(Aᴴ) = singularValues(A) -/
theorem singularValues_conjTranspose (A : Matrix n n ℂ) :
    singularValues (conjTranspose A) = singularValues A := by
  ext i
  simp only [singularValues]
  -- Goal: sqrt(eigenvalues((Aᴴ)ᴴ * Aᴴ) i) = sqrt(eigenvalues(Aᴴ * A) i)
  -- Since (Aᴴ)ᴴ = A, this becomes: sqrt(eigenvalues(A * Aᴴ) i) = sqrt(eigenvalues(Aᴴ * A) i)

  -- Step 1: (Aᴴ)ᴴ * Aᴴ = A * Aᴴ (by conjTranspose_conjTranspose)
  have h_matrix_eq : conjTranspose (conjTranspose A) * conjTranspose A = A * conjTranspose A := by
    rw [conjTranspose_conjTranspose]

  -- Step 2: eigenvalues of (Aᴴ)ᴴ * Aᴴ = eigenvalues of A * Aᴴ (same matrix!)
  have h1 : (posSemidef_conjTranspose_mul_self (Aᴴ)).isHermitian.eigenvalues i =
            (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvalues i := by
    have h_charpoly : (conjTranspose (conjTranspose A) * conjTranspose A).charpoly =
                      (A * conjTranspose A).charpoly := by
      rw [h_matrix_eq]
    have := IsHermitian.eigenvalues_eq_eigenvalues_iff
        (posSemidef_conjTranspose_mul_self (Aᴴ)).isHermitian
        (posSemidef_self_mul_conjTranspose A).isHermitian
    rw [this.mpr h_charpoly]

  -- Step 3: eigenvalues of A * Aᴴ = eigenvalues of Aᴴ * A (by charpoly_mul_comm)
  have h2 : (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvalues i =
            (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := by
    exact congrFun (eigenvalues_self_mul_conjTranspose_eq_conjTranspose_mul_self A) i

  rw [h1, h2]

/-! ### Helper lemmas for characteristic polynomial similarity invariance -/

/-- Scalar matrices commute with all matrices. -/
private lemma scalar_mul_eq_mul_scalar' (M : Matrix n n (Polynomial ℂ)) (x : Polynomial ℂ) :
    M * scalar n x = scalar n x * M := by
  have h : Commute (scalar n x) M := Matrix.scalar_commute x (fun r' => mul_comm x r') M
  exact h.symm.eq

/-- The characteristic matrix expressed as scalar minus map. -/
private lemma charmatrix_eq_scalar_sub_map (M : Matrix n n ℂ) :
    M.charmatrix = scalar n Polynomial.X - M.map Polynomial.C := by
  ext i j
  simp only [charmatrix_apply, Matrix.sub_apply, scalar_apply, diagonal, of_apply, map_apply]

/-- Ring homomorphism map preserves inverses for invertible matrices. -/
private lemma map_inv_of_isUnit {R S : Type*} [CommRing R] [CommRing S]
    (M : Matrix n n R) (f : R →+* S) (hM : IsUnit M.det) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  have h1 : M.map f = f.mapMatrix M := by ext; simp [RingHom.mapMatrix_apply]
  have h2 : M⁻¹.map f = f.mapMatrix M⁻¹ := by ext; simp [RingHom.mapMatrix_apply]
  have hMf : IsUnit (M.map f).det := by
    rw [h1, ← RingHom.map_det f M]
    exact hM.map f
  rw [h1, h2]
  symm
  apply Matrix.inv_eq_right_inv
  rw [← RingHom.map_mul, mul_nonsing_inv M hM]
  simp

/-- IsUnit lifts through polynomial C map. -/
private lemma isUnit_det_map_C (P : Matrix n n ℂ) (hP : IsUnit P.det) :
    IsUnit (P.map Polynomial.C).det := by
  have h := RingHom.map_det (Polynomial.C (R := ℂ)) P
  have h2 : P.map Polynomial.C = Polynomial.C.mapMatrix P := by
    ext; simp [RingHom.mapMatrix_apply]
  rw [h2, ← h]
  exact hP.map _

/-- Determinant is invariant under similarity. -/
private lemma det_conj_of_isUnit' {R : Type*} [CommRing R] (M P : Matrix n n R) (hP : IsUnit P.det) :
    (P * M * P⁻¹).det = M.det := by
  rw [det_mul, det_mul]
  rw [mul_comm P.det M.det, mul_assoc]
  have h : P.det * P⁻¹.det = 1 := by
    rw [det_nonsing_inv]
    rw [Ring.mul_inverse_cancel _ hP]
  rw [h, mul_one]

/-- The characteristic matrix transforms under similarity. -/
private lemma charmatrix_conj_of_isUnit (M P : Matrix n n ℂ) (hP : IsUnit P.det) :
    (P * M * P⁻¹).charmatrix = (P.map Polynomial.C) * M.charmatrix * (P.map Polynomial.C)⁻¹ := by
  rw [charmatrix_eq_scalar_sub_map, charmatrix_eq_scalar_sub_map]
  rw [Matrix.map_mul, Matrix.map_mul]
  rw [map_inv_of_isUnit P Polynomial.C hP]
  have h_scalar_central : (P.map Polynomial.C) * scalar n Polynomial.X * (P.map Polynomial.C)⁻¹ =
      scalar n Polynomial.X := by
    rw [scalar_mul_eq_mul_scalar' (P.map Polynomial.C) Polynomial.X]
    rw [mul_assoc, mul_nonsing_inv (P.map Polynomial.C) (isUnit_det_map_C P hP)]
    rw [mul_one]
  have h_rhs : (P.map Polynomial.C) * (scalar n Polynomial.X - M.map Polynomial.C) *
      (P.map Polynomial.C)⁻¹ =
      (P.map Polynomial.C) * scalar n Polynomial.X * (P.map Polynomial.C)⁻¹ -
      (P.map Polynomial.C) * M.map Polynomial.C * (P.map Polynomial.C)⁻¹ := by
    rw [mul_sub, sub_mul]
  rw [h_rhs, h_scalar_central]

/-- **Characteristic polynomial is invariant under similarity**:
    For any invertible P, charpoly(P * M * P⁻¹) = charpoly(M). -/
theorem charpoly_conj_of_isUnit (M P : Matrix n n ℂ) (hP : IsUnit P.det) :
    (P * M * P⁻¹).charpoly = M.charpoly := by
  unfold charpoly
  rw [charmatrix_conj_of_isUnit M P hP]
  have hPC := isUnit_det_map_C P hP
  exact det_conj_of_isUnit' M.charmatrix (P.map Polynomial.C) hPC

/-- For unitary matrices, star U = U⁻¹. -/
private lemma unitary_star_eq_inv (U : unitaryGroup n ℂ) :
    star (U : Matrix n n ℂ) = (U : Matrix n n ℂ)⁻¹ := by
  have h : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := mem_unitaryGroup_iff.mp U.2
  symm
  exact Matrix.inv_eq_right_inv h

/-- Unitary matrices have unit determinant (|det U| = 1). -/
private lemma unitary_det_isUnit (U : unitaryGroup n ℂ) : IsUnit (U : Matrix n n ℂ).det := by
  have h : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := mem_unitaryGroup_iff.mp U.2
  have hdet : (U : Matrix n n ℂ).det * star ((U : Matrix n n ℂ).det) = 1 := by
    have star_eq : star (U : Matrix n n ℂ) = (U : Matrix n n ℂ)ᴴ := star_eq_conjTranspose _
    calc (U : Matrix n n ℂ).det * star ((U : Matrix n n ℂ).det)
        = (U : Matrix n n ℂ).det * (U : Matrix n n ℂ)ᴴ.det := by rw [det_conjTranspose]
      _ = (U : Matrix n n ℂ).det * (star (U : Matrix n n ℂ)).det := by rw [star_eq]
      _ = ((U : Matrix n n ℂ) * star (U : Matrix n n ℂ)).det := by rw [det_mul]
      _ = (1 : Matrix n n ℂ).det := by rw [h]
      _ = 1 := det_one
  exact IsUnit.of_mul_eq_one _ hdet

/-- Characteristic polynomial is invariant under unitary conjugation. -/
theorem charpoly_unitary_conj (M : Matrix n n ℂ) (U : unitaryGroup n ℂ) :
    ((U : Matrix n n ℂ) * M * star (U : Matrix n n ℂ)).charpoly = M.charpoly := by
  rw [unitary_star_eq_inv U]
  exact charpoly_conj_of_isUnit M (U : Matrix n n ℂ) (unitary_det_isUnit U)

/-! ### Eigenvalues of squared matrices and Hermitian singular values -/

/-- For Hermitian A, Aᴴ * A = A². -/
private lemma hermitian_conjTranspose_mul_self_eq_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    conjTranspose A * A = A ^ 2 := by
  rw [hA.eq, sq]

/-- Eigenvalues of Aᴴ*A equal eigenvalues of A² for Hermitian A (pointwise). -/
private lemma eigenvalues_conjTranspose_mul_self_eq_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues =
    (hA.pow 2).eigenvalues := by
  have h_eq := hermitian_conjTranspose_mul_self_eq_sq hA
  apply (IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
  rw [h_eq]

/-- Eigenvalues of A² equal (λᵢ)² as multisets (Hermitian A). -/
private lemma eigenvalues_sq_multiset (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    Multiset.map ((hA.pow 2).eigenvalues ·) Finset.univ.val =
    Multiset.map (fun i => (hA.eigenvalues i) ^ 2) Finset.univ.val := by
  -- Step 1: Get spectral decomposition A = U * diag(λ) * U*
  let U := hA.eigenvectorUnitary
  let eig := hA.eigenvalues

  have h_spectral : A = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) :=
    hA.spectral_theorem

  -- Step 2: A² = U * diag(λ²) * U*
  have h_sq : A ^ 2 = (U : Matrix n n ℂ) * diagonal (fun j => (Complex.ofReal (eig j)) ^ 2) * star (U : Matrix n n ℂ) := by
    rw [sq, h_spectral]
    have hUU : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := mem_unitaryGroup_iff'.mp U.2
    calc (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) *
        ((U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ))
        = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) *
          (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) *
          diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
      _ = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * 1 *
          diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by rw [hUU]
      _ = (U : Matrix n n ℂ) * (diagonal (Complex.ofReal ∘ eig) *
          diagonal (Complex.ofReal ∘ eig)) * star (U : Matrix n n ℂ) := by simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (U : Matrix n n ℂ) * diagonal (fun j => (Complex.ofReal (eig j)) ^ 2) *
          star (U : Matrix n n ℂ) := by
        congr 1; congr 1
        rw [diagonal_mul_diagonal]
        congr 1; ext j; simp only [Function.comp_apply, sq]

  -- Step 3: By unitary conjugation invariance, charpoly(A²) = charpoly(diag(λ²))
  have h_charpoly_eq : (A ^ 2).charpoly = (diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)).charpoly := by
    rw [h_sq]
    exact charpoly_unitary_conj _ U

  -- Step 4: Compute roots of both charpolys
  have h_roots_A_sq : (A ^ 2).charpoly.roots = Multiset.map (Complex.ofReal ∘ (hA.pow 2).eigenvalues) Finset.univ.val :=
    (hA.pow 2).roots_charpoly_eq_eigenvalues

  have h_roots_diag : (diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)).charpoly.roots =
      Finset.univ.val.map (fun j => (Complex.ofReal (eig j)) ^ 2) := by
    rw [charpoly_diagonal]
    have hne : ∏ i : n, (X - C ((Complex.ofReal (eig i)) ^ 2)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      exact X_sub_C_ne_zero _
    rw [Polynomial.roots_prod _ _ hne]
    simp only [roots_X_sub_C, Multiset.bind_singleton]

  -- Step 5: Since charpolys are equal, roots are equal
  have h_roots_eq : Multiset.map (Complex.ofReal ∘ (hA.pow 2).eigenvalues) Finset.univ.val =
      Finset.univ.val.map (fun j => (Complex.ofReal (eig j)) ^ 2) := by
    rw [← h_roots_A_sq, ← h_roots_diag, h_charpoly_eq]

  -- Step 6: Use that (ofReal r)² = ofReal (r²) to rewrite RHS
  have h_rhs_eq : Finset.univ.val.map (fun j => (Complex.ofReal (eig j)) ^ 2) =
      Finset.univ.val.map (fun j => Complex.ofReal ((eig j) ^ 2)) := by
    congr 1; ext j; simp only [Complex.ofReal_pow]

  rw [h_rhs_eq] at h_roots_eq

  -- Step 7: Use injectivity of ofReal to extract multiset equality
  have key : Multiset.map (Complex.ofReal ∘ (hA.pow 2).eigenvalues) Finset.univ.val =
             Multiset.map (Complex.ofReal ∘ (fun j => (hA.eigenvalues j) ^ 2)) Finset.univ.val := h_roots_eq

  simp only [← Multiset.map_map] at key
  exact Multiset.map_injective Complex.ofReal_injective key

/-- For a Hermitian matrix, the multiset of singular values equals the multiset of absolute
    values of eigenvalues. Note: pointwise equality does NOT hold in general because
    singular values are sorted decreasingly (all positive), while eigenvalues are sorted
    decreasingly by value (can be negative), so the orderings may differ.

    **Proof**: Uses helper lemmas `hermitian_conjTranspose_mul_self_eq_sq`,
    `eigenvalues_conjTranspose_mul_self_eq_sq`, and `eigenvalues_sq_multiset`
    defined above in the charpoly invariance machinery. -/
theorem singularValues_hermitian_multiset (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    Multiset.map (singularValues A) Finset.univ.val =
    Multiset.map (|hA.eigenvalues ·|) Finset.univ.val := by
  -- Step 1: Rewrite singularValues in terms of eigenvalues(A²)
  have h_sv_eq : ∀ i, singularValues A i = Real.sqrt ((hA.pow 2).eigenvalues i) := by
    intro i
    simp only [singularValues]
    rw [eigenvalues_conjTranspose_mul_self_eq_sq hA]

  -- Step 2: Rewrite LHS using h_sv_eq
  have h_lhs : Multiset.map (singularValues A) Finset.univ.val =
      Multiset.map (fun i => Real.sqrt ((hA.pow 2).eigenvalues i)) Finset.univ.val := by
    congr 1; ext i; exact h_sv_eq i

  rw [h_lhs]

  -- Step 3: Use eigenvalues_sq_multiset: eigenvalues(A²) as multiset = λ² as multiset
  have h_eig_sq := eigenvalues_sq_multiset A hA

  -- Step 4: Reformulate using Multiset.map_map
  have h1 : Multiset.map (fun i => Real.sqrt ((hA.pow 2).eigenvalues i)) Finset.univ.val =
      Multiset.map Real.sqrt (Multiset.map (fun i => (hA.pow 2).eigenvalues i) Finset.univ.val) := by
    rw [Multiset.map_map]; rfl

  have h2 : Multiset.map (fun i => Real.sqrt ((hA.eigenvalues i) ^ 2)) Finset.univ.val =
      Multiset.map Real.sqrt (Multiset.map (fun i => (hA.eigenvalues i) ^ 2) Finset.univ.val) := by
    rw [Multiset.map_map]; rfl

  rw [h1, h_eig_sq, ← h2]

  -- Step 5: Apply Real.sqrt_sq_eq_abs: √(λ²) = |λ|
  congr 1; ext i
  exact Real.sqrt_sq_eq_abs _


end Matrix.SVD
end Hagi.External.Flywheel
