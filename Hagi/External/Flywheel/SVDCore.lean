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

/-!
# SVDCore

Core square SVD: `singularValues`, zero-matrix spectra, singular vectors, the EuclideanSpace orthonormal-extension bridge, and the main decomposition theorem `A = U * S * Vᴴ`.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

namespace Matrix.SVD

variable {n : Type*} [Fintype n] [DecidableEq n]


/-- σᵢ(A) := √λᵢ(Aᴴ A). Well-defined since Aᴴ A ≽ 0. -/
noncomputable def singularValues (A : Matrix n n ℂ) : n → ℝ :=
  fun i => Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i)

theorem singularValues_nonneg (A : Matrix n n ℂ) (i : n) : 0 ≤ singularValues A i :=
  Real.sqrt_nonneg _

theorem singularValues_sq (A : Matrix n n ℂ) (i : n) :
    (singularValues A i) ^ 2 = (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := by
  unfold singularValues
  rw [Real.sq_sqrt]
  exact PosSemidef.eigenvalues_nonneg (posSemidef_conjTranspose_mul_self A) i

/-! ### Sorted Values

Antitone ordering σ₀ ≥ σ₁ ≥ ... via eigenvalues₀ from Mathlib.
-/

/-- Sorted singular values. Index 0 is largest (cf. Horn & Johnson Thm 7.3.5). -/
noncomputable def singularValues₀ (A : Matrix n n ℂ) : Fin (Fintype.card n) → ℝ :=
  fun k => Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ k)

/-- Sorted singular values are non-negative. -/
theorem singularValues₀_nonneg (A : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    0 ≤ singularValues₀ A k :=
  Real.sqrt_nonneg _

/-- Sorted singular values are antitone (decreasing): σ₀ ≥ σ₁ ≥ ⋯ ≥ σₙ₋₁. -/
theorem singularValues₀_antitone (A : Matrix n n ℂ) : Antitone (singularValues₀ A) := by
  intro k₁ k₂ hk
  unfold singularValues₀
  apply Real.sqrt_le_sqrt
  exact (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀_antitone hk

/-- Equivalence between sorted and unsorted singular values via the canonical bijection.
    singularValues A i = singularValues₀ A ((Fintype.equivOfCardEq ...).symm i) -/
theorem singularValues_eq_singularValues₀ (A : Matrix n n ℂ) (i : n) :
    singularValues A i =
      singularValues₀ A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := by
  unfold singularValues singularValues₀
  -- eigenvalues i = eigenvalues₀ ((Fintype.equivOfCardEq ...).symm i) by Mathlib definition
  rfl

/-- The squared sorted singular values equal the sorted eigenvalues of Aᴴ * A. -/
theorem singularValues₀_sq (A : Matrix n n ℂ) (k : Fin (Fintype.card n)) :
    (singularValues₀ A k) ^ 2 = (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ k := by
  unfold singularValues₀
  rw [Real.sq_sqrt]
  -- Use eigenvalues_nonneg via the equivalence: eigenvalues i = eigenvalues₀ (equiv.symm i)
  -- So eigenvalues₀ k = eigenvalues (equiv k)
  have h_psd := posSemidef_conjTranspose_mul_self A
  have h_herm := h_psd.isHermitian
  -- eigenvalues₀ k ≥ 0 follows from eigenvalues being nonneg at equiv k
  let i := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n) k
  have hi : h_herm.eigenvalues₀ k = h_herm.eigenvalues i := by
    simp only [i, Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]
  rw [hi]
  exact h_psd.eigenvalues_nonneg i

/-! ### Singular Values of Zero Matrix -/

-- This section is probably overkill for just proving that sv(0) = 0
-- but I wanted to make sure all the plumbing was correct.
-- Feel free to golf these proofs.

/-- Helper: The characteristic polynomial of the zero matrix is X^n. -/
private lemma matrix_charpoly_zero : (0 : Matrix n n ℂ).charpoly = X ^ Fintype.card n := by
  rw [charpoly, charmatrix]
  simp only [map_zero, sub_zero]
  have h_scalar : scalar n (X : ℂ[X]) = diagonal (fun _ => X) := by rfl
  rw [h_scalar, det_diagonal]
  simp only [Finset.prod_const, Finset.card_univ]

/-- Helper: The eigenvalues₀ of the zero matrix are all zero.
    Proof: charpoly(0) = X^n, whose roots are all 0. -/
private theorem eigenvalues₀_zero (hZ : IsHermitian (0 : Matrix n n ℂ)) : hZ.eigenvalues₀ = 0 := by
  funext k
  have h_roots := hZ.roots_charpoly_eq_eigenvalues₀
  rw [matrix_charpoly_zero] at h_roots
  have h_roots_Xn : (X ^ Fintype.card n : Polynomial ℂ).roots =
      Multiset.replicate (Fintype.card n) 0 := by
    simp only [Polynomial.roots_pow, Polynomial.roots_X, Multiset.nsmul_singleton]
  rw [h_roots_Xn] at h_roots
  have h_all_zero : ∀ x ∈ Multiset.map (RCLike.ofReal ∘ hZ.eigenvalues₀) Finset.univ.val,
      x = (0 : ℂ) := by
    intro x hx
    rw [← h_roots] at hx
    simp only [Multiset.mem_replicate, ne_eq] at hx
    exact hx.2
  have h_k_zero : (RCLike.ofReal (hZ.eigenvalues₀ k) : ℂ) = 0 := by
    apply h_all_zero
    simp only [Multiset.mem_map, Finset.mem_val, Function.comp_apply]
    exact ⟨k, Finset.mem_univ k, rfl⟩
  simp only [Pi.zero_apply]
  exact RCLike.ofReal_injective h_k_zero

/-- Singular values of zero matrix are all zero. -/
theorem singularValues₀_zero : singularValues₀ (0 : Matrix n n ℂ) = 0 := by
  unfold singularValues₀
  funext k
  simp only [Pi.zero_apply]
  -- 0ᴴ * 0 = 0, so we need eigenvalues₀ of zero matrix
  have h_psd := posSemidef_conjTranspose_mul_self (0 : Matrix n n ℂ)
  have h_herm_zero : IsHermitian (0 : Matrix n n ℂ) := isHermitian_zero
  -- Use eigenvalues_eq_eigenvalues_iff to relate eigenvalues via charpoly
  have h_eig_eq := IsHermitian.eigenvalues_eq_eigenvalues_iff h_psd.isHermitian h_herm_zero
  have h_eig_rel : h_psd.isHermitian.eigenvalues = h_herm_zero.eigenvalues := by
    rw [h_eig_eq]
    simp only [conjTranspose_zero, zero_mul]
  -- eigenvalues₀ k = eigenvalues (equiv k)
  have h_eig_zero := eigenvalues₀_zero h_herm_zero
  have h_target_zero : h_psd.isHermitian.eigenvalues₀ k = 0 := by
    have h1 : h_psd.isHermitian.eigenvalues₀ k =
              h_psd.isHermitian.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) k) := by
      simp only [IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    have h2 : h_herm_zero.eigenvalues₀ k =
              h_herm_zero.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) k) := by
      simp only [IsHermitian.eigenvalues, Equiv.symm_apply_apply]
    rw [h1]
    have h3 := congrFun h_eig_rel ((Fintype.equivOfCardEq (Fintype.card_fin _)) k)
    rw [h3, ← h2, h_eig_zero, Pi.zero_apply]
  rw [h_target_zero, Real.sqrt_zero]

/-! ### Singular Vectors -/

-- Naming convention: left vs right is confusing. Here's how I remember it:
-- - rightUnitary V: eigenvectors of A^H A ("right" because Av = σ u)
-- - leftUnitary U: eigenvectors of A A^H ("left" because A^H u = σ v)
-- If anyone has a better mnemonic please share!

/-- The right singular vectors V: an orthonormal basis of eigenvectors of Aᴴ * A.
    These form a unitary matrix where column i is the eigenvector for σᵢ². -/
noncomputable def rightUnitary (A : Matrix n n ℂ) : unitaryGroup n ℂ :=
  (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorUnitary

/-- The left singular vectors U: an orthonormal basis of eigenvectors of A * Aᴴ.
    These form a unitary matrix where column i is the eigenvector for σᵢ². -/
noncomputable def leftUnitary (A : Matrix n n ℂ) : unitaryGroup n ℂ :=
  (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvectorUnitary

/-- The diagonal matrix Σ containing the singular values along its diagonal. -/
noncomputable def singularDiagonal (A : Matrix n n ℂ) : Matrix n n ℂ :=
  diagonal (Complex.ofReal ∘ singularValues A)

-- CFC = continuous functional calculus. Took me a while to figure out what this was.
-- See: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.html

/-- The square root of Aᴴ*A, which is positive semidefinite by construction.
    This matrix P = √(Aᴴ*A) is central to polar decomposition: A = U*P. -/
noncomputable def sqrtConjTransposeMulSelf (A : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt (conjTranspose A * A)

/-- The square root of Aᴴ*A is positive semidefinite. -/
theorem sqrtConjTransposeMulSelf_isPosSemidef (A : Matrix n n ℂ) :
    (sqrtConjTransposeMulSelf A).PosSemidef := by
  unfold sqrtConjTransposeMulSelf
  exact (CFC.sqrt_nonneg (Aᴴ * A)).posSemidef

/-- The square root of Aᴴ*A is Hermitian (since it's PosSemidef). -/
theorem sqrtConjTransposeMulSelf_isHermitian (A : Matrix n n ℂ) :
    (sqrtConjTransposeMulSelf A).IsHermitian :=
  (sqrtConjTransposeMulSelf_isPosSemidef A).isHermitian

/-- Squaring √(Aᴴ*A) recovers Aᴴ*A. -/
theorem sqrtConjTransposeMulSelf_sq (A : Matrix n n ℂ) :
    (sqrtConjTransposeMulSelf A) ^ 2 = conjTranspose A * A := by
  unfold sqrtConjTransposeMulSelf
  have h : (0 : Matrix n n ℂ) ≤ Aᴴ * A := (posSemidef_conjTranspose_mul_self A).nonneg
  exact CFC.sq_sqrt (Aᴴ * A) h

/-- √(Aᴴ*A) * √(Aᴴ*A) = Aᴴ*A. -/
theorem sqrtConjTransposeMulSelf_mul_self (A : Matrix n n ℂ) :
    sqrtConjTransposeMulSelf A * sqrtConjTransposeMulSelf A = conjTranspose A * A := by
  unfold sqrtConjTransposeMulSelf
  have h : (0 : Matrix n n ℂ) ≤ Aᴴ * A := (posSemidef_conjTranspose_mul_self A).nonneg
  exact CFC.sqrt_mul_sqrt_self (Aᴴ * A) h

-- Polar decomposition: A = U·P where P = √(A*A) is psd and U unitary

/-- Key computational lemma: Vᴴ * (Aᴴ * A) * V = diag(eigenvalues). -/
theorem svd_action (A : Matrix n n ℂ) :
    let V : Matrix n n ℂ := rightUnitary A
    let eig := (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
    Vᴴ * (Aᴴ * A) * V = diagonal (Complex.ofReal ∘ eig) := by
  intro V eig
  have h_spectral : Aᴴ * A = V * diagonal (Complex.ofReal ∘ eig) * Vᴴ :=
    (posSemidef_conjTranspose_mul_self A).isHermitian.spectral_theorem
  have hVV : Vᴴ * V = 1 := mem_unitaryGroup_iff'.mp (rightUnitary A).2
  calc Vᴴ * (Aᴴ * A) * V
      = Vᴴ * (V * diagonal (Complex.ofReal ∘ eig) * Vᴴ) * V := by simp only [h_spectral]
    _ = Vᴴ * V * diagonal (Complex.ofReal ∘ eig) * Vᴴ * V := by simp only [Matrix.mul_assoc]
    _ = 1 * diagonal (Complex.ofReal ∘ eig) * Vᴴ * V := by rw [hVV]
    _ = diagonal (Complex.ofReal ∘ eig) * Vᴴ * V := by rw [one_mul]
    _ = diagonal (Complex.ofReal ∘ eig) * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = diagonal (Complex.ofReal ∘ eig) * 1 := by rw [hVV]
    _ = diagonal (Complex.ofReal ∘ eig) := by rw [mul_one]

/-- Corollary: (A*V)ᴴ * (A*V) = diag(σ²). -/
theorem conjTranspose_AV_mul_AV (A : Matrix n n ℂ) :
    let V : Matrix n n ℂ := rightUnitary A
    let eig := (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
    (A * V)ᴴ * (A * V) = diagonal (Complex.ofReal ∘ eig) := by
  intro V eig
  rw [conjTranspose_mul]
  calc Vᴴ * Aᴴ * (A * V)
      = Vᴴ * (Aᴴ * A) * V := by simp only [Matrix.mul_assoc]
    _ = diagonal (Complex.ofReal ∘ eig) := svd_action A

-- For σᵢ ≠ 0, left singular vector uᵢ = (1/σᵢ)(A·vᵢ)

/-- The (i,j) entry of (A*V)ᴴ*(A*V) equals inner product of cols i and j. -/
lemma AV_conjTranspose_mul_AV_apply (A : Matrix n n ℂ) (i j : n) :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    (AVᴴ * AV) i j = ∑ k, star (AV k i) * AV k j := by
  simp only [conjTranspose_apply, mul_apply]

/-- Columns of A*V are orthogonal: for i ≠ j, the inner product is 0. -/
lemma AV_columns_orthogonal (A : Matrix n n ℂ) (i j : n) (hij : i ≠ j) :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    ∑ k, star (AV k i) * AV k j = 0 := by
  intro V AV
  have h2 := conjTranspose_AV_mul_AV A
  simp only at h2
  have h1 : (AVᴴ * AV) i j = ∑ k, star (AV k i) * AV k j := by
    simp only [conjTranspose_apply, mul_apply]
  rw [h1.symm, h2, diagonal_apply, Function.comp_apply, if_neg hij]

/-- Squared norm of column i of A*V equals σᵢ² (using singularValues). -/
lemma AV_column_norm_sq (A : Matrix n n ℂ) (i : n) :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    ∑ k, star (AV k i) * AV k i = Complex.ofReal ((singularValues A i) ^ 2) := by
  intro V AV
  have h2 := conjTranspose_AV_mul_AV A
  simp only at h2
  have h1 : (AVᴴ * AV) i i = ∑ k, star (AV k i) * AV k i := by
    simp only [conjTranspose_apply, mul_apply]
  simp only [singularValues]
  rw [h1.symm, h2, diagonal_apply_eq, Function.comp_apply]
  congr 1
  rw [Real.sq_sqrt]
  exact (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i

/-- For σᵢ ≠ 0, the i-th left singular vector is (1/σᵢ) · (column i of A·V).
    This vector has unit norm and is orthogonal to other left singular vectors. -/
noncomputable def leftSingularVectorNonzero (A : Matrix n n ℂ) (i : n)
    (_ : singularValues A i ≠ 0) : n → ℂ :=
  let AV := A * (rightUnitary A : Matrix n n ℂ)
  fun k => (Complex.ofReal (singularValues A i))⁻¹ * AV k i

/-- The inner product of left singular vectors for i ≠ j is 0. -/
theorem leftSingularVectorNonzero_orthogonal (A : Matrix n n ℂ) (i j : n)
    (hi : singularValues A i ≠ 0) (hj : singularValues A j ≠ 0) (hij : i ≠ j) :
    ∑ k, star (leftSingularVectorNonzero A i hi k) * (leftSingularVectorNonzero A j hj k) = 0 := by
  unfold leftSingularVectorNonzero
  have h_orth := AV_columns_orthogonal A i j hij
  simp only [star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  have factor : ∀ k : n,
      ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ *
        (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) *
        (((Complex.ofReal (singularValues A j) : ℂ))⁻¹ * (A * (rightUnitary A : Matrix n n ℂ)) k j) =
      ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ * ((Complex.ofReal (singularValues A j) : ℂ))⁻¹ *
        ((starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) * (A * (rightUnitary A : Matrix n n ℂ)) k j) := by
    intro k; ring
  conv_lhs => arg 2; ext k; rw [factor k]
  rw [← Finset.mul_sum]
  have h_star_eq : ∀ k : n, (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) =
      star ((A * (rightUnitary A : Matrix n n ℂ)) k i) := fun _ => rfl
  simp_rw [h_star_eq, h_orth, mul_zero]

/-- The squared norm (inner product with self) of a left singular vector is 1.
    This uses: ‖uᵢ‖² = (1/σᵢ)² · ‖column i of A*V‖² = (1/σᵢ)² · σᵢ² = 1 -/
theorem leftSingularVectorNonzero_inner_self (A : Matrix n n ℂ) (i : n)
    (hi : singularValues A i ≠ 0) :
    ∑ k, star (leftSingularVectorNonzero A i hi k) * (leftSingularVectorNonzero A i hi k) = 1 := by
  unfold leftSingularVectorNonzero
  have h_norm := AV_column_norm_sq A i
  simp only [star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  have factor : ∀ k : n,
      ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ *
        (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) *
        (((Complex.ofReal (singularValues A i) : ℂ))⁻¹ * (A * (rightUnitary A : Matrix n n ℂ)) k i) =
      ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ * ((Complex.ofReal (singularValues A i) : ℂ))⁻¹ *
        ((starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) * (A * (rightUnitary A : Matrix n n ℂ)) k i) := by
    intro k; ring
  conv_lhs => arg 2; ext k; rw [factor k]
  rw [← Finset.mul_sum]
  have h_star_eq : ∀ k : n, (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) k i) =
      star ((A * (rightUnitary A : Matrix n n ℂ)) k i) := fun _ => rfl
  simp_rw [h_star_eq, h_norm]
  -- Now: (σᵢ⁻¹)² · σᵢ² = 1
  have hi' : (Complex.ofReal (singularValues A i) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hi
  have h_sq_eq : (Complex.ofReal ((singularValues A i) ^ 2) : ℂ) =
      ((Complex.ofReal (singularValues A i) : ℂ)) * ((Complex.ofReal (singularValues A i) : ℂ)) := by
    rw [sq, Complex.ofReal_mul]
  rw [h_sq_eq]
  field_simp

/-- When σᵢ = 0, column i of A*V is the zero vector.
    This follows from ||(A*V)[:,i]||² = σᵢ² = 0. -/
lemma AV_column_zero_of_singularValue_zero (A : Matrix n n ℂ) (i : n)
    (hi : singularValues A i = 0) :
    ∀ k, (A * (rightUnitary A : Matrix n n ℂ)) k i = 0 := by
  intro k
  -- The sum ∑ k, star(AV k i) * (AV k i) = σᵢ² = 0
  have h_sum := AV_column_norm_sq A i
  simp only at h_sum
  rw [hi] at h_sum
  simp only [sq, mul_zero, Complex.ofReal_zero] at h_sum
  -- Each term star(z) * z = |z|² ≥ 0
  let AV := (A * (rightUnitary A : Matrix n n ℂ))
  -- star(z) * z = normSq(z) for complex numbers
  have h_eq_normSq : ∀ j, star (AV j i) * AV j i = Complex.normSq (AV j i) := by
    intro j
    have h1 : star (AV j i) = (starRingEnd ℂ) (AV j i) := rfl
    rw [h1]
    have h2 : (starRingEnd ℂ) (AV j i) * AV j i = AV j i * (starRingEnd ℂ) (AV j i) := mul_comm _ _
    rw [h2]
    rw [mul_comm]
    exact Complex.normSq_eq_conj_mul_self.symm
  -- The sum of normSq values = 0
  have h_sum_normSq_complex : ∑ j, (Complex.normSq (AV j i) : ℂ) = 0 := by
    conv_lhs => rw [← Finset.sum_congr rfl (fun j _ => h_eq_normSq j)]
    exact h_sum
  -- Extract as a real sum
  have h_sum_normSq : ∑ j, Complex.normSq (AV j i) = 0 := by
    have h_real : (∑ j, Complex.normSq (AV j i) : ℂ) = (∑ j, Complex.normSq (AV j i) : ℝ) := by
      rw [Complex.ofReal_sum]
    rw [h_real] at h_sum_normSq_complex
    exact Complex.ofReal_injective h_sum_normSq_complex
  -- Sum of nonneg = 0 implies each = 0
  have h_each_zero := @Finset.sum_eq_zero_iff_of_nonneg n ℝ _ _ (fun j => Complex.normSq (AV j i))
    Finset.univ _ (fun j _ => Complex.normSq_nonneg _)
  rw [h_each_zero] at h_sum_normSq
  have hk := h_sum_normSq k (Finset.mem_univ k)
  change Complex.normSq (AV k i) = 0 at hk
  exact Complex.normSq_eq_zero.mp hk

/-! ### EuclideanSpace Bridge for Orthonormal Basis Extension

Constructing the unitary U for full SVD.
-/

set_option linter.unusedSectionVars false in
/-- Inner product on EuclideanSpace matches our sum formula for star-multiplication. -/
lemma inner_euclidean_eq_sum {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    @inner ℂ (EuclideanSpace ℂ ι) _
      ((WithLp.equiv 2 (ι → ℂ)).symm x)
      ((WithLp.equiv 2 (ι → ℂ)).symm y)
    = ∑ i, star (x i) * y i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  have h1 : ∀ i, ((WithLp.equiv 2 (ι → ℂ)).symm x).ofLp i = x i := fun _ => rfl
  have h2 : ∀ i, ((WithLp.equiv 2 (ι → ℂ)).symm y).ofLp i = y i := fun _ => rfl
  simp_rw [h1, h2, ← Complex.star_def, mul_comm]

/-- Left singular vector as EuclideanSpace element. -/
noncomputable def leftSingularVectorEuclidean (A : Matrix n n ℂ) (i : n)
    (hi : singularValues A i ≠ 0) : EuclideanSpace ℂ n :=
  (WithLp.equiv 2 (n → ℂ)).symm (leftSingularVectorNonzero A i hi)

/-- Extended function for all indices: uses left singular vector when σᵢ ≠ 0, else 0.
    The 0 values will be replaced by the orthonormal basis extension. -/
noncomputable def leftSingularVectorExtended (A : Matrix n n ℂ) : n → EuclideanSpace ℂ n :=
  fun i => if h : singularValues A i ≠ 0
           then leftSingularVectorEuclidean A i h
           else 0

/-- The set of indices with nonzero singular values. -/
def nonzeroSingularIndices (A : Matrix n n ℂ) : Set n :=
  {i | singularValues A i ≠ 0}

/-- The left singular vectors restricted to nonzero singular value indices form an orthonormal set. -/
theorem leftSingularVectorExtended_orthonormal_on_nonzero (A : Matrix n n ℂ) :
    Orthonormal ℂ ((nonzeroSingularIndices A).domRestrict (leftSingularVectorExtended A)) := by
  rw [orthonormal_iff_ite]
  intro ⟨i, hi⟩ ⟨j, hj⟩
  unfold nonzeroSingularIndices at hi hj
  have hi' : (if h : singularValues A i ≠ 0 then leftSingularVectorEuclidean A i h else 0)
            = leftSingularVectorEuclidean A i hi := dif_pos hi
  have hj' : (if h : singularValues A j ≠ 0 then leftSingularVectorEuclidean A j h else 0)
            = leftSingularVectorEuclidean A j hj := dif_pos hj
  unfold leftSingularVectorExtended
  rw [Set.domRestrict_apply, Set.domRestrict_apply]
  rw [hi', hj']
  unfold leftSingularVectorEuclidean
  rw [inner_euclidean_eq_sum]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
    exact leftSingularVectorNonzero_inner_self A i hi
  · have hij' : (⟨i, hi⟩ : {i : n | singularValues A i ≠ 0}) ≠ ⟨j, hj⟩ := by
      intro heq; apply h; exact Subtype.ext_iff.mp heq
    split
    · next heq => exact absurd (Subtype.ext_iff.mp heq) h
    · exact leftSingularVectorNonzero_orthogonal A i j hi hj h

/-- Extend the orthonormal left singular vectors to a full orthonormal basis. -/
noncomputable def extendedONB (A : Matrix n n ℂ) :
    OrthonormalBasis n ℂ (EuclideanSpace ℂ n) :=
  ((leftSingularVectorExtended_orthonormal_on_nonzero A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose

/-- The extended ONB agrees with left singular vectors on nonzero singular value indices. -/
theorem extendedONB_spec (A : Matrix n n ℂ) :
    ∀ i, i ∈ nonzeroSingularIndices A → (extendedONB A) i = leftSingularVectorExtended A i :=
  ((leftSingularVectorExtended_orthonormal_on_nonzero A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose_spec

/-- Convert an orthonormal basis of EuclideanSpace ℂ ι to a matrix
(column j = basis vector j). General form: covers both square and
rectangular constructions (the rectangular copies were merged). -/
noncomputable def onbToMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) : Matrix ι ι ℂ :=
  fun i j => (b j) i

set_option linter.unusedSectionVars false in
/-- The inner product of columns equals the inner product of basis vectors. -/
lemma onbToMatrix_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (i j : ι) :
    (star (onbToMatrix b) * onbToMatrix b) i j =
    @inner ℂ (EuclideanSpace ℂ ι) _ (b i) (b j) := by
  simp only [mul_apply, star_apply, onbToMatrix]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply]
  congr 1
  ext k
  simp only [star, ← Complex.star_def, mul_comm]

/-- A matrix built from an orthonormal basis is unitary. -/
theorem onbToMatrix_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) :
    onbToMatrix b ∈ unitaryGroup ι ℂ := by
  rw [mem_unitaryGroup_iff']
  ext i j
  rw [onbToMatrix_inner, one_apply]
  have h_on : Orthonormal ℂ b := b.orthonormal
  rw [orthonormal_iff_ite] at h_on
  exact h_on i j

/-- The constructed unitary matrix U for SVD.
    Columns are: left singular vectors for σᵢ ≠ 0, orthonormal extension for σᵢ = 0. -/
noncomputable def constructedU (A : Matrix n n ℂ) : unitaryGroup n ℂ :=
  ⟨onbToMatrix (extendedONB A), onbToMatrix_mem_unitaryGroup _⟩

/-- Column j of constructed U equals the left singular vector when σⱼ ≠ 0. -/
theorem constructedU_column_eq (A : Matrix n n ℂ) (j : n) (hj : singularValues A j ≠ 0) :
    (fun i => (constructedU A : Matrix n n ℂ) i j) = leftSingularVectorNonzero A j hj := by
  ext i
  simp only [constructedU, onbToMatrix]
  have hj_mem : j ∈ nonzeroSingularIndices A := hj
  have h_spec := extendedONB_spec A j hj_mem
  have h_expand : leftSingularVectorExtended A j = leftSingularVectorEuclidean A j hj := dif_pos hj
  rw [h_spec, h_expand]
  simp only [leftSingularVectorEuclidean]
  rfl

/-- Key relationship: A * V = U * Σ (where U = constructedU).
    This is the core equation that makes SVD work:
    - For σⱼ ≠ 0: column j of A*V equals σⱼ times column j of U (by definition of U)
    - For σⱼ = 0: column j of A*V is zero, and σⱼ * column j of U is also zero -/
theorem AV_eq_constructedU_mul_sigma (A : Matrix n n ℂ) :
    A * (rightUnitary A : Matrix n n ℂ) =
    (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) := by
  ext i j
  simp only [mul_apply, diagonal_apply, Function.comp_apply]
  -- RHS simplifies: ∑ x, U i x * (if x = j then σ x else 0) = U i j * σ j
  have h_rhs : ∑ x, (constructedU A : Matrix n n ℂ) i x *
               (if x = j then Complex.ofReal (singularValues A x) else 0) =
               (constructedU A : Matrix n n ℂ) i j * Complex.ofReal (singularValues A j) := by
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte]
    · intro b _ hbj; simp only [hbj, ↓reduceIte, mul_zero]
    · intro hj_not_mem; exact absurd (Finset.mem_univ j) hj_not_mem
  rw [h_rhs]
  by_cases hj : singularValues A j ≠ 0
  · -- Case σⱼ ≠ 0: (A*V)ᵢⱼ = σⱼ * Uᵢⱼ
    have h_col := constructedU_column_eq A j hj
    have h_U_eq : (constructedU A : Matrix n n ℂ) i j = leftSingularVectorNonzero A j hj i := by
      exact congrFun h_col i
    rw [h_U_eq]
    simp only [leftSingularVectorNonzero]
    -- Uᵢⱼ = (1/σⱼ) * (A*V)ᵢⱼ, so σⱼ * Uᵢⱼ = (A*V)ᵢⱼ
    have hj' : (Complex.ofReal (singularValues A j) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; exact hj
    -- LHS is (A * V) i j by definition
    simp only [mul_apply]
    field_simp
  · -- Case σⱼ = 0: both sides are 0
    push_neg at hj
    have h_AV_zero := AV_column_zero_of_singularValue_zero A j hj
    simp only [hj, Complex.ofReal_zero, mul_zero]
    -- LHS: ∑ x, A i x * V x j = (A * V) i j = 0
    have h_lhs : ∑ x, A i x * (rightUnitary A : Matrix n n ℂ) x j =
                 (A * (rightUnitary A : Matrix n n ℂ)) i j := rfl
    rw [h_lhs, h_AV_zero i]

/-! ### Main Decomposition Theorem -/

/-- **Singular Value Decomposition (Existence Form)**:
    Any square complex matrix A can be decomposed as A = U * Σ * Vᴴ
    where:
    - U is unitary (the left singular vectors)
    - V is unitary (the right singular vectors)
    - Σ is diagonal with non-negative real entries (the singular values)

    This follows from the spectral theorem applied to the positive semidefinite
    matrices Aᴴ * A and A * Aᴴ.

    **Proof Strategy:**
    1. V = eigenvectors of Aᴴ*A (rightUnitary)
    2. σᵢ = √(eigenvalues of Aᴴ*A) (singularValues)
    3. Construct U such that A*V = U*Σ
       - For σᵢ ≠ 0: uᵢ = (1/σᵢ)*A*vᵢ
       - For σᵢ = 0: uᵢ is any orthonormal extension
    4. Verify A = U*Σ*Vᴴ -/
theorem svd_decomposition (A : Matrix n n ℂ) :
    ∃ (U V : unitaryGroup n ℂ) (σ : n → ℝ),
      (∀ i, 0 ≤ σ i) ∧
      A = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ σ) * star (V : Matrix n n ℂ) := by
  -- Use V from spectral decomposition of Aᴴ*A
  -- Use U constructed by extending orthonormal left singular vectors
  use constructedU A, rightUnitary A, singularValues A
  constructor
  · intro i; exact Real.sqrt_nonneg _
  · -- Main equation: A = U * Σ * Vᴴ
    -- From AV_eq_constructedU_mul_sigma: A * V = U * Σ
    -- Multiply both sides by Vᴴ: A * V * Vᴴ = U * Σ * Vᴴ
    -- Since V is unitary: V * Vᴴ = I, so A = U * Σ * Vᴴ
    have h_AV := AV_eq_constructedU_mul_sigma A
    have h_V_unitary : (rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ) = 1 :=
      mem_unitaryGroup_iff.mp (rightUnitary A).2
    calc A = A * 1 := by rw [mul_one]
      _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [h_V_unitary]
      _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]
      _ = ((constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A)) *
          star (rightUnitary A : Matrix n n ℂ) := by rw [h_AV]
      _ = (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) *
          star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]


end Matrix.SVD
end Hagi.External.Flywheel
