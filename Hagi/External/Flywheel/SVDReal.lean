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
import Hagi.External.Flywheel.SVDTruncated

/-!
# SVDReal

Real matrix SVD (`Matrix.SVD.Real`) plus `eigenvalues₀` helper lemmas for positive-semidefinite spectra.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

/-! ## Real Matrix SVD -/

namespace Matrix.SVD.Real

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The singular values of a real matrix A are the square roots of the eigenvalues of Aᵀ * A. -/
noncomputable def singularValues (A : Matrix n n ℝ) : n → ℝ :=
  Matrix.SVD.singularValues (A.map Complex.ofReal)

omit [Fintype n] [DecidableEq n] in
/-- A real matrix mapped to ℂ has Hermitian = Symmetric (transpose equals conjTranspose). -/
lemma real_matrix_conjTranspose_eq_transpose (A : Matrix n n ℝ) :
    (A.map Complex.ofReal)ᴴ = (Aᵀ).map Complex.ofReal := by
  ext i j
  simp only [conjTranspose_apply, map_apply, transpose_apply]
  exact Complex.conj_ofReal (A j i)

omit [DecidableEq n] in
/-- For real A, Aᴴ * A = Aᵀ * A (as complex matrices). -/
lemma real_conjTranspose_mul_self (A : Matrix n n ℝ) :
    (A.map Complex.ofReal)ᴴ * (A.map Complex.ofReal) = (Aᵀ * A).map Complex.ofReal := by
  rw [real_matrix_conjTranspose_eq_transpose]
  ext i j
  simp only [mul_apply, map_apply, transpose_apply]
  conv_lhs =>
    arg 2
    ext k
    rw [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum]

omit [Fintype n] [DecidableEq n] in
/-- A real symmetric matrix is Hermitian when viewed as complex. -/
lemma real_symmetric_isHermitian {A : Matrix n n ℝ} (hA : A.IsSymm) :
    (A.map Complex.ofReal).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, map_apply]
  have h_star : star (Complex.ofReal (A j i)) = Complex.ofReal (A j i) := by
    rw [Complex.star_def]
    exact Complex.conj_ofReal (A j i)
  rw [h_star, hA.apply j i]

omit [DecidableEq n] in
/-- Aᵀ * A is symmetric for any real matrix A. -/
lemma transpose_mul_self_isSymm (A : Matrix n n ℝ) : (Aᵀ * A).IsSymm := by
  rw [IsSymm, transpose_mul, transpose_transpose]

omit [Fintype n] [DecidableEq n] in
/-- For real matrices, transpose = conjTranspose. -/
private lemma transpose_eq_conjTranspose (A : Matrix n n ℝ) :
    A.transpose = A.conjTranspose := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply]
  exact (starRingEnd_self_apply (A j i)).symm

omit [DecidableEq n] in
/-- Aᵀ * A is Hermitian for real A (since transpose = conjTranspose). -/
private lemma transpose_mul_self_isHermitian' (A : Matrix n n ℝ) :
    (A.transpose * A).IsHermitian := by
  rw [transpose_eq_conjTranspose]
  exact (posSemidef_conjTranspose_mul_self A).isHermitian

/-- Eigenvalues of Aᵀ*A are nonnegative for real A. -/
lemma eigenvalues_transpose_mul_self_nonneg (A : Matrix n n ℝ) :
    let hATA := transpose_mul_self_isHermitian' A
    ∀ i, 0 ≤ hATA.eigenvalues i := by
  intro hATA i
  have h := eigenvalues_conjTranspose_mul_self_nonneg A
  have h_charpoly : (A.transpose * A).charpoly = (A.conjTranspose * A).charpoly := by
    simp only [transpose_eq_conjTranspose]
  have h_eig_eq : hATA.eigenvalues =
      (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues :=
    hATA.eigenvalues_eq_eigenvalues_iff _ |>.mpr h_charpoly
  rw [h_eig_eq]
  exact h i

/-! ### Real SVD Construction

We construct the real SVD by adapting the complex construction pattern.
Key insight: Over ℝ, `unitaryGroup = orthogonalGroup` and `star = transpose`.
-/

/-- The right orthogonal matrix V for SVD, obtained from eigenvectors of Aᵀ * A. -/
noncomputable def rightOrthogonal (A : Matrix n n ℝ) : orthogonalGroup n ℝ :=
  let hHerm := transpose_mul_self_isHermitian' A
  ⟨hHerm.eigenvectorUnitary, hHerm.eigenvectorUnitary.2⟩

/-- A * V, the key intermediate matrix for SVD construction. -/
noncomputable def realAV (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A * (rightOrthogonal A : Matrix n n ℝ)

/-- Real singular values: σᵢ = √(eigenvalues of Aᵀ*A). -/
noncomputable def realSingularValues (A : Matrix n n ℝ) : n → ℝ :=
  let hHerm := transpose_mul_self_isHermitian' A
  fun i => Real.sqrt (hHerm.eigenvalues i)

/-- Key property: (A*V)ᵀ * (A*V) = diagonal of eigenvalues of Aᵀ*A. -/
lemma transpose_realAV_mul_realAV (A : Matrix n n ℝ) :
    (realAV A).transpose * realAV A =
    diagonal (transpose_mul_self_isHermitian' A).eigenvalues := by
  let hHerm := transpose_mul_self_isHermitian' A
  let V : Matrix n n ℝ := hHerm.eigenvectorUnitary
  have h := hHerm.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at h
  -- Over ℝ: RCLike.ofReal is identity
  have h_real_diag : diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) = diagonal hHerm.eigenvalues := by
    ext i j; simp only [diagonal, of_apply, Function.comp_apply]
    split_ifs <;> simp [RCLike.ofReal]
  -- Over ℝ: star = transpose
  have h_star_eq_trans : star V = V.transpose := by ext i j; simp [star]
  have h_Vstar_V : star V * V = 1 := mem_unitaryGroup_iff'.mp (hHerm.eigenvectorUnitary).2
  simp only [realAV, rightOrthogonal]
  have step1 : (A * V).transpose * (A * V) = V.transpose * (A.transpose * A) * V := by
    rw [transpose_mul]; noncomm_ring
  have step2 : V.transpose * (A.transpose * A) * V = star V * (A.transpose * A) * V := by
    rw [← h_star_eq_trans]
  have step3 : star V * (A.transpose * A) * V =
               star V * (V * diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * star V) * V := by
    conv_lhs => rw [h]
  have step4 : star V * (V * diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * star V) * V =
               (star V * V) * diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * (star V * V) := by
    noncomm_ring
  have step5 : (star V * V) * diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) * (star V * V) =
               diagonal (RCLike.ofReal ∘ hHerm.eigenvalues) := by
    rw [h_Vstar_V]; simp
  rw [step1, step2, step3, step4, step5, h_real_diag]

/-- Columns of A*V are orthogonal. -/
lemma realAV_columns_orthogonal (A : Matrix n n ℝ) (i j : n) (hij : i ≠ j) :
    ∑ k, (realAV A) k i * (realAV A) k j = 0 := by
  have h := transpose_realAV_mul_realAV A
  have h_entry : ((realAV A).transpose * realAV A) i j = ∑ k, (realAV A) k i * (realAV A) k j := by
    simp only [mul_apply, transpose_apply]
  have h_diag : (diagonal (transpose_mul_self_isHermitian' A).eigenvalues) i j = 0 := by
    simp only [diagonal_apply, hij, ↓reduceIte]
  rw [← h_entry, h, h_diag]

/-- Squared norm of column i of A*V equals σᵢ². -/
lemma realAV_column_norm_sq (A : Matrix n n ℝ) (i : n) :
    ∑ k, (realAV A) k i * (realAV A) k i = (realSingularValues A i) ^ 2 := by
  have h := transpose_realAV_mul_realAV A
  have h_entry : ((realAV A).transpose * realAV A) i i = ∑ k, (realAV A) k i * (realAV A) k i := by
    simp only [mul_apply, transpose_apply]
  rw [← h_entry, h, diagonal_apply_eq]
  simp only [realSingularValues]
  rw [Real.sq_sqrt]
  exact eigenvalues_transpose_mul_self_nonneg A i

/-- Left singular vector for nonzero σᵢ: uᵢ = (1/σᵢ) * (A*V)[:,i]. -/
noncomputable def leftSingularVectorNonzero_real (A : Matrix n n ℝ) (i : n)
    (_ : realSingularValues A i ≠ 0) : n → ℝ :=
  fun k => (realSingularValues A i)⁻¹ * realAV A k i

/-- Left singular vector as EuclideanSpace element. -/
noncomputable def leftSingularVectorEuclidean_real (A : Matrix n n ℝ) (i : n)
    (hi : realSingularValues A i ≠ 0) : EuclideanSpace ℝ n :=
  (WithLp.equiv 2 (n → ℝ)).symm (leftSingularVectorNonzero_real A i hi)

/-- Extended function: left singular vector for nonzero σ, 0 for zero σ. -/
noncomputable def leftSingularVectorExtended_real (A : Matrix n n ℝ) : n → EuclideanSpace ℝ n :=
  fun i => if h : realSingularValues A i ≠ 0
           then leftSingularVectorEuclidean_real A i h
           else 0

/-- Set of indices with nonzero singular values. -/
def nonzeroSingularIndices_real (A : Matrix n n ℝ) : Set n :=
  {i | realSingularValues A i ≠ 0}

set_option linter.unusedSectionVars false in
/-- Inner product on EuclideanSpace ℝ n equals sum formula. -/
private lemma inner_euclidean_eq_sum_real (x y : EuclideanSpace ℝ n) :
    @inner ℝ (EuclideanSpace ℝ n) _ x y = ∑ i, x i * y i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  congr 1; ext i; ring

/-- Left singular vectors (on nonzero singular value indices) are orthonormal. -/
theorem leftSingularVectorExtended_orthonormal_on_nonzero_real (A : Matrix n n ℝ) :
    Orthonormal ℝ ((nonzeroSingularIndices_real A).domRestrict (leftSingularVectorExtended_real A)) := by
  rw [orthonormal_iff_ite]
  intro ⟨i, hi⟩ ⟨j, hj⟩
  unfold nonzeroSingularIndices_real at hi hj
  have hi' : (if h : realSingularValues A i ≠ 0 then leftSingularVectorEuclidean_real A i h else 0)
            = leftSingularVectorEuclidean_real A i hi := dif_pos hi
  have hj' : (if h : realSingularValues A j ≠ 0 then leftSingularVectorEuclidean_real A j h else 0)
            = leftSingularVectorEuclidean_real A j hj := dif_pos hj
  unfold leftSingularVectorExtended_real
  rw [Set.domRestrict_apply, Set.domRestrict_apply]
  rw [hi', hj']
  rw [inner_euclidean_eq_sum_real]
  simp only [leftSingularVectorEuclidean_real, leftSingularVectorNonzero_real,
             WithLp.equiv_symm_apply]
  by_cases h : i = j
  · -- Case i = j: inner product = 1
    subst h
    simp only [ite_true]
    have h_norm := realAV_column_norm_sq A i
    have factor : ∀ k : n,
        (realSingularValues A i)⁻¹ * realAV A k i * ((realSingularValues A i)⁻¹ * realAV A k i) =
        (realSingularValues A i)⁻¹ * (realSingularValues A i)⁻¹ * (realAV A k i * realAV A k i) := by
      intro k; ring
    simp_rw [factor, ← Finset.mul_sum, h_norm]
    have h_sq : (realSingularValues A i)⁻¹ * (realSingularValues A i)⁻¹ * (realSingularValues A i) ^ 2 =
                ((realSingularValues A i)⁻¹ * (realSingularValues A i)) ^ 2 := by ring
    rw [h_sq, inv_mul_cancel₀ hi, one_pow]
  · -- Case i ≠ j: inner product = 0
    split
    · next heq => exact absurd (Subtype.ext_iff.mp heq) h
    · have h_orth := realAV_columns_orthogonal A i j h
      have factor : ∀ k : n,
          (realSingularValues A i)⁻¹ * realAV A k i * ((realSingularValues A j)⁻¹ * realAV A k j) =
          (realSingularValues A i)⁻¹ * (realSingularValues A j)⁻¹ * (realAV A k i * realAV A k j) := by
        intro k; ring
      simp_rw [factor, ← Finset.mul_sum, h_orth, mul_zero]

/-- Extend orthonormal left singular vectors to a full orthonormal basis. -/
noncomputable def extendedONB_real (A : Matrix n n ℝ) :
    OrthonormalBasis n ℝ (EuclideanSpace ℝ n) :=
  ((leftSingularVectorExtended_orthonormal_on_nonzero_real A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose

/-- The extended ONB agrees with left singular vectors on nonzero singular value indices. -/
theorem extendedONB_real_spec (A : Matrix n n ℝ) :
    ∀ i, i ∈ nonzeroSingularIndices_real A → (extendedONB_real A) i = leftSingularVectorExtended_real A i :=
  ((leftSingularVectorExtended_orthonormal_on_nonzero_real A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose_spec

/-- Convert an orthonormal basis of EuclideanSpace ℝ n to a matrix (column j = basis vector j). -/
noncomputable def onbToMatrix_real (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) : Matrix n n ℝ :=
  fun i j => (b j) i

/-- A matrix built from an orthonormal basis is orthogonal. -/
theorem onbToMatrix_real_mem_orthogonalGroup (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) :
    onbToMatrix_real b ∈ orthogonalGroup n ℝ := by
  rw [mem_orthogonalGroup_iff']
  ext i j
  simp only [mul_apply, transpose_apply, one_apply, onbToMatrix_real]
  have h_inner : @inner ℝ (EuclideanSpace ℝ n) _ (b i) (b j) = if i = j then 1 else 0 := by
    have h_on := b.orthonormal
    rw [orthonormal_iff_ite] at h_on
    exact h_on i j
  rw [← h_inner, inner_euclidean_eq_sum_real]

/-- The constructed orthogonal matrix U for real SVD. -/
noncomputable def constructedU_real (A : Matrix n n ℝ) : orthogonalGroup n ℝ :=
  ⟨onbToMatrix_real (extendedONB_real A), onbToMatrix_real_mem_orthogonalGroup _⟩

/-- Column j of constructed U equals the left singular vector when σⱼ ≠ 0. -/
theorem constructedU_real_column_eq (A : Matrix n n ℝ) (j : n) (hj : realSingularValues A j ≠ 0) :
    (fun i => (constructedU_real A : Matrix n n ℝ) i j) = leftSingularVectorNonzero_real A j hj := by
  ext i
  simp only [constructedU_real, onbToMatrix_real]
  have hj_mem : j ∈ nonzeroSingularIndices_real A := hj
  have h_spec := extendedONB_real_spec A j hj_mem
  have h_expand : leftSingularVectorExtended_real A j = leftSingularVectorEuclidean_real A j hj := dif_pos hj
  rw [h_spec, h_expand]
  simp only [leftSingularVectorEuclidean_real]
  rfl

/-- When σᵢ = 0, column i of A*V is zero. -/
lemma realAV_column_zero_of_singularValue_zero (A : Matrix n n ℝ) (i : n)
    (hi : realSingularValues A i = 0) :
    ∀ k, (realAV A) k i = 0 := by
  intro k
  have h_sum := realAV_column_norm_sq A i
  rw [hi] at h_sum
  simp only [sq, mul_zero] at h_sum
  -- Sum of squares = 0 implies each term = 0
  have h_each_nonneg : ∀ m, m ∈ Finset.univ → 0 ≤ (realAV A) m i * (realAV A) m i :=
    fun m _ => mul_self_nonneg _
  have h_each_zero := (Finset.sum_eq_zero_iff_of_nonneg h_each_nonneg).mp h_sum
  have hk := h_each_zero k (Finset.mem_univ k)
  exact mul_self_eq_zero.mp hk

/-- Key relationship: A * V = U * Σ for real matrices. -/
theorem realAV_eq_constructedU_real_mul_sigma (A : Matrix n n ℝ) :
    realAV A = (constructedU_real A : Matrix n n ℝ) * diagonal (realSingularValues A) := by
  ext i j
  simp only [mul_apply, diagonal_apply]
  -- RHS: ∑ x, U i x * (if x = j then σ x else 0) = U i j * σ j
  have h_rhs : ∑ x, (constructedU_real A : Matrix n n ℝ) i x *
               (if x = j then realSingularValues A x else 0) =
               (constructedU_real A : Matrix n n ℝ) i j * realSingularValues A j := by
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte]
    · intro b _ hbj; simp only [hbj, ↓reduceIte, mul_zero]
    · intro hj_not_mem; exact absurd (Finset.mem_univ j) hj_not_mem
  rw [h_rhs]
  by_cases hj : realSingularValues A j ≠ 0
  · -- Case σⱼ ≠ 0: (A*V)ᵢⱼ = σⱼ * Uᵢⱼ
    have h_col := constructedU_real_column_eq A j hj
    have h_U_eq : (constructedU_real A : Matrix n n ℝ) i j = leftSingularVectorNonzero_real A j hj i := by
      exact congrFun h_col i
    rw [h_U_eq]
    simp only [leftSingularVectorNonzero_real, realAV]
    -- Uᵢⱼ = (1/σⱼ) * (A*V)ᵢⱼ, so σⱼ * Uᵢⱼ = (A*V)ᵢⱼ
    field_simp
  · -- Case σⱼ = 0: both sides are 0
    push_neg at hj
    have h_AV_zero := realAV_column_zero_of_singularValue_zero A j hj
    simp only [hj, mul_zero, h_AV_zero i]

/-- **Real SVD Theorem**: Any square real matrix A can be decomposed as A = U * Σ * Vᵀ
    where U and V are orthogonal matrices and Σ is diagonal with non-negative entries.

    **Proof:**
    1. V = eigenvectors of Aᵀ * A (from spectral theorem, automatically orthogonal)
    2. σᵢ = √(eigenvalues of Aᵀ * A) (nonnegative since Aᵀ * A is positive semidefinite)
    3. U is constructed by:
       - For σᵢ ≠ 0: column i = (1/σᵢ) * A * vᵢ (normalized left singular vector)
       - For σᵢ = 0: extend orthonormally to complete the basis
    4. The equation A = U * Σ * Vᵀ follows from A * V = U * Σ and V * Vᵀ = I -/
theorem svd_decomposition (A : Matrix n n ℝ) :
    ∃ (U V : Matrix.orthogonalGroup n ℝ) (σ : n → ℝ),
      (∀ i, 0 ≤ σ i) ∧
      A = (U : Matrix n n ℝ) * diagonal σ * (V : Matrix n n ℝ)ᵀ := by
  -- Use constructed U and V
  use constructedU_real A, rightOrthogonal A, realSingularValues A
  constructor
  · -- Singular values are nonnegative
    intro i
    exact Real.sqrt_nonneg _
  · -- Main equation: A = U * Σ * Vᵀ
    -- From realAV_eq_constructedU_real_mul_sigma: A * V = U * Σ
    -- Multiply both sides by Vᵀ: A * V * Vᵀ = U * Σ * Vᵀ
    -- Since V is orthogonal: V * Vᵀ = I, so A = U * Σ * Vᵀ
    have h_AV := realAV_eq_constructedU_real_mul_sigma A
    have hV := (rightOrthogonal A).2
    have h_V_VT : (rightOrthogonal A : Matrix n n ℝ) * (rightOrthogonal A : Matrix n n ℝ)ᵀ = 1 := by
      rw [mem_orthogonalGroup_iff] at hV
      exact hV
    calc A = A * 1 := by rw [mul_one]
      _ = A * ((rightOrthogonal A : Matrix n n ℝ) * (rightOrthogonal A : Matrix n n ℝ)ᵀ) := by rw [h_V_VT]
      _ = (A * (rightOrthogonal A : Matrix n n ℝ)) * (rightOrthogonal A : Matrix n n ℝ)ᵀ := by rw [mul_assoc]
      _ = realAV A * (rightOrthogonal A : Matrix n n ℝ)ᵀ := rfl
      _ = ((constructedU_real A : Matrix n n ℝ) * diagonal (realSingularValues A)) *
          (rightOrthogonal A : Matrix n n ℝ)ᵀ := by rw [h_AV]
      _ = (constructedU_real A : Matrix n n ℝ) * diagonal (realSingularValues A) *
          (rightOrthogonal A : Matrix n n ℝ)ᵀ := by rw [mul_assoc]

end Matrix.SVD.Real

/-! ### Helper lemmas for eigenvalues₀ -/

/-- eigenvalues₀ are nonneg for PosSemidef matrices.
    Transfer from `PosSemidef.eigenvalues_nonneg` via the bijection
    `eigenvalues j = eigenvalues₀ (equivOfCardEq.symm j)`. -/
lemma PosSemidef_eigenvalues₀_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : Fin (Fintype.card n)) :
    0 ≤ hA.isHermitian.eigenvalues₀ i := by
  have h := hA.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)
  unfold IsHermitian.eigenvalues at h
  simp only [Equiv.symm_apply_apply] at h
  exact h

/-- For an antitone nonneg function on Fin n, if only the first k values can be nonzero,
    then values at indices ≥ k are 0.
    Used to prove `eigenvalues₀_zero_beyond_rank`. -/
lemma antitone_nonneg_zeros_after_rank {n k : ℕ} (f : Fin n → ℝ)
    (h_anti : Antitone f) (h_nonneg : ∀ i, 0 ≤ f i)
    (h_card : Fintype.card {i : Fin n // f i ≠ 0} ≤ k)
    (i : Fin n) (hi : k ≤ i.val) : f i = 0 := by
  by_contra h_ne
  -- If f i ≠ 0, then all f j for j ≤ i are also ≠ 0 (by antitone + nonneg)
  have h_all_nonzero : ∀ j : Fin n, j ≤ i → f j ≠ 0 := by
    intro j hji h_fj_zero
    have h_fi_pos : 0 < f i := (h_nonneg i).lt_of_ne' h_ne
    have h_fj_ge : f j ≥ f i := h_anti hji
    linarith [h_fj_zero.symm ▸ h_fj_ge]
  -- So {j | f j ≠ 0} ⊇ {j | j ≤ i}, which has at least i.val + 1 elements
  have h_count : i.val + 1 ≤ Fintype.card {j : Fin n // f j ≠ 0} := by
    have h_iic : (Finset.Iic i).card = i.val + 1 := by simp [Fin.card_Iic]
    calc i.val + 1 = (Finset.Iic i).card := h_iic.symm
      _ ≤ (Finset.univ.filter (fun j : Fin n => f j ≠ 0)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_all_nonzero j (Finset.mem_Iic.mp hj)
      _ = Fintype.card {j : Fin n // f j ≠ 0} := by rw [Fintype.card_subtype]
  -- But i.val + 1 > k ≥ card {j | f j ≠ 0}, contradiction
  omega


end Hagi.External.Flywheel
