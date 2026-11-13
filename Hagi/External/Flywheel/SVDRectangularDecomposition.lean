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
import Hagi.External.Flywheel.SVDRectangularNorms

/-!
# SVDRectangularDecomposition

Rectangular main construction: unitary `U`, `V`, rectangular diagonal `S` with `A * V = U * S` and `A = U * S * Vᴴ`.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

namespace Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Main Construction -/

set_option linter.unusedSectionVars false in
/-- Left singular vector as EuclideanSpace ℂ m element (rectangular case).
    For j : n with σⱼ ≠ 0, this is the normalized column j of A*V. -/
noncomputable def leftSingularVectorEuclidean_rectangular (A : Matrix m n ℂ) (j : n)
    (hj : singularValueFromEigenvalue A j ≠ 0) : EuclideanSpace ℂ m :=
  (WithLp.equiv 2 (m → ℂ)).symm (leftSingularVectorNonzero_rectangular A j hj)

/-- The set of column indices with nonzero singular values (rectangular case).
    These are the indices j : n for which σⱼ ≠ 0. -/
def nonzeroSingularIndices_rectangular (A : Matrix m n ℂ) : Set n :=
  {j | singularValueFromEigenvalue A j ≠ 0}

/-- Extended function for all column indices: uses left singular vector when σⱼ ≠ 0, else 0.
    This maps n → EuclideanSpace ℂ m (columns to m-dimensional vectors). -/
noncomputable def leftSingularVectorExtended_rectangular (A : Matrix m n ℂ) :
    n → EuclideanSpace ℂ m :=
  fun j => if h : singularValueFromEigenvalue A j ≠ 0
           then leftSingularVectorEuclidean_rectangular A j h
           else 0

/-- The left singular vectors (restricted to nonzero σⱼ) form an orthonormal set.
    This is the key lemma enabling ONB extension. -/
theorem leftSingularVectorExtended_orthonormal_on_nonzero_rectangular (A : Matrix m n ℂ) :
    Orthonormal ℂ ((nonzeroSingularIndices_rectangular A).domRestrict
                   (leftSingularVectorExtended_rectangular A)) := by
  rw [orthonormal_iff_ite]
  intro ⟨j, hj⟩ ⟨j', hj'⟩
  unfold nonzeroSingularIndices_rectangular at hj hj'
  have hj_dif : (if h : singularValueFromEigenvalue A j ≠ 0
                then leftSingularVectorEuclidean_rectangular A j h else 0)
               = leftSingularVectorEuclidean_rectangular A j hj := dif_pos hj
  have hj'_dif : (if h : singularValueFromEigenvalue A j' ≠ 0
                 then leftSingularVectorEuclidean_rectangular A j' h else 0)
                = leftSingularVectorEuclidean_rectangular A j' hj' := dif_pos hj'
  unfold leftSingularVectorExtended_rectangular
  rw [Set.domRestrict_apply, Set.domRestrict_apply]
  rw [hj_dif, hj'_dif]
  simp only [leftSingularVectorEuclidean_rectangular]
  rw [inner_euclidean_eq_sum]
  by_cases h : j = j'
  · subst h
    simp only [↓reduceIte]
    exact leftSingularVectorNonzero_rectangular_inner_self A j hj
  · have hjj' : (⟨j, hj⟩ : {j : n | singularValueFromEigenvalue A j ≠ 0}) ≠ ⟨j', hj'⟩ := by
      intro heq; apply h; exact Subtype.ext_iff.mp heq
    split
    · next heq => exact absurd (Subtype.ext_iff.mp heq) h
    · exact leftSingularVectorNonzero_rectangular_orthogonal A j j' hj hj' h

/-! #### Orthonormal Basis Extension -/

/-- For k : m, find the corresponding j : n on the diagonal. -/
noncomputable def correspondingN (k : m) : Option n :=
  if h : (eigenvaluesBijection m k).val < Fintype.card n then
    some ((eigenvaluesBijection n).symm ⟨(eigenvaluesBijection m k).val, h⟩)
  else
    none

set_option linter.unusedSectionVars false in
/-- When correspondingN returns Some j, the indices align on the diagonal. -/
lemma correspondingN_spec (k : m) (j : n) (hj : correspondingN k = some j) :
    (eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val := by
  unfold correspondingN at hj
  split_ifs at hj with h
  · simp only [Option.some.injEq] at hj
    subst hj; simp only [Equiv.apply_symm_apply]

/-- The correspondence is injective: different k give different j. -/
lemma correspondingN_injective (k k' : m) (j : n)
    (hk : correspondingN k = some j) (hk' : correspondingN k' = some j) : k = k' := by
  have h1 := correspondingN_spec k j hk
  have h2 := correspondingN_spec k' j hk'
  have h3 : (eigenvaluesBijection m k).val = (eigenvaluesBijection m k').val := by
    rw [h1, h2]
  have h4 : eigenvaluesBijection m k = eigenvaluesBijection m k' := Fin.ext h3
  exact (eigenvaluesBijection m).injective h4

/-- Left singular vectors indexed by m: for k : m, use uⱼ if k corresponds to j with σⱼ ≠ 0, else 0. -/
noncomputable def leftSingularVectorByM (A : Matrix m n ℂ) (k : m) : EuclideanSpace ℂ m :=
  match correspondingN k with
  | some j => if h : singularValueFromEigenvalue A j ≠ 0
              then leftSingularVectorEuclidean_rectangular A j h
              else 0
  | none => 0

/-- The set of m-indices that correspond to nonzero singular values. -/
def nonzeroSingularIndicesM (A : Matrix m n ℂ) : Set m :=
  {k | ∃ j, correspondingN k = some j ∧ singularValueFromEigenvalue A j ≠ 0}

set_option linter.unusedSectionVars false in
/-- Helper: when k ∈ nonzeroSingularIndicesM, leftSingularVectorByM equals the corresponding left singular vector. -/
lemma leftSingularVectorByM_eq (A : Matrix m n ℂ) (k : m) (j : n)
    (hcorr : correspondingN k = some j) (hj : singularValueFromEigenvalue A j ≠ 0) :
    leftSingularVectorByM A k = leftSingularVectorEuclidean_rectangular A j hj := by
  unfold leftSingularVectorByM
  simp only [hcorr, dif_pos hj]

/-- The left singular vectors indexed by m are orthonormal on the nonzero set. -/
theorem leftSingularVectorByM_orthonormal_on_nonzero (A : Matrix m n ℂ) :
    Orthonormal ℂ ((nonzeroSingularIndicesM A).domRestrict (leftSingularVectorByM A)) := by
  rw [orthonormal_iff_ite]
  intro ⟨k, hk⟩ ⟨k', hk'⟩
  unfold nonzeroSingularIndicesM at hk hk'
  obtain ⟨j, hcorr, hj⟩ := hk
  obtain ⟨j', hcorr', hj'⟩ := hk'
  rw [Set.domRestrict_apply, Set.domRestrict_apply]
  rw [leftSingularVectorByM_eq A k j hcorr hj, leftSingularVectorByM_eq A k' j' hcorr' hj']
  unfold leftSingularVectorEuclidean_rectangular
  rw [inner_euclidean_eq_sum]
  by_cases h : k = k'
  · -- Same index k = k', so j = j' by injectivity
    subst h
    have hj_eq : j = j' := by
      have h_eq : some j = some j' := hcorr.symm.trans hcorr'
      exact Option.some_injective _ h_eq
    subst hj_eq
    simp only [↓reduceIte]
    exact leftSingularVectorNonzero_rectangular_inner_self A j hj
  · -- Different k ≠ k', need to show j ≠ j' or inner product is 0
    have hjj' : j ≠ j' := by
      intro heq
      subst heq
      exact h (correspondingN_injective k k' j hcorr hcorr')
    split
    · next heq => exact absurd (Subtype.ext_iff.mp heq) h
    · exact leftSingularVectorNonzero_rectangular_orthogonal A j j' hj hj' hjj'

/-- Extend the m-indexed left singular vectors to a full orthonormal basis.
    This uses `exists_orthonormalBasis_extension_of_card_eq` to get an ONB indexed by m
    that agrees with the left singular vectors on the diagonal nonzero positions. -/
noncomputable def extendedONB_rectangular_v2 (A : Matrix m n ℂ) :
    OrthonormalBasis m ℂ (EuclideanSpace ℂ m) :=
  (leftSingularVectorByM_orthonormal_on_nonzero A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace |>.choose

/-- The extended ONB agrees with left singular vectors on the nonzero diagonal positions. -/
theorem extendedONB_rectangular_v2_spec (A : Matrix m n ℂ) (k : m) (hk : k ∈ nonzeroSingularIndicesM A) :
    (extendedONB_rectangular_v2 A) k = leftSingularVectorByM A k :=
  (leftSingularVectorByM_orthonormal_on_nonzero A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace |>.choose_spec k hk

/-! ##### Original Orthonormal Basis Extension (kept for compatibility) -/

/-- Extend the orthonormal left singular vectors to a full orthonormal basis of EuclideanSpace ℂ m.

    Note: The partial set is indexed by a subset of n (columns with σⱼ ≠ 0), but the full
    basis must be indexed by m. The extension theorem handles this mismatch by constructing
    a basis indexed by m that agrees with our vectors on their domain. -/
noncomputable def extendedONB_rectangular (A : Matrix m n ℂ) :
    OrthonormalBasis m ℂ (EuclideanSpace ℂ m) := by
  let s := nonzeroSingularIndices_rectangular A
  let v := leftSingularVectorExtended_rectangular A
  have h_on := leftSingularVectorExtended_orthonormal_on_nonzero_rectangular A
  -- The range of the restricted function forms an orthonormal set
  let restricted_v := s.domRestrict v
  have h_inj : Function.Injective restricted_v := h_on.linearIndependent.injective
  -- Convert to orthonormal on the range (as a set)
  have h_img_on : Orthonormal ℂ ((↑) : Set.range restricted_v → EuclideanSpace ℂ m) :=
    (orthonormal_subtype_range h_inj).mpr h_on
  -- Get extension - use Classical.choose to extract the witnesses
  let ext_proof := h_img_on.exists_orthonormalBasis_extension
  let u : Finset (EuclideanSpace ℂ m) := ext_proof.choose
  let b : OrthonormalBasis u ℂ (EuclideanSpace ℂ m) := ext_proof.choose_spec.choose
  -- Reindex to m using cardinality equality
  -- Fintype.card u = u.card by Fintype.card_coe
  -- u.card = finrank by Module.finrank_eq_card_finset_basis
  -- finrank = Fintype.card m by finrank_euclideanSpace
  have h_card : Fintype.card u = Fintype.card m := by
    rw [Fintype.card_coe, (Module.finrank_eq_card_finset_basis b.toBasis).symm,
        finrank_euclideanSpace]
  exact b.reindex (Fintype.equivOfCardEq h_card)

/-! #### Unitary Matrix Construction

Convert the orthonormal basis to a unitary matrix in unitaryGroup m ℂ.
-/

/-- The constructed unitary matrix U for rectangular SVD.
    Columns are derived from the extended orthonormal basis (v2 with diagonal alignment). -/
noncomputable def constructedU_rectangular (A : Matrix m n ℂ) : unitaryGroup m ℂ :=
  ⟨onbToMatrix (extendedONB_rectangular_v2 A),
   onbToMatrix_mem_unitaryGroup _⟩

/-- Column k of constructedU_rectangular equals the left singular vector uⱼ
    when k corresponds to j (via diagonal correspondence) and σⱼ ≠ 0. -/
theorem constructedU_rectangular_column_spec (A : Matrix m n ℂ) (k : m) (j : n)
    (hcorr : correspondingN k = some j) (hj : singularValueFromEigenvalue A j ≠ 0) :
    (fun i => (constructedU_rectangular A : Matrix m m ℂ) i k) =
    leftSingularVectorNonzero_rectangular A j hj := by
  ext i
  simp only [constructedU_rectangular, onbToMatrix]
  have hk_mem : k ∈ nonzeroSingularIndicesM A := ⟨j, hcorr, hj⟩
  have h_spec := extendedONB_rectangular_v2_spec A k hk_mem
  rw [h_spec, leftSingularVectorByM_eq A k j hcorr hj]
  simp only [leftSingularVectorEuclidean_rectangular]
  rfl

/-! #### Diagonal Correspondence Helpers

For the rectangular SVD equation A*V = U*S, we need to track which row index k : m
corresponds to which column index j : n on the "diagonal" of the rectangular matrix S.
-/

/-- Given j : n, find the corresponding k : m on the diagonal of S (if it exists).
    Returns Some k when (eigenvaluesBijection n j).val < #m, i.e., when j is in the "diagonal range".
    Uses eigenvaluesBijection to be consistent with eigenvalue/eigenvector indexing. -/
noncomputable def diagonalK (j : n) : Option m :=
  if h : (eigenvaluesBijection n j).val < Fintype.card m then
    some ((eigenvaluesBijection m).symm ⟨(eigenvaluesBijection n j).val, h⟩)
  else
    none

set_option linter.unusedSectionVars false in
/-- When diagonalK returns Some k, the indices align on the diagonal. -/
lemma diagonalK_spec (j : n) (k : m) (hk : diagonalK j = some k) :
    (eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val := by
  unfold diagonalK at hk
  split_ifs at hk with h
  · simp only [Option.some.injEq] at hk
    subst hk; simp only [Equiv.apply_symm_apply]

set_option linter.unusedSectionVars false in
/-- When #n ≤ #m, every j has a corresponding k on the diagonal. -/
lemma diagonalK_isSome_of_card_le (hn : Fintype.card n ≤ Fintype.card m) (j : n) :
    (diagonalK (m := m) (n := n) j).isSome = true := by
  unfold diagonalK
  have h : (eigenvaluesBijection n j).val < Fintype.card m := by
    calc (eigenvaluesBijection n j).val < Fintype.card n := (eigenvaluesBijection n j).isLt
      _ ≤ Fintype.card m := hn
  simp only [h, ↓reduceDIte, Option.isSome_some]

set_option linter.unusedSectionVars false in
/-- The singular diagonal entry S(k,j) is nonzero only at the diagonal position for j. -/
lemma singularDiagonal_eq_zero_of_ne_diagonalK (A : Matrix m n ℂ) (j : n) (k : m)
    (hk : diagonalK j ≠ some k) : singularDiagonal A k j = 0 := by
  unfold singularDiagonal
  -- After unfolding, we have: if h : ... then ... else 0
  -- S k j ≠ 0 requires (eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val ∧ ... < min(#m, #n)
  -- If k is not the diagonal match for j, then the first condition fails
  by_cases h_in_range : (eigenvaluesBijection n j).val < Fintype.card m
  · -- j is in diagonal range, so diagonalK j = some k₀ for some k₀
    have h_some : diagonalK (m := m) (n := n) j = some ((eigenvaluesBijection m).symm ⟨(eigenvaluesBijection n j).val, h_in_range⟩) := by
      unfold diagonalK; simp only [h_in_range, ↓reduceDIte]
    -- Since hk says k ≠ that k₀, we have (eigenvaluesBijection m k).val ≠ (eigenvaluesBijection n j).val
    have h_ne : (eigenvaluesBijection m k).val ≠ (eigenvaluesBijection n j).val := by
      intro heq
      apply hk
      unfold diagonalK
      simp only [h_in_range, ↓reduceDIte, Option.some.injEq]
      have h_fin_eq : eigenvaluesBijection m k = ⟨(eigenvaluesBijection n j).val, h_in_range⟩ := by
        ext; exact heq
      have h_apply : (eigenvaluesBijection m).symm (eigenvaluesBijection m k) = k := (eigenvaluesBijection m).symm_apply_apply k
      rw [h_fin_eq] at h_apply
      exact h_apply
    -- Now the dif_pos condition fails: need to show ¬(fi.val = fj.val ∧ fi.val < min)
    have h_cond_false : ¬((eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val ∧
        (eigenvaluesBijection m k).val < min (Fintype.card m) (Fintype.card n)) := by
      intro ⟨h_eq, _⟩
      exact h_ne h_eq
    simp only [dif_neg h_cond_false]
  · -- j is out of diagonal range, so S k j = 0 for all k
    have h_none : diagonalK (m := m) (n := n) j = none := by
      unfold diagonalK; simp only [h_in_range, ↓reduceDIte]
    -- (eigenvaluesBijection n j).val ≥ #m, so (eigenvaluesBijection m k).val < #m ≤ (eigenvaluesBijection n j).val
    have h_cond_false : ¬((eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val ∧
        (eigenvaluesBijection m k).val < min (Fintype.card m) (Fintype.card n)) := by
      intro ⟨h_eq, _⟩
      have h_lt_m : (eigenvaluesBijection m k).val < Fintype.card m := (eigenvaluesBijection m k).isLt
      rw [h_eq] at h_lt_m
      exact h_in_range h_lt_m
    simp only [dif_neg h_cond_false]

/-- When diagonalK j = some k, the singular diagonal value at (k,j) equals the singular value. -/
lemma singularDiagonal_at_diagonalK (A : Matrix m n ℂ) (j : n) (k : m)
    (hk : diagonalK j = some k)
    (h_in_min : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    singularDiagonal A k j = Complex.ofReal (singularValues A ⟨(eigenvaluesBijection n j).val, h_in_min⟩) := by
  unfold singularDiagonal
  have h_eq := diagonalK_spec j k hk
  have h_cond : (eigenvaluesBijection m k).val = (eigenvaluesBijection n j).val ∧
                (eigenvaluesBijection m k).val < min (Fintype.card m) (Fintype.card n) := by
    constructor
    · exact h_eq
    · rw [h_eq]; exact h_in_min
  simp only [dif_pos h_cond]
  -- The two Fin values have same underlying nat value by h_eq
  have h_fin_eq : (⟨(eigenvaluesBijection m k).val, h_cond.2⟩ : Fin (min (Fintype.card m) (Fintype.card n))) =
                  ⟨(eigenvaluesBijection n j).val, h_in_min⟩ := by
    ext
    exact h_eq
  rw [h_fin_eq]

/-! #### Core Equation: A*V = U*S

The main theorem of prove that A*V equals U*S column by column.

For column j (with j : n):
- If σⱼ ≠ 0: (A*V)[:,j] = σⱼ · uⱼ by construction of left singular vectors
- If σⱼ = 0: (A*V)[:,j] = 0 and (U*S)[:,j] = 0 (since S has zero in that diagonal position)

Note: S is m×n, so we need to handle the case where j corresponds to a diagonal
position (j < min(m,n)) vs an off-diagonal zero.
-/

/-- Column j of A*V is zero when the corresponding eigenvalue (and hence singular value) is zero. -/
lemma AV_column_zero_of_eigenvalue_zero_rectangular (A : Matrix m n ℂ) (j : n)
    (hj : singularValueFromEigenvalue A j = 0) :
    ∀ i, (A * (rightUnitary A : Matrix n n ℂ)) i j = 0 := by
  intro i
  -- The sum ∑ k, star(AV k j) * (AV k j) = eigenvalue j = 0 when hj holds
  have h_sum := AV_column_norm_sq_rectangular A j
  simp only at h_sum
  -- singularValueFromEigenvalue A j = 0 means eigenvalues j = 0 (since it's sqrt of eigenvalue)
  unfold singularValueFromEigenvalue at hj
  have h_eig_zero : (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j = 0 := by
    have h_nonneg := (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg j
    exact Real.sqrt_eq_zero h_nonneg |>.mp hj
  rw [h_eig_zero, Complex.ofReal_zero] at h_sum
  -- Each term star(z) * z = |z|² ≥ 0
  let AV := (A * (rightUnitary A : Matrix n n ℂ))
  have h_eq_normSq : ∀ k, star (AV k j) * AV k j = Complex.normSq (AV k j) := by
    intro k
    have h1 : star (AV k j) = (starRingEnd ℂ) (AV k j) := rfl
    rw [h1]
    have h2 : (starRingEnd ℂ) (AV k j) * AV k j = AV k j * (starRingEnd ℂ) (AV k j) := mul_comm _ _
    rw [h2, mul_comm]
    exact Complex.normSq_eq_conj_mul_self.symm
  have h_sum_normSq_complex : ∑ k, (Complex.normSq (AV k j) : ℂ) = 0 := by
    conv_lhs => rw [← Finset.sum_congr rfl (fun k _ => h_eq_normSq k)]
    exact h_sum
  have h_sum_normSq : ∑ k, Complex.normSq (AV k j) = 0 := by
    have h_real : (∑ k, Complex.normSq (AV k j) : ℂ) = (∑ k, Complex.normSq (AV k j) : ℝ) := by
      rw [Complex.ofReal_sum]
    rw [h_real] at h_sum_normSq_complex
    exact Complex.ofReal_injective h_sum_normSq_complex
  have h_each_zero := @Finset.sum_eq_zero_iff_of_nonneg m ℝ _ _ (fun k => Complex.normSq (AV k j))
    Finset.univ _ (fun k _ => Complex.normSq_nonneg _)
  rw [h_each_zero] at h_sum_normSq
  have hi := h_sum_normSq i (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp hi

/-- **Core equation for rectangular SVD**: A * V = U * S

    This is the central identity that makes SVD work:
    - A is m × n
    - V = rightUnitary A is n × n unitary
    - U = constructedU_rectangular A is m × m unitary
    - S = singularDiagonal A is m × n with singular values on the "diagonal"

    The proof proceeds entry by entry:
    - Find the unique diagonal k (if it exists) where S k j ≠ 0
    - When σⱼ ≠ 0: use constructedU_rectangular_column_spec to relate U[:,k] to uⱼ
    - When σⱼ = 0 or off-diagonal: both sides are zero -/
theorem AV_eq_US_rectangular (A : Matrix m n ℂ) :
    A * (rightUnitary A : Matrix n n ℂ) =
    (constructedU_rectangular A : Matrix m m ℂ) * singularDiagonal A := by
  ext i j
  simp only [mul_apply]
  -- RHS: ∑ k, U i k * S k j
  -- S k j is nonzero only when k = diagonalK j (the diagonal position for j)

  -- Case split: is j in the "diagonal range" (has corresponding k)?
  by_cases h_in_range : (eigenvaluesBijection n j).val < Fintype.card m
  · -- j has a corresponding k on the diagonal
    let k₀ := (eigenvaluesBijection m).symm ⟨(eigenvaluesBijection n j).val, h_in_range⟩
    have h_diagonalK : diagonalK j = some k₀ := by
      unfold diagonalK; simp only [h_in_range, ↓reduceDIte]; rfl

    -- The sum collapses to just the k₀ term
    have h_sum_eq : ∑ k, (constructedU_rectangular A : Matrix m m ℂ) i k * singularDiagonal A k j =
                   (constructedU_rectangular A : Matrix m m ℂ) i k₀ * singularDiagonal A k₀ j := by
      apply Finset.sum_eq_single k₀
      · intro k _ hk_ne
        have h_zero := singularDiagonal_eq_zero_of_ne_diagonalK A j k
          (by rw [h_diagonalK]; intro h; exact hk_ne (Option.some_injective _ h.symm))
        simp only [h_zero, mul_zero]
      · intro h_not_mem
        exact absurd (Finset.mem_univ k₀) h_not_mem
    rw [h_sum_eq]

    -- Case split on whether σⱼ ≠ 0
    by_cases hj : singularValueFromEigenvalue A j ≠ 0
    · -- Case 1a: σⱼ ≠ 0 - use the column spec
      -- First, establish correspondingN k₀ = some j
      have h_corr : correspondingN k₀ = some j := by
        unfold correspondingN
        have h_lt : (eigenvaluesBijection m k₀).val < Fintype.card n := by
          simp only [k₀]; simp only [Equiv.apply_symm_apply]
          exact (eigenvaluesBijection n j).isLt
        simp only [dif_pos h_lt, Option.some.injEq]
        have h_eq : (eigenvaluesBijection m k₀).val = (eigenvaluesBijection n j).val := by
          simp only [k₀]; simp only [Equiv.apply_symm_apply]
        have h_fin_eq : (⟨(eigenvaluesBijection m k₀).val, h_lt⟩ : Fin (Fintype.card n)) =
                       eigenvaluesBijection n j := by ext; exact h_eq
        rw [h_fin_eq]; simp only [Equiv.symm_apply_apply]

      -- Get the column spec: U[:,k₀] = uⱼ
      have h_col := constructedU_rectangular_column_spec A k₀ j h_corr hj
      have h_U_eq : (constructedU_rectangular A : Matrix m m ℂ) i k₀ =
                   leftSingularVectorNonzero_rectangular A j hj i := congrFun h_col i

      -- The singular diagonal value at (k₀, j)
      have h_in_min : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n) := by
        apply Nat.lt_min.mpr ⟨h_in_range, (eigenvaluesBijection n j).isLt⟩
      have h_S_val := singularDiagonal_at_diagonalK A j k₀ h_diagonalK h_in_min
      rw [h_S_val, h_U_eq]

      -- uⱼ i * σ_from_singularValues = (A*V) i j
      -- where uⱼ i = (1/σⱼ) * (A*V) i j (by definition)
      simp only [leftSingularVectorNonzero_rectangular]

      -- Need: singularValues A ⟨idx, _⟩ = singularValueFromEigenvalue A j
      -- Now that singularValues always uses Aᴴ*A, this follows directly
      have h_sv_eq : singularValues A ⟨(eigenvaluesBijection n j).val, h_in_min⟩ =
                    singularValueFromEigenvalue A j :=
        singularValues_eq_singularValueFromEigenvalue A j h_in_min
      rw [h_sv_eq]

      have hj' : (Complex.ofReal (singularValueFromEigenvalue A j) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]; exact hj
      field_simp
      ring_nf
      rfl  -- Goal: ∑ x, A i x * ↑(rightUnitary A) x j = (A * ↑(rightUnitary A)) i j

    · -- Case 1b: σⱼ = 0 - both sides are zero
      push_neg at hj
      -- LHS: (A*V) i j = 0 when σⱼ = 0
      have h_AV_zero := AV_column_zero_of_eigenvalue_zero_rectangular A j hj

      -- RHS: U i k₀ * S k₀ j, need to show S k₀ j = 0 when σⱼ = 0
      have h_S_zero : singularDiagonal A k₀ j = 0 := by
        unfold singularDiagonal
        simp only
        split_ifs with h_diag
        · -- At diagonal position, the value is singularValues A ⟨idx, _⟩
          have h_eq := h_diag.1
          have h_lt := h_diag.2
          -- Convert h_lt from (eigenvaluesBijection m k₀).val < min ... to (eigenvaluesBijection n j).val < min ...
          have h_in_min_j : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n) := by
            rw [← h_eq]; exact h_lt
          have h_sv_eq : singularValues A ⟨(eigenvaluesBijection n j).val, h_in_min_j⟩ =
                        singularValueFromEigenvalue A j :=
            singularValues_eq_singularValueFromEigenvalue A j h_in_min_j
          -- The Fin index h_lt vs h_in_min_j: they have the same .val (via h_eq)
          have h_idx_eq : (⟨(eigenvaluesBijection m k₀).val, h_lt⟩ : Fin (min (Fintype.card m) (Fintype.card n))) =
                         ⟨(eigenvaluesBijection n j).val, h_in_min_j⟩ := by
            ext; exact h_eq
          rw [h_idx_eq, h_sv_eq, hj, Complex.ofReal_zero]
        · rfl
      -- The goal is: (A*V) i j = U i k₀ * S k₀ j
      -- LHS = 0 by h_AV_zero, RHS = 0 by h_S_zero
      rw [h_S_zero, mul_zero]
      -- Now goal is: (A*V) i j = 0
      exact h_AV_zero i

  · -- Case 2: j outside diagonal range - all S k j = 0, need (A*V) i j = 0
    have h_all_zero : ∀ k, singularDiagonal A k j = 0 := by
      intro k
      unfold singularDiagonal
      simp only
      split_ifs with h_diag
      · have h_lt_m : (eigenvaluesBijection m k).val < Fintype.card m := (eigenvaluesBijection m k).isLt
        have h_ge_m : (eigenvaluesBijection n j).val ≥ Fintype.card m := le_of_not_gt h_in_range
        omega
      · rfl
    simp only [h_all_zero, mul_zero, Finset.sum_const_zero]

    -- Need: (A*V) i j = 0 when j is outside diagonal range
    -- This requires: singularValueFromEigenvalue A j = 0 for such j
    -- Which follows from rank considerations: rank(AᴴA) ≤ min(m,n) = m
    -- For j with index ≥ m, the eigenvalue is 0
    have h_sigma_zero : singularValueFromEigenvalue A j = 0 := by
      -- When idx(j) ≥ m and m < n, the j-th eigenvalue of AᴴA is 0
      -- because AᴴA has at most m nonzero eigenvalues
      unfold singularValueFromEigenvalue
      -- eigenvalues j = eigenvalues₀ (equivOfCardEq.symm j) by Mathlib definition
      -- eigenvaluesBijection = equivFin = equivOfCardEq.symm by our bridge lemma
      have h_eq : (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j =
                  (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀
                    (eigenvaluesBijection n j) := by
        rfl
      rw [h_eq]
      -- Use eigenvalues₀_zero_beyond_rank since (eigenvaluesBijection n j).val ≥ card m
      have h_ge_m : (eigenvaluesBijection n j).val ≥ Fintype.card m := le_of_not_gt h_in_range
      have h_card_lt : Fintype.card m < Fintype.card n := by
        -- Since j exists and its index ≥ card m, we must have card m < card n
        exact Nat.lt_of_le_of_lt h_ge_m (eigenvaluesBijection n j).isLt
      have h_eig_zero := eigenvalues₀_zero_beyond_rank A (eigenvaluesBijection n j) h_ge_m h_card_lt
      rw [h_eig_zero]
      exact Real.sqrt_zero
    exact AV_column_zero_of_eigenvalue_zero_rectangular A j h_sigma_zero i

/-! #### Main Decomposition Theorem -/

/-- **Rectangular SVD Decomposition (Existence Form)**:
    Any m × n complex matrix A can be decomposed as A = U * S * Vᴴ
    where:
    - U ∈ unitaryGroup m ℂ (m × m unitary matrix of left singular vectors)
    - V ∈ unitaryGroup n ℂ (n × n unitary matrix of right singular vectors)
    - S : Matrix m n ℂ (rectangular "diagonal" with non-negative singular values)

    This is the natural extension of SVD to non-square matrices. -/
theorem svd_decomposition_rectangular (A : Matrix m n ℂ) :
    ∃ (U : unitaryGroup m ℂ) (V : unitaryGroup n ℂ) (S : Matrix m n ℂ),
      A = (U : Matrix m m ℂ) * S * star (V : Matrix n n ℂ) := by
  use constructedU_rectangular A, rightUnitary A, singularDiagonal A
  -- Main equation: A = U * S * Vᴴ
  have h_AV := AV_eq_US_rectangular A
  have h_V_unitary := mem_unitaryGroup_iff.mp (rightUnitary A).2
  calc A = A * (1 : Matrix n n ℂ) := by rw [Matrix.mul_one]
    _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [h_V_unitary]
    _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [Matrix.mul_assoc]
    _ = ((constructedU_rectangular A : Matrix m m ℂ) * singularDiagonal A) *
        star (rightUnitary A : Matrix n n ℂ) := by rw [h_AV]
    _ = (constructedU_rectangular A : Matrix m m ℂ) * singularDiagonal A *
        star (rightUnitary A : Matrix n n ℂ) := by rw [Matrix.mul_assoc]

end Matrix.SVD.Rectangular
end Hagi.External.Flywheel
