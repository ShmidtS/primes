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
import Hagi.External.Flywheel.SVDEigenvalues

/-!
# SVDDiagonal

Eigenvalues of diagonal matrices, product and sum properties of singular values, and `det A = ∏ σᵢ`.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

namespace Matrix.SVD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Eigenvalues of diagonal matrices -/

/-- For a diagonal matrix with real entries sorted decreasingly, eigenvalues equal the entries.

    The key insight is that `eigenvalues` is defined via sorting the roots of charpoly,
    and for a diagonal matrix `diagonal(d)`, the roots are exactly `{d_i | i}`.
    If `d` is already sorted decreasingly (via `eigenvalues₀_antitone`), then
    sorting is the identity, so `eigenvalues = d` pointwise.

    The formal proof uses:
    1. `charpoly_diagonal`: charpoly(diagonal(d)) = ∏(X - d_i)
    2. `sort_roots_charpoly_eq_eigenvalues₀`: sorted roots = eigenvalues₀
    3. `Antitone.ofFn_sorted`: antitone function gives sorted list
    4. `List.eq_of_perm_of_sorted`: two sorted lists with same elements are equal -/
private lemma eigenvalues_diagonal_of_sorted (f : Fin (Fintype.card n) → ℝ) (h_antitone : Antitone f) :
    let equiv := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n)
    let D := diagonal (Complex.ofReal ∘ f ∘ equiv.symm)
    ∀ (hD : D.IsHermitian), hD.eigenvalues₀ = f := by
  intro equiv D hD
  -- Strategy: Use that eigenvalues₀ = sorted roots of charpoly, and for diagonal matrices
  -- with antitone entries, sorting is the identity.
  --
  -- Key chain of equalities:
  -- 1. D.charpoly = ∏ i, (X - C (ofReal (f (equiv.symm i))))  [charpoly_diagonal]
  -- 2. D.charpoly.roots = multiset of {ofReal (f (equiv.symm i)) | i}
  -- 3. After mapping re and sorting by ≥: List.ofFn f
  -- 4. But sorted roots = List.ofFn eigenvalues₀  [sort_roots_charpoly_eq_eigenvalues₀]
  -- 5. By List.ofFn_inj: eigenvalues₀ = f

  -- Use sort_roots_charpoly_eq_eigenvalues₀ from Mathlib
  have h_sort_eq := hD.sort_roots_charpoly_eq_eigenvalues₀

  -- The charpoly of diagonal is product of (X - entries)
  have h_charpoly := charpoly_diagonal (Complex.ofReal ∘ f ∘ equiv.symm)

  -- Compute roots of the diagonal charpoly
  have h_roots : D.charpoly.roots = Finset.univ.val.map (fun i => Complex.ofReal (f (equiv.symm i))) := by
    rw [h_charpoly, Polynomial.roots_prod]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Function.comp_apply]
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => Polynomial.X_sub_C_ne_zero _

  -- Map re over the roots gives values in the range of f ∘ equiv.symm
  have h_roots_re : D.charpoly.roots.map Complex.re = (Finset.univ : Finset n).val.map (f ∘ equiv.symm) := by
    rw [h_roots]
    simp only [Multiset.map_map, Function.comp_apply, Complex.ofReal_re]

  -- Convert to Fin indexing using the equivalence
  have h_multiset_eq : (Finset.univ : Finset n).val.map (f ∘ equiv.symm) = (Finset.univ : Finset (Fin (Fintype.card n))).val.map f := by
    rw [← Multiset.map_map]
    congr 1
    ext x
    simp

  -- v4.34 port: List.Sorted / Antitone.ofFn_sorted removed
  have h_f_sorted : List.Pairwise (fun a b => decide (a ≥ b) = true) (List.ofFn f) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    rw [List.get_ofFn, List.get_ofFn]
    have h1 : f (Fin.cast (by simp [List.length_ofFn]) i)
        ≥ f (Fin.cast (by simp [List.length_ofFn]) j) :=
      h_antitone (by simpa [List.length_ofFn] using hij.le)
    exact decide_eq_true h1

  -- Sort of an already-sorted list is itself
  have h_sort_id : (D.charpoly.roots.map Complex.re).sort (· ≥ ·) = List.ofFn f := by
    rw [h_roots_re, h_multiset_eq]
    -- Finset.univ.val.map f = List.ofFn f as a Multiset
    have h_eq : ((Finset.univ : Finset (Fin (Fintype.card n))).val.map f : Multiset ℝ) = ↑(List.ofFn f) := by
      simp only [Fin.univ_val_map]
    rw [h_eq, Multiset.coe_sort]
    -- Sorting a sorted list returns itself
    have h_pw : List.Pairwise (fun a b => decide (a ≥ b) = true) (List.ofFn f) := h_f_sorted
    exact (List.ofFn f).mergeSort_of_pairwise h_pw

  -- Combine with sort_roots_charpoly_eq_eigenvalues₀
  have h_eq_lists : List.ofFn hD.eigenvalues₀ = List.ofFn f := by
    simp only [RCLike.re_eq_complex_re] at h_sort_eq
    rw [← h_sort_eq, h_sort_id]

  -- Extract function equality from list equality
  exact List.ofFn_injective h_eq_lists

lemma eigenvalues_sq {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n) :
    (hA.isHermitian.pow 2).eigenvalues i = (hA.isHermitian.eigenvalues i) ^ 2 := by
  /-
  Proof for PSD matrices using spectral theorem:
  1. A = U * diag(λ) * U* where U = eigenvectorUnitary, λ = eigenvalues
  2. A² = U * diag(λ²) * U*
  3. By charpoly_unitary_conj: charpoly(A²) = charpoly(diag(λ²))
  4. charpoly(diag(λ²)) = ∏ i, (X - C(λᵢ²))
  5. For PSD: λᵢ ≥ 0, sorted decreasingly, so λᵢ² are also sorted decreasingly
  6. By eigenvalues_eq_of_charpoly_eq: eigenvalues match pointwise
  -/
  -- Get the eigenvector unitary from spectral theorem
  let U := hA.isHermitian.eigenvectorUnitary
  let eig := hA.isHermitian.eigenvalues

  -- Step 1: Express A using spectral theorem
  have h_spectral : A = (U : Matrix n n ℂ) *
      diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by
    have := hA.isHermitian.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at this
    exact this

  -- Step 2: A² = U * D² * U*
  have h_sq : A ^ 2 = (U : Matrix n n ℂ) *
      diagonal (fun j => (Complex.ofReal (eig j)) ^ 2) * star (U : Matrix n n ℂ) := by
    rw [pow_two, h_spectral]
    -- (U * D * U*) * (U * D * U*) = U * D * (U* * U) * D * U* = U * D * D * U* = U * D² * U*
    have hUU : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 :=
      mem_unitaryGroup_iff'.mp U.2
    calc (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) *
        ((U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ))
        = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) *
          (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) *
          diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by
            simp only [Matrix.mul_assoc]
      _ = (U : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ eig) * 1 *
          diagonal (Complex.ofReal ∘ eig) * star (U : Matrix n n ℂ) := by rw [hUU]
      _ = (U : Matrix n n ℂ) * (diagonal (Complex.ofReal ∘ eig) *
          diagonal (Complex.ofReal ∘ eig)) * star (U : Matrix n n ℂ) := by
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (U : Matrix n n ℂ) * diagonal (fun j => (Complex.ofReal (eig j)) ^ 2) *
          star (U : Matrix n n ℂ) := by
        congr 1; congr 1
        rw [diagonal_mul_diagonal]
        congr 1
        ext j
        simp only [Function.comp_apply, sq]

  -- Step 3: charpoly(A²) = charpoly(D²) by unitary conjugation invariance
  have h_charpoly_eq : (A ^ 2).charpoly =
      (diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)).charpoly := by
    rw [h_sq]
    exact charpoly_unitary_conj _ U

  -- Step 4: charpoly of diagonal = product of (X - entries)
  have h_charpoly_diag : (diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)).charpoly =
      ∏ j, (Polynomial.X - Polynomial.C ((Complex.ofReal (eig j)) ^ 2)) := by
    exact charpoly_diagonal _

  -- Step 5: Relate to real diagonal for eigenvalues
  -- The eigenvalues of D² (as a Hermitian matrix) are eig²
  -- Need to show (A²).eigenvalues i = eigᵢ² using charpoly equality

  -- For PSD matrices, eigenvalues are non-negative and sorted decreasingly
  have h_nonneg : ∀ j, 0 ≤ eig j := fun j => PosSemidef.eigenvalues_nonneg hA j

  -- The diagonal matrix with entries eig² is Hermitian
  let D_sq := diagonal (fun j => (Complex.ofReal (eig j)) ^ 2)
  have h_D_herm : D_sq.IsHermitian := by
    rw [IsHermitian, diagonal_conjTranspose]
    congr 1
    ext j
    show star ((↑(hA.isHermitian.eigenvalues j) : ℂ) ^ 2) = (↑(hA.isHermitian.eigenvalues j)) ^ 2
    rw [star_pow]
    congr 1
    exact Complex.conj_ofReal _

  -- By eigenvalues_eq_eigenvalues_iff: matrices with same charpoly have same eigenvalues
  have h_eigenvalues_eq : (hA.isHermitian.pow 2).eigenvalues = h_D_herm.eigenvalues := by
    rw [IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact h_charpoly_eq

  -- Now we need: h_D_herm.eigenvalues i = (eig i)²
  -- Use eigenvalues_diagonal_of_sorted: for diagonal with sorted entries, eigenvalues₀ = entries
  have h_D_eigenvalues : h_D_herm.eigenvalues i = (eig i) ^ 2 := by
    -- eig₀ = eigenvalues₀ is antitone
    let eig₀ := hA.isHermitian.eigenvalues₀
    have h_eig₀_antitone := hA.isHermitian.eigenvalues₀_antitone

    -- eig₀² is also antitone (since eig₀ ≥ 0 from PSD)
    have h_eig₀_nonneg : ∀ j, 0 ≤ eig₀ j := by
      intro j
      have := hA.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
      simp only [IsHermitian.eigenvalues] at this
      simp at this
      exact this
    have h_eig₀_sq_antitone : Antitone (fun j => (eig₀ j) ^ 2) := by
      intro x y hxy
      rw [sq_le_sq, abs_of_nonneg (h_eig₀_nonneg y), abs_of_nonneg (h_eig₀_nonneg x)]
      exact h_eig₀_antitone hxy

    -- The diagonal matrix D_sq = diagonal(ofReal ∘ eig²) matches diagonal(ofReal ∘ eig₀² ∘ equiv.symm)
    -- where eig i = eig₀ (equiv.symm i), so (eig i)² = (eig₀ (equiv.symm i))²

    -- By eigenvalues_diagonal_of_sorted: eigenvalues₀ of D_sq = eig₀²
    -- And eigenvalues i = eigenvalues₀ (equiv.symm i) = (eig₀ (equiv.symm i))² = (eig i)²

    -- The key step uses that D_sq matches the structure expected by eigenvalues_diagonal_of_sorted
    -- D_sq = diagonal (fun j => (ofReal (eig j))²)
    --      = diagonal (fun j => ofReal ((eig j)²))  -- since (ofReal x)² = ofReal (x²)
    --      = diagonal (ofReal ∘ (fun j => (eig j)²))
    --      = diagonal (ofReal ∘ (fun j => (eig₀ (equiv.symm j))²))
    --      = diagonal (ofReal ∘ (fun j => (eig₀)² (equiv.symm j)))
    --      = diagonal (ofReal ∘ (eig₀)² ∘ equiv.symm)

    -- This matches eigenvalues_diagonal_of_sorted with f = (eig₀)²
    -- So h_D_herm.eigenvalues₀ = (eig₀)²
    -- And h_D_herm.eigenvalues i = h_D_herm.eigenvalues₀ (equiv.symm i) = (eig₀ (equiv.symm i))² = (eig i)²

    have h_D_eq : D_sq = diagonal (Complex.ofReal ∘ (fun j => (eig₀ j)^2) ∘
        (Fintype.equivOfCardEq (Fintype.card_fin _)).symm) := by
      simp only [D_sq, eig, eig₀]
      congr 1
      ext j
      simp only [Function.comp_apply, IsHermitian.eigenvalues]
      norm_cast

    have h_eigval₀ := eigenvalues_diagonal_of_sorted (fun j => (eig₀ j)^2) h_eig₀_sq_antitone
    specialize h_eigval₀ (h_D_eq ▸ h_D_herm)
    -- h_eigval₀ : (h_D_eq ▸ h_D_herm).eigenvalues₀ = fun j => (eig₀ j)²

    simp only [IsHermitian.eigenvalues]
    -- Goal: eigenvalues₀ (equiv.symm i) = (eig₀ (equiv.symm i))²
    -- Use h_eigval₀ after handling the dependent type rewrite

    -- Key insight: h_D_eq is essentially a definitional equality after unfolding let bindings
    -- The eigenvalues₀ only depends on the matrix, and the matrices are definitionally equal
    have key : h_D_herm.eigenvalues₀ = fun j => (eig₀ j)^2 := by
      convert h_eigval₀ using 2
    rw [key]
    -- Goal: (fun j => eig₀ j ^ 2) (equiv.symm i) = eig i ^ 2
    -- Since eig i = eig₀ (equiv.symm i), this is eig₀ (equiv.symm i) ^ 2 = eig₀ (equiv.symm i) ^ 2
    simp only [eig, eig₀, IsHermitian.eigenvalues]

  rw [h_eigenvalues_eq, h_D_eigenvalues]

/-- For a positive semidefinite matrix, singular values equal eigenvalues. -/
theorem singularValues_posSemidef (A : Matrix n n ℂ) (hA : A.PosSemidef) (i : n) :
    singularValues A i = hA.isHermitian.eigenvalues i := by
  dsimp [singularValues]
  have h_sq : conjTranspose A * A = A^2 := by
    rw [hA.isHermitian.eq, pow_two]
  have h_charpoly : (conjTranspose A * A).charpoly = (A^2).charpoly := by
    rw [h_sq]
  have h_eq : (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i = (hA.isHermitian.pow 2).eigenvalues i := by
    apply congr_fun
    exact (IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr h_charpoly
  rw [h_eq]
  rw [eigenvalues_sq hA]
  rw [Real.sqrt_sq]
  exact PosSemidef.eigenvalues_nonneg hA i

/-- The eigenvalues of √(Aᴴ*A) are the singular values of A.
    This follows from the spectral theorem: if Aᴴ*A has eigenvalues λᵢ ≥ 0,
    then √(Aᴴ*A) has eigenvalues √λᵢ, which are exactly the singular values.

    **Proof strategy:**
    1. Let B = √(Aᴴ*A), which is PosSemidef
    2. B² = Aᴴ*A (by CFC.sq_sqrt)
    3. eigenvalues(B²) = eigenvalues(Aᴴ*A) (same matrix, same eigenvalues)
    4. For PSD B: eigenvalues(B²) i = (eigenvalues(B) i)² (by eigenvalues_sq)
    5. Therefore: (eigenvalues(B) i)² = eigenvalues(Aᴴ*A) i
    6. Taking sqrt: eigenvalues(B) i = √(eigenvalues(Aᴴ*A) i) = singularValues A i
       (using eigenvalues(B) i ≥ 0 for PSD B)
-/
theorem sqrtConjTransposeMulSelf_eigenvalues (A : Matrix n n ℂ) (i : n) :
    (sqrtConjTransposeMulSelf_isHermitian A).eigenvalues i = singularValues A i := by
  -- Let B = sqrt(Aᴴ*A) and let hB be the proof that B is PosSemidef
  let B := sqrtConjTransposeMulSelf A
  let hB := sqrtConjTransposeMulSelf_isPosSemidef A

  -- B² = Aᴴ*A
  have h_sq : B ^ 2 = Aᴴ * A := sqrtConjTransposeMulSelf_sq A

  -- eigenvalues(B²) = eigenvalues(Aᴴ*A) because they're the same matrix
  have h_eig_sq : (hB.isHermitian.pow 2).eigenvalues =
                  (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues := by
    rw [IsHermitian.eigenvalues_eq_eigenvalues_iff]
    rw [h_sq]

  -- For PSD B: eigenvalues(B²) i = (eigenvalues(B) i)²
  have h_sq_eig : (hB.isHermitian.pow 2).eigenvalues i = (hB.isHermitian.eigenvalues i) ^ 2 :=
    eigenvalues_sq hB i

  -- eigenvalues(Aᴴ*A) i = (eigenvalues(B) i)²
  have h_eq : (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i =
              (hB.isHermitian.eigenvalues i) ^ 2 := by
    rw [← h_eig_sq, h_sq_eig]

  -- singularValues A i = sqrt((eigenvalues(B) i)²) = eigenvalues(B) i
  -- (since B is PSD, eigenvalues are non-negative)
  unfold singularValues
  rw [h_eq]
  rw [Real.sqrt_sq]
  exact PosSemidef.eigenvalues_nonneg hB i

/-! ### Product and Sum Properties -/

/-- Product of square roots equals square root of product for nonnegative functions. -/
private lemma prod_sqrt_eq_sqrt_prod {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∏ i, Real.sqrt (f i) = Real.sqrt (∏ i, f i) := by
  have h_prod_nonneg : 0 ≤ ∏ i, f i := Finset.prod_nonneg fun i _ => hf i
  have h_prod_sqrt_nonneg : 0 ≤ ∏ i, Real.sqrt (f i) :=
    Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  symm
  rw [Real.sqrt_eq_iff_eq_sq h_prod_nonneg h_prod_sqrt_nonneg]
  rw [← Finset.prod_pow]
  congr 1
  ext i
  rw [Real.sq_sqrt (hf i)]

/-- The determinant of Aᴴ * A equals the squared norm of det A. -/
private lemma det_conjTranspose_mul_self (A : Matrix n n ℂ) :
    (Aᴴ * A).det = Complex.normSq A.det := by
  rw [det_mul, det_conjTranspose]
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- The product of singular values equals the absolute value of the determinant. -/
theorem prod_singularValues_eq_abs_det (A : Matrix n n ℂ) :
    ∏ i, singularValues A i = Real.sqrt (Complex.normSq (A.det)) := by
  unfold singularValues
  rw [prod_sqrt_eq_sqrt_prod _ (fun i =>
    PosSemidef.eigenvalues_nonneg (posSemidef_conjTranspose_mul_self A) i)]
  congr 1
  -- Goal: ∏ eigenvalues (Aᴴ*A) = Complex.normSq (det A) at ℝ level
  have h1 := (posSemidef_conjTranspose_mul_self A).isHermitian.det_eq_prod_eigenvalues
  have h2 : (Aᴴ * A).det = Complex.normSq A.det := det_conjTranspose_mul_self A
  -- h1 : det(Aᴴ*A) = ∏ i, ↑(eigenvalues i) as complex numbers
  -- h2 : det(Aᴴ*A) = normSq(det A) as complex numbers
  have h3 : ∏ i, ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i : ℂ) =
            (Complex.normSq A.det : ℂ) := by
    calc ∏ i, ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i : ℂ)
        = (Aᴴ * A).det := h1.symm
      _ = Complex.normSq A.det := h2
  -- Convert from complex product to real product using Complex.ofReal_prod
  have h4 : (↑(∏ i, (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) : ℂ) =
            ∏ i, ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i : ℂ) :=
    Complex.ofReal_prod _ _
  have h5 : (↑(∏ i, (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i) : ℂ) =
            (Complex.normSq A.det : ℂ) := h4.trans h3
  exact Complex.ofReal_injective h5

/-- The sum of squared singular values equals the squared Frobenius norm.
    (i.e., trace(Aᴴ * A)) -/
theorem sum_sq_singularValues_eq_trace (A : Matrix n n ℂ) :
    ∑ i, (singularValues A i) ^ 2 = Complex.re (Matrix.trace (conjTranspose A * A)) := by
  -- Singular values squared = eigenvalues of Aᴴ * A
  simp_rw [singularValues_sq]
  -- trace(Aᴴ * A) = sum of eigenvalues (spectral theorem)
  have h := (posSemidef_conjTranspose_mul_self A).isHermitian.trace_eq_sum_eigenvalues
  -- The RHS simplifies to Re(∑ (λᵢ : ℂ)) = ∑ Re(λᵢ) = ∑ λᵢ (since λᵢ are real)
  rw [h, Complex.re_sum]
  rfl


end Matrix.SVD
end Hagi.External.Flywheel
