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
import Hagi.External.Flywheel.SVDRectangularOrdering

/-!
# SVDRectangularNorms

Frobenius and spectral norm sections for rectangular matrices: `‖A‖ ² = ∑ σᵢ²` and `‖A‖ = sup σᵢ`.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

/-! ## Frobenius Norm - Singular Values Connection for Rectangular Matrices -/

section FrobeniusNormRectangular

open Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

/-- **Frobenius norm squared equals sum of squared singular values** for rectangular matrices.
    This connects to the trace identity via trace(Aᴴ*A) = ‖A‖_F². -/
theorem Matrix.SVD.Rectangular.frobeniusNorm_sq_eq_sum_singularValues_sq_rect (A : Matrix m n ℂ) :
    ‖A‖ ^ 2 = ∑ k, (singularValues A k) ^ 2 := by
  rw [sum_sq_singularValues_rect_eq_trace]
  -- ‖A‖_F² = trace(Aᴴ*A).re
  rw [frobenius_norm_def]
  have h_nonneg : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _))
  -- (x^(1/2))^2 = x for x ≥ 0
  have h_sq_sqrt : ((∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1/2 : ℝ)) ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
    norm_num
  rw [h_sq_sqrt]
  -- Goal: ∑ i, ∑ j, ‖A i j‖ ^ 2 = trace(Aᴴ*A).re
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  -- RHS is (∑ x, ∑ x_1, star (A x_1 x) * A x_1 x).re
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- Goal: ‖A i j‖ ^ 2 = (star (A i j) * A i j).re
  rw [Complex.star_def]
  -- Goal: ‖A i j‖ ^ 2 = (conj (A i j) * A i j).re
  rw [Complex.conj_mul']
  -- Goal: ‖A i j‖ ^ 2 = (↑‖A i j‖ ^ 2).re
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  -- Need to convert ℝ power to ℕ power: x ^ (2:ℝ) = x ^ (2:ℕ)
  norm_cast

/-- **Frobenius norm equals square root of sum of squared singular values** for rectangular matrices. -/
theorem Matrix.SVD.Rectangular.frobeniusNorm_eq_sqrt_sum_singularValues_sq_rect (A : Matrix m n ℂ) :
    ‖A‖ = Real.sqrt (∑ k, (singularValues A k) ^ 2) := by
  have h_sq := frobeniusNorm_sq_eq_sum_singularValues_sq_rect A
  have h_nonneg : 0 ≤ ‖A‖ := norm_nonneg _
  rw [← h_sq, Real.sqrt_sq h_nonneg]

end FrobeniusNormRectangular

/-! ## Spectral Norm for Rectangular Matrices

This section establishes that for rectangular matrices `A : Matrix m n ℂ`:
- `‖A‖² = ‖Aᴴ*A‖ = λ_max(Aᴴ*A)` (spectral norm squared equals max eigenvalue of Gram matrix)
- `‖A‖ = max{σₖ}` where σₖ are the singular values

These connect the L2 operator norm to singular values, generalizing the square case
in `MatrixNormRelations.lean` to rectangular matrices.

**Key insight:** The fundamental identity `‖A‖² = ‖Aᴴ*A‖` holds for all rectangular A
(from `Matrix.l2_opNorm_conjTranspose_mul_self` in Mathlib). Since Aᴴ*A is a square
Hermitian positive semidefinite n×n matrix, its spectral norm equals its max eigenvalue,
which equals the max squared singular value of A.
-/

section SpectralNormRectangular

open Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

-- Enable L2 operator norm instances locally for this section (needed for CStarAlgebra)
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace
attribute [local instance] Matrix.instCStarRing

/-- The CStarAlgebra instance for complex matrices with L2 operator norm. -/
private noncomputable def instCStarAlgebraMatrixLocal : CStarAlgebra (Matrix n n ℂ) :=
  CStarAlgebra.mk

/-- Notation for L2 operator norm of rectangular matrices. -/
local notation "‖" A "‖₂" => @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A

/-! ### Helper Lemmas for Spectral Norm -/

/-- For a Hermitian matrix H, the L2 operator norm equals the spectral radius. -/
private theorem l2_opNorm_hermitian_eq_spectralRadius
    (H : Matrix n n ℂ) (hH : Matrix.IsHermitian H) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm H = (spectralRadius ℝ H).toReal := by
  -- Use the CStarAlgebra instance for matrices with L2 norm
  have h_sa : IsSelfAdjoint H := hH.isSelfAdjoint
  -- The L2 norm of matrices forms a C*-algebra, so we can use the spectral radius formula
  have := @IsSelfAdjoint.toReal_spectralRadius_eq_norm (Matrix n n ℂ)
    instCStarAlgebraMatrixLocal H h_sa
  exact this.symm

/-- The spectral radius of a Hermitian matrix equals the supremum of absolute eigenvalues. -/
private theorem hermitian_spectralRadius_eq_sup_abs_eigenvalues [Nonempty n]
    (H : Matrix n n ℂ) (hH : Matrix.IsHermitian H) :
    (spectralRadius ℝ H).toReal = Finset.sup' Finset.univ Finset.univ_nonempty (|hH.eigenvalues ·|) := by
  have h_spec : quasispectrum ℝ H = Set.range hH.eigenvalues ∪ {0} := by
    rw [quasispectrum_eq_spectrum_union_zero, hH.spectrum_real_eq_range_eigenvalues]
  simp only [spectralRadius, h_spec]
  rw [iSup_union, iSup_range, iSup_singleton]
  simp only [nnnorm_zero, ENNReal.coe_zero, max_zero]
  have h_ne_top : ∀ i, ((‖hH.eigenvalues i‖₊ : NNReal) : ENNReal) ≠ ⊤ := fun i => ENNReal.coe_ne_top
  rw [ENNReal.toReal_iSup h_ne_top]
  have h_eq : ∀ i, (↑(‖hH.eigenvalues i‖₊) : ENNReal).toReal = |hH.eigenvalues i| := fun i => by
    simp only [ENNReal.toReal, ENNReal.toNNReal_coe]
    simp only [nnnorm, Real.norm_eq_abs]
    rfl
  simp_rw [h_eq]
  symm
  rw [Finset.sup'_eq_csSup_image]
  simp only [Finset.coe_univ, Set.image_univ, sSup_range]

/-- For a Hermitian matrix, ‖H‖ = max |λᵢ| where λᵢ are eigenvalues. -/
private theorem l2_opNorm_hermitian_eq_sup_abs_eigenvalues [Nonempty n]
    (H : Matrix n n ℂ) (hH : Matrix.IsHermitian H) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm H =
      Finset.sup' Finset.univ Finset.univ_nonempty (|hH.eigenvalues ·|) := by
  rw [l2_opNorm_hermitian_eq_spectralRadius H hH]
  exact hermitian_spectralRadius_eq_sup_abs_eigenvalues H hH

/-- For nonneg values, sup(f²) = (sup f)². Helper lemma for spectral norm theorem. -/
private lemma sup'_sq_eq_sq_sup' {α : Type*} {s : Finset α} (hs : s.Nonempty) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    s.sup' hs (fun i => (f i) ^ 2) = (s.sup' hs f) ^ 2 := by
  obtain ⟨j, hjs, hj⟩ := s.exists_mem_eq_sup' hs f
  rw [hj]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    have : f i ≤ f j := by
      calc f i ≤ s.sup' hs f := Finset.le_sup' f hi
        _ = f j := hj
    exact sq_le_sq' (by linarith [hf i hi]) this
  · exact Finset.le_sup' (fun i => (f i) ^ 2) hjs

/-! ### Main Theorems -/

/-- The largest singular value of a rectangular matrix. -/
noncomputable def Matrix.SVD.Rectangular.maxSingularValue
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩) (singularValues A)

/-- **Spectral norm squared equals max eigenvalue of Aᴴ*A** for rectangular matrices.

This is the key intermediate result connecting operator norm to eigenvalues. -/
theorem Matrix.SVD.Rectangular.spectral_norm_sq_eq_max_eigenvalue_rect
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ^ 2 = Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr (⟨⟨0, Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)⟩⟩ : Nonempty (Fin (Fintype.card n))))
      (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ := by
  -- Step 1: ‖A‖² = ‖Aᴴ*A‖ (fundamental C*-algebra identity)
  have h1 : @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A ^ 2 =
      @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (Aᴴ * A) := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self A
    linarith [sq_nonneg ‖A‖₂]
  rw [h1]
  -- Step 2: Aᴴ*A is Hermitian positive semidefinite
  let h_psd := posSemidef_conjTranspose_mul_self A
  let h_herm := h_psd.isHermitian
  -- Step 3: For Hermitian PSD matrices, ‖H‖ = max eigenvalue = max |eigenvalue| = max eigenvalue (since ≥ 0)
  have h_nonempty_n : Nonempty n := by
    have : 0 < Fintype.card n := Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)
    exact Fintype.card_pos_iff.mp this
  -- ‖Aᴴ*A‖ = sup |eigenvalues|
  have h2 : @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm (Aᴴ * A) =
      Finset.sup' Finset.univ Finset.univ_nonempty (|h_herm.eigenvalues ·|) :=
    l2_opNorm_hermitian_eq_sup_abs_eigenvalues (Aᴴ * A) h_herm
  -- For PSD, eigenvalues ≥ 0 so |λ| = λ
  have h3 : ∀ i, |h_herm.eigenvalues i| = h_herm.eigenvalues i := fun i =>
    abs_of_nonneg (h_psd.eigenvalues_nonneg i)
  rw [h2]
  -- Convert: sup over unsorted eigenvalues = sup over sorted eigenvalues₀
  -- For PSD, |λ| = λ
  conv_lhs => rw [show (fun x => |h_herm.eigenvalues x|) = (fun x => h_herm.eigenvalues x) from
    funext h3]
  -- eigenvalues and eigenvalues₀ have the same image (one is a sorted reindexing of the other)
  -- eigenvalues₀ k = eigenvalues ((Fintype.equivOfCardEq _) k) by Mathlib's definition
  -- So their sups are equal. We prove this by showing each is ≤ the other.
  let equiv := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n)
  apply le_antisymm
  · -- sup eigenvalues ≤ sup eigenvalues₀
    apply Finset.sup'_le
    intro i _
    -- eigenvalues i = eigenvalues₀ (equiv.symm i)
    have h_eq : h_herm.eigenvalues i = h_herm.eigenvalues₀ (equiv.symm i) := by
      simp only [Matrix.IsHermitian.eigenvalues, equiv]
    rw [h_eq]
    exact Finset.le_sup' h_herm.eigenvalues₀ (Finset.mem_univ _)
  · -- sup eigenvalues₀ ≤ sup eigenvalues
    apply Finset.sup'_le
    intro j _
    -- eigenvalues₀ j = eigenvalues (equiv j)
    have h_eq : h_herm.eigenvalues₀ j = h_herm.eigenvalues (equiv j) := by
      simp only [Matrix.IsHermitian.eigenvalues, equiv, Equiv.symm_apply_apply]
    rw [h_eq]
    exact Finset.le_sup' h_herm.eigenvalues (Finset.mem_univ _)

/-- **Spectral norm squared equals max squared singular value** for rectangular matrices.

This converts from eigenvalues to singular values using σₖ² = λₖ. -/
theorem Matrix.SVD.Rectangular.spectral_norm_sq_eq_max_singularValue_sq_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ‖A‖₂ ^ 2 = Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
      (fun k => (singularValues A k) ^ 2) := by
  -- First establish the eigenvalue version
  have h_eig := spectral_norm_sq_eq_max_eigenvalue_rect h A
  rw [h_eig]
  -- Now we need: sup_{j : Fin #n} eigenvalues₀ j = sup_{k : Fin min} (singularValues A k)²
  let h_psd := posSemidef_conjTranspose_mul_self A
  let h_herm := h_psd.isHermitian
  -- Key: eigenvalues beyond min are 0, and singularValues k² = eigenvalues₀ (castLE k)
  -- So the sup over all eigenvalues₀ equals the sup over singular values²
  apply le_antisymm
  · -- sup eigenvalues₀ ≤ sup singularValues²
    apply Finset.sup'_le
    intro j _
    by_cases hj : j.val < min (Fintype.card m) (Fintype.card n)
    · -- j < min: eigenvalues₀ j = singularValues ⟨j.val, hj⟩²
      have h_eq : h_herm.eigenvalues₀ j = (singularValues A ⟨j.val, hj⟩) ^ 2 := by
        rw [singularValues_sq_rect]
        congr 1
      rw [h_eq]
      exact Finset.le_sup' (fun k => (singularValues A k) ^ 2) (Finset.mem_univ _)
    · -- j ≥ min: eigenvalues₀ j = 0
      have hj' : j.val ≥ min (Fintype.card m) (Fintype.card n) := Nat.not_lt.mp hj
      have h_zero := eigenvalues₀_zero_beyond_min A j hj'
      rw [h_zero]
      apply Finset.le_sup'_of_le (fun k => (singularValues A k) ^ 2) (Finset.mem_univ ⟨0, h⟩)
      exact sq_nonneg _
  · -- sup singularValues² ≤ sup eigenvalues₀
    apply Finset.sup'_le
    intro k _
    have h_eq : (singularValues A k) ^ 2 = h_herm.eigenvalues₀ (Fin.castLE (Nat.min_le_right _ _) k) := by
      rw [singularValues_sq_rect]
    rw [h_eq]
    apply Finset.le_sup'
    exact Finset.mem_univ _

/-- **The spectral norm of a rectangular matrix equals its largest singular value.**

For any matrix A, ‖A‖₂ = σ₁(A) = √(λ_max(Aᴴ A)).

This is the main result of this section, generalizing the square-matrix
spectral_norm_eq_max_singularValue
from square matrices to rectangular matrices. -/
theorem Matrix.SVD.Rectangular.spectral_norm_eq_max_singularValue_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ‖A‖₂ = maxSingularValue h A := by
  unfold maxSingularValue
  -- Nonemptiness proof for Finset.sup'
  have h_ne : (Finset.univ : Finset (Fin (min (Fintype.card m) (Fintype.card n)))).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩
  have h_norm_nonneg : 0 ≤ ‖A‖₂ := @norm_nonneg (Matrix m n ℂ) _ A
  have h_maxSV_nonneg : 0 ≤ Finset.sup' Finset.univ h_ne (singularValues A) := by
    apply Finset.le_sup'_of_le (singularValues A) (Finset.mem_univ ⟨0, h⟩)
    exact singularValues_nonneg A ⟨0, h⟩
  -- We have ‖A‖² = (max σₖ)² from spectral_norm_sq_eq_max_singularValue_sq_rect
  have h_sq_eq : ‖A‖₂ ^ 2 = (Finset.sup' Finset.univ h_ne (singularValues A)) ^ 2 := by
    rw [spectral_norm_sq_eq_max_singularValue_sq_rect h A]
    -- Goal: sup' (fun k => (σₖ)²) = (sup' σₖ)²
    -- Apply sup'_sq_eq_sq_sup' which gives: sup' (fun i => (f i)²) = (sup' f)²
    rw [sup'_sq_eq_sq_sup' h_ne (singularValues A) (fun i _ => singularValues_nonneg A i)]
  -- From x² = y² and x,y ≥ 0, conclude x = y
  have h_abs_eq : |‖A‖₂| = |Finset.sup' Finset.univ h_ne (singularValues A)| :=
    (sq_eq_sq_iff_abs_eq_abs ‖A‖₂ _).mp h_sq_eq
  rwa [abs_of_nonneg h_norm_nonneg, abs_of_nonneg h_maxSV_nonneg] at h_abs_eq

/-- Spectral norm squared is bounded by sum of squared singular values (rectangular). -/
theorem Matrix.SVD.Rectangular.spectral_norm_sq_le_sum_singularValues_sq_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ‖A‖₂ ^ 2 ≤ ∑ k, (singularValues A k) ^ 2 := by
  rw [spectral_norm_sq_eq_max_singularValue_sq_rect h A]
  apply Finset.sup'_le
  intro k _
  exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)

/-- **Spectral norm is bounded by Frobenius norm** for rectangular matrices: ‖A‖₂ ≤ ‖A‖_F.

This generalizes the square-matrix spectral_norm_le_frobenius_norm
to rectangular matrices. -/
theorem Matrix.SVD.Rectangular.spectral_norm_le_frobenius_norm_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ‖A‖₂ ≤ Real.sqrt (∑ k, (singularValues A k) ^ 2) := by
  have h_sq : ‖A‖₂ ^ 2 ≤ ∑ k, (singularValues A k) ^ 2 :=
    spectral_norm_sq_le_sum_singularValues_sq_rect h A
  have h_sum_nonneg : 0 ≤ ∑ k, (singularValues A k) ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h_norm_nonneg : 0 ≤ ‖A‖₂ := @norm_nonneg (Matrix m n ℂ) _ A
  calc ‖A‖₂ = Real.sqrt (‖A‖₂ ^ 2) := (Real.sqrt_sq h_norm_nonneg).symm
    _ ≤ Real.sqrt (∑ k, (singularValues A k) ^ 2) := Real.sqrt_le_sqrt h_sq

end SpectralNormRectangular
end Hagi.External.Flywheel
