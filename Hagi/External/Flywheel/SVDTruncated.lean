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
import Hagi.External.Flywheel.SVDDiagonal

/-!
# SVDTruncated

Truncated SVD section: rank-`k` truncation of the decomposition. Split from `SVD` (C258).
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

namespace Matrix.SVD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Truncated SVD

For Eckart-Young theorem and low-rank approximation, we define the rank-k truncated SVD
which keeps only the k largest singular values. -/

section TruncatedSVD

/-- Truncated singular values: keep first k (largest) singular values, zero the rest.
    Uses the sorted `singularValues₀` indexing. -/
noncomputable def truncatedSingularValues (A : Matrix n n ℂ) (k : ℕ) : n → ℝ :=
  fun i =>
    let idx := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
    if idx.val < k then singularValues₀ A idx else 0

/-- Truncated singular values are non-negative. -/
theorem truncatedSingularValues_nonneg (A : Matrix n n ℂ) (k : ℕ) (i : n) :
    0 ≤ truncatedSingularValues A k i := by
  unfold truncatedSingularValues
  simp only
  split_ifs with h
  · exact singularValues₀_nonneg A _
  · rfl

/-- Truncated singular values equal regular singular values for indices < k. -/
theorem truncatedSingularValues_eq_of_lt (A : Matrix n n ℂ) (k : ℕ) (i : n)
    (h : ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val < k) :
    truncatedSingularValues A k i = singularValues₀ A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := by
  unfold truncatedSingularValues
  simp only [h, ↓reduceIte]

/-- Truncated singular values are zero for indices ≥ k. -/
theorem truncatedSingularValues_eq_zero_of_ge (A : Matrix n n ℂ) (k : ℕ) (i : n)
    (h : k ≤ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val) :
    truncatedSingularValues A k i = 0 := by
  unfold truncatedSingularValues
  simp only [not_lt.mpr h, ↓reduceIte]

/-- The number of nonzero truncated singular values is at most k.
    This uses that truncated values are nonzero only for indices < k,
    and there are at most k such indices. -/
theorem card_truncatedSingularValues_nonzero_le (A : Matrix n n ℂ) (k : ℕ) :
    Fintype.card { i : n // truncatedSingularValues A k i ≠ 0 } ≤ k := by
  -- Nonzero entries can only occur when idx.val < k
  have h_subset : ∀ i : n, truncatedSingularValues A k i ≠ 0 →
      ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val < k := by
    intro i hi
    by_contra h_not_lt
    push_neg at h_not_lt
    have := truncatedSingularValues_eq_zero_of_ge A k i h_not_lt
    exact hi this
  -- The set { i : n | truncated ≠ 0 } maps injectively into Fin k
  -- via i ↦ (equiv.symm i).val when that value < k
  let e := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n).symm
  have h_inj : Function.Injective (fun (x : { i : n // truncatedSingularValues A k i ≠ 0 }) =>
      (⟨(e x.val).val, h_subset x.val x.prop⟩ : Fin k)) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h_eq
    simp only [Fin.mk.injEq] at h_eq
    have h_fin_eq : e x = e y := Fin.ext h_eq
    exact Subtype.ext (e.injective h_fin_eq)
  calc Fintype.card { i : n // truncatedSingularValues A k i ≠ 0 }
      ≤ Fintype.card (Fin k) := Fintype.card_le_of_injective _ h_inj
    _ = k := Fintype.card_fin k

/-- The truncated SVD of rank k: Aₖ = U * Σₖ * Vᴴ where Σₖ keeps only the k largest singular values.
    This is the best rank-k approximation in both Frobenius and spectral norms (Eckart-Young). -/
noncomputable def truncatedSVD (A : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  (constructedU A : Matrix n n ℂ) *
    diagonal (Complex.ofReal ∘ truncatedSingularValues A k) *
    star (rightUnitary A : Matrix n n ℂ)

/-- The truncated SVD with k = 0 is the zero matrix. -/
theorem truncatedSVD_zero (A : Matrix n n ℂ) : truncatedSVD A 0 = 0 := by
  unfold truncatedSVD truncatedSingularValues
  simp only [Nat.not_lt_zero, ↓reduceIte]
  have h_diag : diagonal (Complex.ofReal ∘ fun _ : n => (0 : ℝ)) = (0 : Matrix n n ℂ) := by
    ext i j
    simp only [diagonal_apply, Function.comp_apply, Complex.ofReal_zero]
    split_ifs <;> rfl
  rw [h_diag, mul_zero, zero_mul]

/-- The truncated SVD with k ≥ card n equals the original SVD (hence equals A). -/
theorem truncatedSVD_full (A : Matrix n n ℂ) (k : ℕ) (hk : Fintype.card n ≤ k) :
    truncatedSVD A k = A := by
  unfold truncatedSVD truncatedSingularValues
  -- All indices satisfy idx.val < k since idx.val < card n ≤ k
  have h_all : ∀ i : n, ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val < k := by
    intro i
    calc ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i).val
        < Fintype.card n := Fin.isLt _
      _ ≤ k := hk
  -- Simplify the diagonal to use singularValues
  have h_diag_eq : diagonal (Complex.ofReal ∘ fun i =>
      if ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i : Fin (Fintype.card n)).val < k
      then singularValues₀ A ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
      else 0) =
      diagonal (Complex.ofReal ∘ singularValues A) := by
    ext i j
    simp only [diagonal_apply, Function.comp_apply]
    split_ifs with h_eq h_lt
    · -- case h_eq : i = j, h_lt : idx < k
      subst h_eq
      rw [singularValues_eq_singularValues₀]
    · -- case h_eq : i = j, h_lt : ¬(idx < k) - impossible
      subst h_eq
      exact absurd (h_all i) h_lt
    · rfl  -- case ¬(i = j) - both sides are 0
  rw [h_diag_eq]
  -- This is exactly the SVD decomposition
  have h_svd := AV_eq_constructedU_mul_sigma A
  have h_V_unitary : (rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff.mp (rightUnitary A).2
  calc (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) * star (rightUnitary A : Matrix n n ℂ)
      = ((constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A)) * star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]
    _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [← h_svd]
    _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [mul_assoc]
    _ = A * 1 := by rw [h_V_unitary]
    _ = A := by rw [mul_one]

/-- The rank of the truncated SVD is at most k.
    This uses that rank(diagonal w) = #{i | w i ≠ 0} and unitary transformations preserve rank. -/
theorem truncatedSVD_rank_le (A : Matrix n n ℂ) (k : ℕ) :
    (truncatedSVD A k).rank ≤ k := by
  unfold truncatedSVD
  -- Let D = diagonal(truncatedSingularValues)
  let D := diagonal (Complex.ofReal ∘ truncatedSingularValues A k)
  let U := (constructedU A : Matrix n n ℂ)
  let V := (rightUnitary A : Matrix n n ℂ)
  -- truncatedSVD A k = U * D * Vᴴ
  -- rank(U * D * Vᴴ) = rank(D) since U, Vᴴ are unitary (invertible)
  have hU_isUnit : IsUnit U.det := UnitaryGroup.det_isUnit (constructedU A)
  have hVstar_isUnit : IsUnit (star V).det := by
    have hV_isUnit : IsUnit V.det := UnitaryGroup.det_isUnit (rightUnitary A)
    rw [star_eq_conjTranspose, det_conjTranspose]
    exact hV_isUnit.star
  -- rank(U * D * Vᴴ) = rank(D * Vᴴ) = rank(D)
  have h1 : (U * D * star V).rank = (D * star V).rank := by
    rw [mul_assoc]
    exact rank_mul_eq_right_of_isUnit_det U (D * star V) hU_isUnit
  have h2 : (D * star V).rank = D.rank := rank_mul_eq_left_of_isUnit_det (star V) D hVstar_isUnit
  -- rank(D) = #{i | D i i ≠ 0} = #{i | truncatedSingularValues A k i ≠ 0} ≤ k
  have h3 : D.rank = Fintype.card { i : n // (Complex.ofReal ∘ truncatedSingularValues A k) i ≠ 0 } := by
    exact rank_diagonal _
  have h4 : Fintype.card { i : n // (Complex.ofReal ∘ truncatedSingularValues A k) i ≠ 0 } =
            Fintype.card { i : n // truncatedSingularValues A k i ≠ 0 } := by
    have h_equiv : { i : n // (Complex.ofReal ∘ truncatedSingularValues A k) i ≠ 0 } ≃
                   { i : n // truncatedSingularValues A k i ≠ 0 } := by
      apply Equiv.subtypeEquivProp
      ext i
      simp only [Function.comp_apply, ne_eq, Complex.ofReal_eq_zero]
    exact Fintype.card_eq.mpr ⟨h_equiv⟩
  rw [h1, h2, h3, h4]
  exact card_truncatedSingularValues_nonzero_le A k

/-- The tail of the SVD: singular values beyond the k-th. -/
noncomputable def truncatedSingularValues_tail (A : Matrix n n ℂ) (k : ℕ) : n → ℝ :=
  fun i =>
    let idx := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
    if k ≤ idx.val then singularValues₀ A idx else 0

/-- The truncated and tail singular values sum to the original. -/
theorem truncatedSingularValues_add_tail (A : Matrix n n ℂ) (k : ℕ) (i : n) :
    truncatedSingularValues A k i + truncatedSingularValues_tail A k i = singularValues A i := by
  unfold truncatedSingularValues truncatedSingularValues_tail
  simp only [singularValues_eq_singularValues₀]
  split_ifs with h1 h2
  · -- h1 : idx < k, h2 : k ≤ idx - impossible
    omega
  · -- h1 : idx < k, h2 : ¬(k ≤ idx)
    ring
  · -- h1 : ¬(idx < k), h2 : k ≤ idx
    ring
  · -- h1 : ¬(idx < k), h2 : ¬(k ≤ idx) - impossible
    omega

/-- The tail of the truncated SVD. -/
noncomputable def truncatedSVD_tail (A : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  (constructedU A : Matrix n n ℂ) *
    diagonal (Complex.ofReal ∘ truncatedSingularValues_tail A k) *
    star (rightUnitary A : Matrix n n ℂ)

/-- The original matrix equals the truncated SVD plus its tail: A = Aₖ + A_tail. -/
theorem truncatedSVD_add_tail (A : Matrix n n ℂ) (k : ℕ) :
    A = truncatedSVD A k + truncatedSVD_tail A k := by
  unfold truncatedSVD truncatedSVD_tail
  -- diag(trunc) + diag(tail) = diag(trunc + tail) = diag(singularValues)
  have h_diag : diagonal (Complex.ofReal ∘ truncatedSingularValues A k) +
                diagonal (Complex.ofReal ∘ truncatedSingularValues_tail A k) =
                diagonal (Complex.ofReal ∘ singularValues A) := by
    ext i j
    simp only [Matrix.add_apply, diagonal_apply, Function.comp_apply]
    split_ifs with h
    · subst h
      rw [← Complex.ofReal_add, truncatedSingularValues_add_tail]
    · ring
  -- U * D₁ * Vᴴ + U * D₂ * Vᴴ = U * (D₁ + D₂) * Vᴴ
  have h_factor : (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ truncatedSingularValues A k) *
                  star (rightUnitary A : Matrix n n ℂ) +
                  (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ truncatedSingularValues_tail A k) *
                  star (rightUnitary A : Matrix n n ℂ) =
                  (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) *
                  star (rightUnitary A : Matrix n n ℂ) := by
    -- Use (A * B) * C + (A * D) * C = (A * (B + D)) * C
    rw [← add_mul, ← mul_add, h_diag]
  rw [h_factor]
  -- Now we have A = U * diag(singularValues) * Vᴴ by SVD
  have h_svd := AV_eq_constructedU_mul_sigma A
  have h_V_unitary : (rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ) = 1 :=
    mem_unitaryGroup_iff.mp (rightUnitary A).2
  symm
  calc (constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A) * star (rightUnitary A : Matrix n n ℂ)
      = ((constructedU A : Matrix n n ℂ) * diagonal (Complex.ofReal ∘ singularValues A)) * star (rightUnitary A : Matrix n n ℂ) := by rw [mul_assoc]
    _ = (A * (rightUnitary A : Matrix n n ℂ)) * star (rightUnitary A : Matrix n n ℂ) := by rw [← h_svd]
    _ = A * ((rightUnitary A : Matrix n n ℂ) * star (rightUnitary A : Matrix n n ℂ)) := by rw [mul_assoc]
    _ = A * 1 := by rw [h_V_unitary]
    _ = A := by rw [mul_one]

end TruncatedSVD

end Matrix.SVD
end Hagi.External.Flywheel
