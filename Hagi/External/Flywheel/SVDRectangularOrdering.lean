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
import Hagi.External.Flywheel.SVDRectangular

/-!
# SVDRectangularOrdering

Singular-value ordering for rectangular matrices, rectangular coherence infrastructure, and the Frobenius-singular-value connection.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

namespace Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! #### Singular Values Ordering

The singular values inherit the decreasing order from `IsHermitian.eigenvalues`.
This is important for truncated SVD and Eckart-Young theorem.

Note: `Matrix.IsHermitian.eigenvalues` are sorted in decreasing order by construction
(via `LinearMap.IsSymmetric.eigenvalues` which uses a sorted list).
The antitone property follows from this ordering.
-/

set_option linter.unusedSectionVars false in
/-- Singular values are non-increasing (antitone).
    This follows from the eigenvalue ordering of Hermitian matrices.

    The eigenvalues of a Hermitian matrix are sorted in decreasing order by construction
    (via `eigenvalues₀_antitone`), so larger indices give smaller eigenvalues.
    Since singular values are square roots of eigenvalues (which are nonneg), the ordering
    is preserved by `Real.sqrt_le_sqrt`. -/
theorem singularValues_antitone (A : Matrix m n ℂ) :
    Antitone (singularValues A) := by
  intro k₁ k₂ hk
  unfold singularValues
  -- Always use AᴴA eigenvalues₀ (after architectural change)
  apply Real.sqrt_le_sqrt
  -- eigenvalues₀_antitone: k₁ ≤ k₂ → eigenvalues₀ k₂ ≤ eigenvalues₀ k₁
  -- castLE preserves ≤: k₁ ≤ k₂ → castLE k₁ ≤ castLE k₂
  have h_cast : Fin.castLE (Nat.min_le_right (Fintype.card m) (Fintype.card n)) k₁ ≤
                Fin.castLE (Nat.min_le_right (Fintype.card m) (Fintype.card n)) k₂ := by
    simp only [Fin.le_def, Fin.coe_castLE]
    exact hk
  exact (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀_antitone h_cast

/-! ### Rectangular Coherence Infrastructure

These lemmas connect rank to singular values for rectangular matrices,
enabling the coherence factor extension in CoherenceCharacterization.lean.

For A : Matrix m n ℂ:
- rank(A) ≤ min(#m, #n)
- rank(A) = |{k : σₖ ≠ 0}| where σₖ are singular values
-/

set_option linter.unusedSectionVars false in
/-- The rank of a rectangular matrix is at most the minimum of its dimensions.
    This follows from Mathlib's `rank_le_card_height` and `rank_le_card_width`. -/
theorem rank_le_min_card (A : Matrix m n ℂ) :
    A.rank ≤ min (Fintype.card m) (Fintype.card n) := by
  apply Nat.le_min.mpr
  constructor
  · exact rank_le_card_height A
  · exact rank_le_card_width A

set_option linter.unusedSectionVars false in
/-- Nonzero singular values (for rectangular matrices) correspond to nonzero eigenvalues of Aᴴ*A.
    Since σₖ = √(λₖ) where λₖ ≥ 0, we have σₖ ≠ 0 ↔ λₖ ≠ 0.

    This is the rectangular analogue of the square-matrix
    singularValues_ne_zero_iff_eigenvalues_ne_zero
    from the square case in CoherenceCharacterization.lean. -/
theorem singularValues_ne_zero_iff_eigenvalues₀_ne_zero (A : Matrix m n ℂ)
    (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    singularValues A k ≠ 0 ↔
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀
      (Fin.castLE (Nat.min_le_right _ _) k) ≠ 0 := by
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let j := Fin.castLE (Nat.min_le_right (Fintype.card m) (Fintype.card n)) k
  have h_eig_nonneg : 0 ≤ hermAHA.eigenvalues₀ j := by
    have h_psd := posSemidef_conjTranspose_mul_self A
    exact PosSemidef_eigenvalues₀_nonneg h_psd j
  constructor
  · intro h_sv_ne h_eig_eq
    -- If σₖ ≠ 0, then √(λₖ) ≠ 0, so λₖ ≠ 0
    unfold singularValues at h_sv_ne
    simp only [h_eig_eq, Real.sqrt_zero, ne_eq, not_true] at h_sv_ne
  · intro h_eig_ne
    -- If λₖ ≠ 0 and λₖ ≥ 0, then λₖ > 0, so √λₖ > 0 ≠ 0
    unfold singularValues
    have h_pos : 0 < hermAHA.eigenvalues₀ j := lt_of_le_of_ne h_eig_nonneg (ne_comm.mpr h_eig_ne)
    exact ne_of_gt (Real.sqrt_pos.mpr h_pos)

/-- The rank of a rectangular matrix equals the number of nonzero singular values.

    For A : Matrix m n ℂ, we have:
      rank(A) = rank(Aᴴ*A) = |{k : eigenvalues₀ k ≠ 0}| = |{k : singularValues A k ≠ 0}|

    Key insight: The singular values are indexed by Fin (min #m #n), and
    rank(A) ≤ min(#m, #n), so all nonzero singular values fit within this index range. -/
theorem rank_eq_card_nonzero_singularValues_rect (A : Matrix m n ℂ) :
    A.rank = Fintype.card {k : Fin (min (Fintype.card m) (Fintype.card n)) // singularValues A k ≠ 0} := by
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let h_psd := posSemidef_conjTranspose_mul_self A

  -- Step 1: rank(A) = rank(Aᴴ*A)
  have h_rank_eq : A.rank = (Aᴴ * A).rank := (rank_conjTranspose_mul_self A).symm

  -- Step 2: rank(Aᴴ*A) = |{j : n // eigenvalues j ≠ 0}| by Hermitian characterization
  have h_herm_rank : (Aᴴ * A).rank = Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} :=
    hermAHA.rank_eq_card_non_zero_eigs

  -- Step 3: Convert to eigenvalues₀ (indexed by Fin (card n))
  have h_card_eig₀_eq_eig : Fintype.card {i : Fin (Fintype.card n) // hermAHA.eigenvalues₀ i ≠ 0} =
                            Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} :=
    card_nonzero_eigenvalues₀_eq_card_nonzero_eigenvalues hermAHA

  -- Step 4: Show nonzero eigenvalues₀ only occur for indices < min(#m, #n)
  -- Since rank(A) ≤ min(#m, #n) and eigenvalues₀ is antitone with nonneg values,
  -- indices ≥ min(#m, #n) have eigenvalue 0

  -- Build bijection between {k : Fin (min ..) | σₖ ≠ 0} and {i : Fin (card n) | λᵢ ≠ 0}
  -- The key is that for i with i.val ≥ min(#m, #n), we have λᵢ = 0

  -- Helper: eigenvalues₀ at index ≥ rank are 0
  have h_rank_le : A.rank ≤ min (Fintype.card m) (Fintype.card n) := rank_le_min_card A

  -- The nonzero eigenvalues₀ are exactly those at indices < rank(A) ≤ min(#m, #n)
  -- Due to antitone property and rank = card of nonzero eigenvalues

  -- Build the bijection via restriction
  have h_card_eq : Fintype.card {k : Fin (min (Fintype.card m) (Fintype.card n)) // singularValues A k ≠ 0} =
                   Fintype.card {i : Fin (Fintype.card n) // hermAHA.eigenvalues₀ i ≠ 0} := by
    -- Forward: k ↦ castLE k (since singularValues uses eigenvalues₀ ∘ castLE)
    -- Backward: i ↦ ⟨i.val, ...⟩ when i.val < min ...
    apply Fintype.card_eq.mpr
    let cast_to_n := fun (k : Fin (min (Fintype.card m) (Fintype.card n))) =>
                       Fin.castLE (Nat.min_le_right _ _) k
    refine ⟨{
      toFun := fun ⟨k, hk⟩ => ⟨cast_to_n k, (singularValues_ne_zero_iff_eigenvalues₀_ne_zero A k).mp hk⟩
      invFun := fun ⟨i, hi⟩ => by
        -- Need to show i.val < min(#m, #n) when eigenvalues₀ i ≠ 0
        -- This follows from: at indices ≥ rank(A), eigenvalues₀ = 0 (by antitonicity)
        -- and rank(A) ≤ min(#m, #n)
        by_cases h_lt : i.val < min (Fintype.card m) (Fintype.card n)
        · refine ⟨⟨i.val, h_lt⟩, ?_⟩
          have h_eq : Fin.castLE (Nat.min_le_right _ _) (⟨i.val, h_lt⟩ :
              Fin (min (Fintype.card m) (Fintype.card n))) = i := by ext; simp
          rw [singularValues_ne_zero_iff_eigenvalues₀_ne_zero]
          simp only [h_eq]
          exact hi
        · -- Contradiction: if i.val ≥ min(#m, #n), then eigenvalues₀ i = 0
          exfalso
          push_neg at h_lt
          -- Since card_nonzero_eigenvalues₀ ≤ rank(A) ≤ min(#m, #n) ≤ i.val,
          -- and eigenvalues₀ is antitone with nonzero entries only for indices < card_nonzero,
          -- we must have eigenvalues₀ i = 0
          -- Use antitone_nonneg_zeros_after_rank
          have h_card_le : Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0} ≤
                           min (Fintype.card m) (Fintype.card n) := by
            calc Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0}
              = Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} := h_card_eig₀_eq_eig
              _ = (Aᴴ * A).rank := h_herm_rank.symm
              _ = A.rank := h_rank_eq.symm
              _ ≤ min (Fintype.card m) (Fintype.card n) := h_rank_le
          have h_zero := antitone_nonneg_zeros_after_rank hermAHA.eigenvalues₀
            hermAHA.eigenvalues₀_antitone
            (fun j => PosSemidef_eigenvalues₀_nonneg h_psd j)
            h_card_le i h_lt
          exact hi h_zero
      left_inv := fun ⟨k, hk⟩ => by
        simp only [cast_to_n]
        -- The invFun at cast_to_n k = ⟨k.val, ...⟩ should give back k
        -- Since k : Fin (min #m #n), we have k.val < min(#m, #n)
        have h_k_lt : k.val < min (Fintype.card m) (Fintype.card n) := k.isLt
        simp only [Fin.coe_castLE, h_k_lt, ↓reduceDIte]
      right_inv := fun ⟨i, hi⟩ => by
        simp only [cast_to_n]
        -- Need: the inverse gives back i
        -- The inverse picks ⟨i.val, h_lt⟩ and castLE gives back i
        -- This requires showing i.val < min(#m, #n)
        have h_lt : i.val < min (Fintype.card m) (Fintype.card n) := by
          by_contra h_not_lt
          push_neg at h_not_lt
          have h_card_le : Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0} ≤
                           min (Fintype.card m) (Fintype.card n) := by
            calc Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0}
              = Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} := h_card_eig₀_eq_eig
              _ = (Aᴴ * A).rank := h_herm_rank.symm
              _ = A.rank := h_rank_eq.symm
              _ ≤ min (Fintype.card m) (Fintype.card n) := h_rank_le
          have h_zero := antitone_nonneg_zeros_after_rank hermAHA.eigenvalues₀
            hermAHA.eigenvalues₀_antitone
            (fun j => PosSemidef_eigenvalues₀_nonneg h_psd j)
            h_card_le i h_not_lt
          exact hi h_zero
        simp only [h_lt, ↓reduceDIte, Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castLE]
    }⟩

  rw [h_rank_eq, h_herm_rank, ← h_card_eig₀_eq_eig, h_card_eq]

/-! ### Frobenius-Singular Value Connection for Rectangular Matrices

This section establishes that for rectangular matrices A : Matrix m n ℂ,
the Frobenius norm squared equals the sum of squared singular values:
  ‖A‖_F² = ∑ k, (singularValues A k)²

**Key insight:**
- trace(Aᴴ*A) = ∑ j:n, eigenvalues j (for the n×n Hermitian matrix Aᴴ*A)
- singularValues A k = √(eigenvalues₀ (Fin.castLE k)) for k < min(#m, #n)
- Eigenvalues for indices ≥ min(#m, #n) are zero (by rank constraint)

Therefore the sum over singular values (indexed by Fin (min #m #n)) captures
all nonzero eigenvalues, and equals the trace.
-/

omit [DecidableEq m] in
/-- Singular values squared equal the corresponding eigenvalues₀ for rectangular matrices.
    This is the rectangular analogue of `singularValues_sq`. -/
theorem singularValues_sq_rect (A : Matrix m n ℂ) (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    (singularValues A k) ^ 2 =
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀
      (Fin.castLE (Nat.min_le_right _ _) k) := by
  unfold singularValues
  have h_nonneg := PosSemidef_eigenvalues₀_nonneg (posSemidef_conjTranspose_mul_self A)
    (Fin.castLE (Nat.min_le_right (Fintype.card m) (Fintype.card n)) k)
  rw [Real.sq_sqrt h_nonneg]

set_option linter.unusedSectionVars false in
/-- Eigenvalues beyond index min(#m, #n) are zero.
    This follows from rank(A) ≤ min(#m, #n) and the eigenvalue structure. -/
theorem eigenvalues₀_zero_beyond_min (A : Matrix m n ℂ) (j : Fin (Fintype.card n))
    (hj : j.val ≥ min (Fintype.card m) (Fintype.card n)) :
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ j = 0 := by
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let h_psd := posSemidef_conjTranspose_mul_self A
  -- rank(A) ≤ min(#m, #n) ≤ j.val
  have h_rank_le : A.rank ≤ min (Fintype.card m) (Fintype.card n) := rank_le_min_card A
  have h_card_nonzero : Fintype.card {i : Fin (Fintype.card n) // hermAHA.eigenvalues₀ i ≠ 0} ≤
                        min (Fintype.card m) (Fintype.card n) := by
    have h_eq := card_nonzero_eigenvalues₀_eq_card_nonzero_eigenvalues hermAHA
    have h_herm_rank := hermAHA.rank_eq_card_non_zero_eigs
    have h_rank_eq : A.rank = (Aᴴ * A).rank := (rank_conjTranspose_mul_self A).symm
    calc Fintype.card {i : Fin (Fintype.card n) // hermAHA.eigenvalues₀ i ≠ 0}
        = Fintype.card {i : n // hermAHA.eigenvalues i ≠ 0} := h_eq
      _ = (Aᴴ * A).rank := h_herm_rank.symm
      _ = A.rank := h_rank_eq.symm
      _ ≤ min (Fintype.card m) (Fintype.card n) := h_rank_le
  exact antitone_nonneg_zeros_after_rank hermAHA.eigenvalues₀
    hermAHA.eigenvalues₀_antitone
    (fun i => PosSemidef_eigenvalues₀_nonneg h_psd i)
    h_card_nonzero j hj

/-- **Sum of squared singular values equals trace** for rectangular matrices.
    For A : Matrix m n ℂ, ∑ k, (singularValues A k)² = Re(trace(Aᴴ * A)).

    This is the rectangular analogue of `sum_sq_singularValues_eq_trace`. -/
theorem sum_sq_singularValues_rect_eq_trace (A : Matrix m n ℂ) :
    ∑ k, (singularValues A k) ^ 2 = Complex.re (Matrix.trace (Aᴴ * A)) := by
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  -- trace(Aᴴ*A) = ∑ j:n, eigenvalues j (as complex numbers)
  have h_trace := hermAHA.trace_eq_sum_eigenvalues
  rw [h_trace, Complex.re_sum]
  -- eigenvalues j = eigenvalues₀ (bijection j)
  -- Note: eigenvalues are ℝ, cast to ℂ, then we take .re which recovers the original ℝ value
  have h_eig_eq : ∀ j : n, hermAHA.eigenvalues j =
      hermAHA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j) := fun _ => rfl
  -- Convert RHS: .re of (ℝ : ℂ) back to ℝ, then eigenvalues to eigenvalues₀
  trans (∑ i : n, hermAHA.eigenvalues i)
  swap
  · apply Finset.sum_congr rfl
    intro j _
    exact (Complex.ofReal_re _).symm
  -- Sum equivalence via bijection n ≃ Fin (card n)
  let e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
  have h_sum_bij : ∑ j : n, hermAHA.eigenvalues j = ∑ i : Fin (Fintype.card n), hermAHA.eigenvalues₀ i := by
    simp_rw [h_eig_eq]
    exact Finset.sum_equiv e (fun _ => by simp [Finset.mem_univ]) (fun _ _ => rfl)
  rw [h_sum_bij]
  -- Now sum over Fin (card n), but only indices < min(#m, #n) contribute (rest are 0)
  -- Use singular values squared = eigenvalues₀ ∘ castLE
  conv_lhs =>
    arg 2; ext k
    rw [singularValues_sq_rect]
  -- Partition Fin (card n) into {i | i.val < min} and {i | i.val ≥ min}
  have h_sum_split : ∑ i : Fin (Fintype.card n), hermAHA.eigenvalues₀ i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => i.val < min (Fintype.card m) (Fintype.card n)),
        hermAHA.eigenvalues₀ i +
      ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card n) => i.val ≥ min (Fintype.card m) (Fintype.card n)),
        hermAHA.eigenvalues₀ i := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
          (p := fun i => i.val < min (Fintype.card m) (Fintype.card n))]
    congr 1
    -- Show filter (not (< min)) = filter (≥ min)
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, ge_iff_le, le_iff_lt_or_eq]
  rw [h_sum_split]
  -- The second sum is 0 (eigenvalues beyond min are 0)
  have h_tail_zero : ∑ i ∈ Finset.univ.filter
      (fun i : Fin (Fintype.card n) => i.val ≥ min (Fintype.card m) (Fintype.card n)),
        hermAHA.eigenvalues₀ i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact eigenvalues₀_zero_beyond_min A i hi
  rw [h_tail_zero, add_zero]
  -- Now show: ∑ k : Fin (min ..), eigenvalues₀ (castLE k) =
  --           ∑ i ∈ filter (< min), eigenvalues₀ i
  symm
  -- The LHS sums over i : Fin (card n) with i.val < min, the RHS sums over k : Fin (min ...)
  -- We establish a bijection: i ↦ ⟨i.val, hi⟩ and k ↦ ⟨k.val, k.isLt_min_right⟩
  refine Finset.sum_bij'
    (fun i hi => ⟨i.val, by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; exact hi⟩)
    (fun k _ => ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.min_le_right _ _)⟩) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_univ]
  · intro k _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k.isLt
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    ext; rfl
  · intro k _
    ext; rfl
  · intro i _
    congr 1

end Matrix.SVD.Rectangular
end Hagi.External.Flywheel
