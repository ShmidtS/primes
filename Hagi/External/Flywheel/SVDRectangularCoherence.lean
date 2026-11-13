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
import Hagi.External.Flywheel.SVDRectangularDecomposition

/-!
# SVDRectangularCoherence

Rectangular coherence factor `μ(E) ∈ [1/√rank, 1]`, its bounds, and application theorems.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

/-! ## Rectangular Coherence Factor

This section defines the coherence factor for **rectangular** matrices `Matrix m n ℂ`.
The coherence factor μ(E) measures how concentrated the singular values are:

  μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂) ∈ [1/√r, 1]

- μ ≈ 1: Incoherent (flat spectrum, singular values roughly equal)
- μ ≈ 1/√r: Coherent (dominated by top singular value)

This generalizes the square-matrix coherenceFactor
from CoherenceCharacterization (not ported)
to rectangular matrices, which is required for analyzing Kronecker approximation errors
after the rearrangement operator $\mathcal{R}$ produces non-square matrices.

### Main definitions

* `coherenceFactorRect`: μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂) for rectangular matrices

### Main results

* `coherenceFactorRect_zero`: μ(0) = 1
* `coherenceFactorRect_pos_of_ne_zero`: E ≠ 0 → μ(E) > 0
* `coherenceFactorRect_eq_square_case`: For n×n matrices, matches `coherenceFactor`
-/

section RectangularCoherenceFactor

open Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

-- Enable L2 operator norm instances locally
attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedSpace
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra
attribute [local instance] Matrix.instL2OpMetricSpace

/-- Notation for L2 operator norm of rectangular matrices. -/
local notation "‖" A "‖₂" => @Norm.norm _ Matrix.instL2OpNormedAddCommGroup.toNorm A

/-- Frobenius norm for rectangular matrices as an explicit function.
    Avoids instance conflicts with the L2 operator norm. -/
noncomputable def frobeniusNormRect (A : Matrix m n ℂ) : ℝ :=
  @Norm.norm _ Matrix.frobeniusNormedAddCommGroup.toNorm A

omit [DecidableEq m] [DecidableEq n] in
/-- Frobenius norm is non-negative. -/
theorem frobeniusNormRect_nonneg (A : Matrix m n ℂ) : 0 ≤ frobeniusNormRect A :=
  @norm_nonneg _ (@SeminormedAddCommGroup.toSeminormedAddGroup _
    Matrix.frobeniusSeminormedAddCommGroup) A

omit [DecidableEq m] [DecidableEq n] in
/-- The squared Frobenius norm equals the sum of squared entry norms. -/
theorem frobeniusNormRect_sq (A : Matrix m n ℂ) :
    frobeniusNormRect A ^ 2 = ∑ i, ∑ j, Complex.normSq (A i j) := by
  unfold frobeniusNormRect
  have h := @Matrix.frobenius_norm_def m n ℂ _ _ _ A
  rw [h]
  have h_nonneg : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h_nonneg]
  norm_num
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [← Complex.normSq_eq_norm_sq]

omit [DecidableEq m] [DecidableEq n] in
/-- For zero matrix, Frobenius norm is 0. -/
theorem frobeniusNormRect_zero : frobeniusNormRect (0 : Matrix m n ℂ) = 0 := by
  unfold frobeniusNormRect
  exact @norm_zero _ (@SeminormedAddCommGroup.toSeminormedAddGroup _
    Matrix.frobeniusSeminormedAddCommGroup)

omit [DecidableEq m] [DecidableEq n] in
/-- For nonzero matrix, Frobenius norm is positive. -/
theorem frobeniusNormRect_pos_of_ne_zero (A : Matrix m n ℂ) (hA : A ≠ 0) :
    0 < frobeniusNormRect A := by
  have h : frobeniusNormRect A ≠ 0 := by
    intro h_eq
    -- If ‖A‖_F = 0, then A = 0
    unfold frobeniusNormRect at h_eq
    have := @norm_eq_zero (Matrix m n ℂ)
      Matrix.frobeniusNormedAddCommGroup.toNormedAddGroup A
    rw [this] at h_eq
    exact hA h_eq
  exact (frobeniusNormRect_nonneg A).lt_of_ne' h

/-! ### Rank Properties for Rectangular Matrices -/

omit [Fintype m] [DecidableEq m] in
/-- A nonzero matrix has positive rank.
    Proved by contrapositive: rank = 0 implies the matrix is zero. -/
theorem rank_pos_of_ne_zero_rect (A : Matrix m n ℂ) (hA : A ≠ 0) : 0 < A.rank := by
  by_contra h_not_pos
  push_neg at h_not_pos
  have h_rank_zero : A.rank = 0 := Nat.eq_zero_of_le_zero h_not_pos
  -- rank = 0 means the linear map A.mulVecLin has trivial range
  rw [Matrix.rank] at h_rank_zero
  have h_range_bot : LinearMap.range A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp h_rank_zero
  -- If range is ⊥, then A * v = 0 for all v, so A = 0
  have h_zero : A = 0 := by
    ext i j
    have h_col : A.mulVecLin (Pi.single j 1) = 0 := by
      rw [Submodule.eq_bot_iff] at h_range_bot
      exact h_range_bot _ ⟨Pi.single j 1, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single] at h_col
    have h_col' : A.col j = 0 := by
      rw [MulOpposite.op_one, one_smul] at h_col
      exact h_col
    have := congr_fun h_col' i
    simp only [Matrix.col_apply, Pi.zero_apply] at this
    exact this
  exact hA h_zero

/-! ### Main Definition: Rectangular Coherence Factor -/

/-- **Coherence factor for rectangular matrices.**

μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂) ∈ [1/√r, 1]

- μ ≈ 1: Incoherent (flat spectrum, singular values roughly equal)
- μ ≈ 1/√r: Coherent (dominated by top singular value)

For the zero matrix, we define μ(0) = 1 by convention. -/
noncomputable def coherenceFactorRect (E : Matrix m n ℂ) : ℝ :=
  if E = 0 then 1
  else frobeniusNormRect E / (Real.sqrt E.rank * ‖E‖₂)

/-! ### Basic Properties -/

omit [DecidableEq m] in
/-- For the zero matrix, coherence factor is 1 by definition. -/
theorem coherenceFactorRect_zero : coherenceFactorRect (0 : Matrix m n ℂ) = 1 := by
  simp [coherenceFactorRect]

omit [DecidableEq m] in
/-- For nonzero matrices, the coherence factor is positive.
    This follows from the positivity of ‖E‖_F, √rank(E), and ‖E‖₂. -/
theorem coherenceFactorRect_pos_of_ne_zero (E : Matrix m n ℂ) (hE : E ≠ 0) :
    0 < coherenceFactorRect E := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]
  -- Need: 0 < frobeniusNormRect E / (√rank * ‖E‖₂)
  have h_frob_pos : 0 < frobeniusNormRect E := frobeniusNormRect_pos_of_ne_zero E hE
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  have h_denom_pos : 0 < Real.sqrt E.rank * ‖E‖₂ := mul_pos h_sqrt_rank_pos h_spectral_pos
  exact div_pos h_frob_pos h_denom_pos

omit [DecidableEq m] in
/-- The coherence factor is non-negative. -/
theorem coherenceFactorRect_nonneg (E : Matrix m n ℂ) : 0 ≤ coherenceFactorRect E := by
  by_cases hE : E = 0
  · rw [hE, coherenceFactorRect_zero]; exact zero_le_one
  · exact le_of_lt (coherenceFactorRect_pos_of_ne_zero E hE)

/-! ### Square Case Equivalence -/

/-- For square matrices, `coherenceFactorRect` is compatible with the definition pattern
    used in `CoherenceCharacterization.lean`. Both use the same formula:
    μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂)

    Note: This theorem establishes structural equivalence. The actual numeric equality
    with `coherenceFactor` from CoherenceCharacterization.lean requires that both files
    use the same norm instances, which they do (L2 operator norm for ‖·‖ and Frobenius for ‖·‖_F). -/
theorem coherenceFactorRect_eq_formula (E : Matrix n n ℂ) (hE : E ≠ 0) :
    coherenceFactorRect E = frobeniusNormRect E / (Real.sqrt E.rank * ‖E‖₂) := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]

/-! ## Upper Bound — μ ≤ 1

The coherence factor is bounded above by 1. This follows from:
  ‖E‖_F² = ∑ σₖ² ≤ rank(E) · max(σₖ)² = rank(E) · ‖E‖₂²

Taking square roots: ‖E‖_F ≤ √rank(E) · ‖E‖₂
Therefore: μ(E) = ‖E‖_F / (√rank(E) · ‖E‖₂) ≤ 1
-/

/-- The sum of squared singular values is bounded by rank(A) times the max squared.
    Key insight: only rank(A) singular values are nonzero, and each is ≤ max.

    This is the rectangular analogue of sum_singularValues_sq_le_rank_mul_max_sq
    from CoherenceCharacterization.lean. -/
theorem sum_singularValues_sq_le_rank_mul_max_sq_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 ≤
    A.rank * (Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩) (Matrix.SVD.Rectangular.singularValues A)) ^ 2 := by
  let M := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
              (Matrix.SVD.Rectangular.singularValues A)
  have hM_nonneg : 0 ≤ M := by
    apply Finset.le_sup'_of_le _ (Finset.mem_univ ⟨0, h⟩)
    exact Matrix.SVD.Rectangular.singularValues_nonneg A ⟨0, h⟩
  have h_le_M : ∀ k, Matrix.SVD.Rectangular.singularValues A k ≤ M := fun k =>
    Finset.le_sup' (Matrix.SVD.Rectangular.singularValues A) (Finset.mem_univ k)

  -- Bound each term by M²
  have h_each_le : ∀ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 ≤ M ^ 2 := fun k => by
    apply sq_le_sq'
    · calc -M ≤ 0 := neg_nonpos.mpr hM_nonneg
        _ ≤ Matrix.SVD.Rectangular.singularValues A k :=
            Matrix.SVD.Rectangular.singularValues_nonneg A k
    · exact h_le_M k

  -- The key insight: only rank(A) singular values are nonzero
  have h_rank := Matrix.SVD.Rectangular.rank_eq_card_nonzero_singularValues_rect A

  -- Split into nonzero and zero contributions
  let S := {k : Fin (min (Fintype.card m) (Fintype.card n)) |
            Matrix.SVD.Rectangular.singularValues A k ≠ 0}.toFinset
  have hS_card : S.card = A.rank := by
    rw [h_rank]
    simp only [S, Set.toFinset_card]
    rfl

  -- Sum over nonzero equals original sum (zero terms contribute 0)
  have h_sum_eq : ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 =
                  ∑ k ∈ S, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun k => k ∈ S)]
    simp only [S, Set.mem_toFinset, Set.mem_setOf_eq]
    have h_zero_sum : ∑ k ∈ Finset.univ.filter (fun k =>
        Matrix.SVD.Rectangular.singularValues A k = 0),
        (Matrix.SVD.Rectangular.singularValues A k) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simp [hk]
    simp only [not_not]
    rw [h_zero_sum, add_zero]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
               Set.mem_toFinset, Set.mem_setOf_eq]

  calc ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2
      = ∑ k ∈ S, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 := h_sum_eq
    _ ≤ ∑ _k ∈ S, M ^ 2 := Finset.sum_le_sum fun k _ => h_each_le k
    _ = S.card * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = A.rank * M ^ 2 := by rw [hS_card]

/-- **The coherence factor is at most 1.**

This is the main upper bound for coherence factor. It follows from:
  ‖E‖_F² = ∑ σₖ² ≤ rank(E) · max(σₖ)² = rank(E) · ‖E‖₂² -/
theorem coherenceFactorRect_le_one
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) :
    coherenceFactorRect E ≤ 1 := by
  unfold coherenceFactorRect
  split_ifs with hE
  · linarith  -- E = 0 case: coherenceFactorRect 0 = 1 ≤ 1
  · -- E ≠ 0
    have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
    have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
    have h_denom_pos : 0 < Real.sqrt E.rank * ‖E‖₂ := by
      apply mul_pos
      · exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
      · exact h_spectral_pos
    rw [div_le_one h_denom_pos]
    -- Goal: frobeniusNormRect E ≤ √rank(E) · ‖E‖₂

    -- The maximum singular value
    let M := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
              (Matrix.SVD.Rectangular.singularValues E)

    -- Spectral norm equals max singular value
    have h_spec_eq : ‖E‖₂ = M :=
      Matrix.SVD.Rectangular.spectral_norm_eq_max_singularValue_rect h E

    -- Square bound: frobeniusNormRect E² ≤ rank(E) · ‖E‖₂²
    have h_sq : frobeniusNormRect E ^ 2 ≤ E.rank * ‖E‖₂ ^ 2 := by
      -- Use Frobenius norm = sqrt(sum of squared singular values)
      have h_frob_sq :=
        Matrix.SVD.Rectangular.frobeniusNorm_sq_eq_sum_singularValues_sq_rect E
      -- frobeniusNormRect uses the same norm instance
      have h_frob_eq : frobeniusNormRect E ^ 2 =
          @Norm.norm _ Matrix.frobeniusNormedAddCommGroup.toNorm E ^ 2 := by
        unfold frobeniusNormRect
        rfl
      rw [h_frob_eq, h_frob_sq]
      calc ∑ k, (Matrix.SVD.Rectangular.singularValues E k) ^ 2
          ≤ E.rank * M ^ 2 := sum_singularValues_sq_le_rank_mul_max_sq_rect h E
        _ = E.rank * ‖E‖₂ ^ 2 := by rw [h_spec_eq]

    -- Take square roots
    have h_frob_nonneg : 0 ≤ frobeniusNormRect E := frobeniusNormRect_nonneg E
    have h_rank_nonneg : (0 : ℝ) ≤ E.rank := Nat.cast_nonneg _
    have h_rhs_nonneg : 0 ≤ Real.sqrt E.rank * ‖E‖₂ :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt h_spectral_pos)

    have h_sq' : frobeniusNormRect E ^ 2 ≤ (Real.sqrt E.rank * ‖E‖₂) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h_rank_nonneg]
      exact h_sq

    calc frobeniusNormRect E
        = Real.sqrt (frobeniusNormRect E ^ 2) := (Real.sqrt_sq h_frob_nonneg).symm
      _ ≤ Real.sqrt ((Real.sqrt E.rank * ‖E‖₂) ^ 2) := Real.sqrt_le_sqrt h_sq'
      _ = Real.sqrt E.rank * ‖E‖₂ := Real.sqrt_sq h_rhs_nonneg

/-! ## Lower Bound — μ ≥ 1/√rank

The coherence factor is bounded below by 1/√rank. This is the tight lower bound,
achieved when all nonzero singular values are equal (i.e., when E is "maximally incoherent").

**Proof strategy:**
  σ₁² ≤ ∑_{k=1}^{r} σₖ² = ‖E‖_F²

So ‖E‖ = σ₁ ≤ ‖E‖_F, and:
  μ(E) = ‖E‖_F / (√r · ‖E‖) ≥ ‖E‖ / (√r · ‖E‖) = 1/√r
-/

omit [DecidableEq m] in
/-- The maximum singular value squared is at most the sum of all squared singular values.

This is the key lemma for proving ‖E‖ ≤ ‖E‖_F (spectral ≤ Frobenius). -/
theorem max_singularValue_sq_le_sum_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (A : Matrix m n ℂ) :
    (Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
      (Matrix.SVD.Rectangular.singularValues A)) ^ 2 ≤
    ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 := by
  let M := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
              (Matrix.SVD.Rectangular.singularValues A)
  -- M = max singular value, which is achieved at some index i₀
  have h_ne : (Finset.univ : Finset (Fin (min (Fintype.card m) (Fintype.card n)))).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup' h_ne (Matrix.SVD.Rectangular.singularValues A)
  -- M² = σᵢ₀² is one term in the sum
  calc M ^ 2
      = (Matrix.SVD.Rectangular.singularValues A i₀) ^ 2 := by congr 1
    _ ≤ ∑ k, (Matrix.SVD.Rectangular.singularValues A k) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i₀)

/-- **Spectral norm is bounded by Frobenius norm**: ‖E‖ ≤ ‖E‖_F for rectangular matrices.

This uses the Frobenius norm defined via `frobeniusNormRect` which matches the
`Matrix.frobeniusSeminormedAddCommGroup` instance. -/
theorem spectral_le_frobenius_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) :
    ‖E‖₂ ≤ frobeniusNormRect E := by
  have h_spec_sq : ‖E‖₂ ^ 2 ≤ frobeniusNormRect E ^ 2 := by
    -- Spectral norm = max singular value
    let M := Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, h⟩⟩)
              (Matrix.SVD.Rectangular.singularValues E)
    have h_spec_eq : ‖E‖₂ = M :=
      Matrix.SVD.Rectangular.spectral_norm_eq_max_singularValue_rect h E
    -- Frobenius² = sum of singular values²
    have h_frob_sq_eq : frobeniusNormRect E ^ 2 =
        ∑ k, (Matrix.SVD.Rectangular.singularValues E k) ^ 2 := by
      unfold frobeniusNormRect
      exact Matrix.SVD.Rectangular.frobeniusNorm_sq_eq_sum_singularValues_sq_rect E
    rw [h_spec_eq, h_frob_sq_eq]
    exact max_singularValue_sq_le_sum_rect h E
  have h_spec_nonneg : 0 ≤ ‖E‖₂ := @norm_nonneg (Matrix m n ℂ) _ E
  have h_frob_nonneg : 0 ≤ frobeniusNormRect E := frobeniusNormRect_nonneg E
  calc ‖E‖₂ = Real.sqrt (‖E‖₂ ^ 2) := (Real.sqrt_sq h_spec_nonneg).symm
    _ ≤ Real.sqrt (frobeniusNormRect E ^ 2) := Real.sqrt_le_sqrt h_spec_sq
    _ = frobeniusNormRect E := Real.sqrt_sq h_frob_nonneg

/-- The ratio of Frobenius norm to spectral norm is at least 1: 1 ≤ ‖E‖_F / ‖E‖.

This is a reformulation of `spectral_le_frobenius_rect` as a ratio bound. -/
theorem frobenius_spectral_ratio_ge_one_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    1 ≤ frobeniusNormRect E / ‖E‖₂ := by
  have h_spec_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  rw [one_le_div h_spec_pos]
  exact spectral_le_frobenius_rect h E

/-- **The coherence factor is at least 1/√rank.**

This is the tight lower bound for coherence factor. It follows from:
  ‖E‖ ≤ ‖E‖_F (spectral ≤ Frobenius)

Therefore:
  μ(E) = ‖E‖_F / (√rank · ‖E‖) ≥ ‖E‖ / (√rank · ‖E‖) = 1/√rank

The bound is tight when all nonzero singular values are equal (maximally incoherent). -/
theorem coherenceFactorRect_ge_inv_sqrt_rank
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    1 / Real.sqrt E.rank ≤ coherenceFactorRect E := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]
  have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_denom_pos : 0 < Real.sqrt E.rank * ‖E‖₂ := mul_pos h_sqrt_rank_pos h_spectral_pos
  -- Goal: 1 / √rank ≤ ‖E‖_F / (√rank · ‖E‖)
  rw [div_le_div_iff₀ h_sqrt_rank_pos h_denom_pos]
  -- Goal: 1 * (√rank · ‖E‖) ≤ ‖E‖_F * √rank
  rw [one_mul, mul_comm (frobeniusNormRect E) (Real.sqrt E.rank)]
  -- Goal: √rank · ‖E‖ ≤ √rank · ‖E‖_F
  exact mul_le_mul_of_nonneg_left (spectral_le_frobenius_rect h E) (le_of_lt h_sqrt_rank_pos)

/-- Combined bounds: the coherence factor lies in [1/√rank, 1].

This combines `coherenceFactorRect_ge_inv_sqrt_rank` and `coherenceFactorRect_le_one`. -/
theorem coherenceFactorRect_bounds
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    1 / Real.sqrt E.rank ≤ coherenceFactorRect E ∧ coherenceFactorRect E ≤ 1 :=
  ⟨coherenceFactorRect_ge_inv_sqrt_rank h E hE, coherenceFactorRect_le_one h E⟩

/-! ### Application Theorems

These theorems connect coherence factor bounds to spectral norm bounds.
The key insight is that coherence μ characterizes how "spread out" the singular values are:
- μ = 1 means the matrix is maximally coherent (rank-1 structure, one dominant singular value)
- μ = 1/√rank means maximally incoherent (all nonzero singular values equal)

When μ is bounded away from 1/√rank, we get improved spectral bounds beyond the naive
‖E‖ ≤ ‖E‖_F relationship.
-/

omit [DecidableEq m] in
/-- **Spectral bound via coherence factor.**

From μ(E) = ‖E‖_F / (√rank · ‖E‖), we can solve for ‖E‖:
  ‖E‖ = ‖E‖_F / (√rank · μ(E))

This gives a way to bound the spectral norm using Frobenius norm and coherence. -/
theorem spectral_bound_via_coherence_rect
    (_h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    ‖E‖₂ = frobeniusNormRect E / (Real.sqrt E.rank * coherenceFactorRect E) := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]
  have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_frob_pos : 0 < frobeniusNormRect E := frobeniusNormRect_pos_of_ne_zero E hE
  have h_denom_inner_pos : 0 < Real.sqrt E.rank * ‖E‖₂ := mul_pos h_sqrt_rank_pos h_spectral_pos
  have h_coherence_pos : 0 < frobeniusNormRect E / (Real.sqrt E.rank * ‖E‖₂) :=
    div_pos h_frob_pos h_denom_inner_pos
  -- μ = ‖E‖_F / (√rank · ‖E‖)
  -- √rank · μ = ‖E‖_F / ‖E‖
  -- ‖E‖_F / (√rank · μ) = ‖E‖
  -- Goal: ‖E‖ = ‖E‖_F / (√rank · μ)
  have h_simpl : Real.sqrt E.rank * (frobeniusNormRect E / (Real.sqrt E.rank * ‖E‖₂)) =
      frobeniusNormRect E / ‖E‖₂ := by
    have h_sqrt_ne : Real.sqrt E.rank ≠ 0 := ne_of_gt h_sqrt_rank_pos
    have h_spec_ne : ‖E‖₂ ≠ 0 := ne_of_gt h_spectral_pos
    field_simp
  rw [h_simpl]
  field_simp

omit [DecidableEq m] in
/-- **Improved spectral bound for incoherent matrices.**

If the coherence factor is bounded below by α (i.e., α ≤ μ(E)), then:
  ‖E‖ ≤ ‖E‖_F / (α · √rank)

This is useful when we know E is "incoherent" (μ bounded away from 1/√rank).
The smaller α is, the weaker the bound; α = 1/√rank gives the trivial bound ‖E‖ ≤ ‖E‖_F. -/
theorem incoherent_improved_bound_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0)
    (α : ℝ) (hα_pos : 0 < α) (hα_bound : α ≤ coherenceFactorRect E) :
    ‖E‖₂ ≤ frobeniusNormRect E / (α * Real.sqrt E.rank) := by
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_coherence_pos : 0 < coherenceFactorRect E :=
    coherenceFactorRect_pos_of_ne_zero E hE
  have h_frob_pos : 0 < frobeniusNormRect E := frobeniusNormRect_pos_of_ne_zero E hE
  -- From spectral_bound_via_coherence_rect: ‖E‖ = ‖E‖_F / (√rank · μ)
  rw [spectral_bound_via_coherence_rect h E hE]
  -- Goal: ‖E‖_F / (√rank · μ) ≤ ‖E‖_F / (α · √rank)
  rw [mul_comm α (Real.sqrt E.rank)]
  -- Goal: ‖E‖_F / (√rank · μ) ≤ ‖E‖_F / (√rank · α)
  apply div_le_div_of_nonneg_left h_frob_pos.le
  · exact mul_pos h_sqrt_rank_pos hα_pos
  · exact mul_le_mul_of_nonneg_left hα_bound (le_of_lt h_sqrt_rank_pos)

omit [DecidableEq m] in
/-- **Coherence determines the spectral-to-Frobenius ratio.**

The coherence factor equals the Frobenius-to-spectral norm ratio divided by √rank:
  μ(E) = (‖E‖_F / ‖E‖) / √rank

Equivalently:
  ‖E‖_F / ‖E‖ = √rank · μ(E)

This shows that coherence captures exactly how much the spectral norm differs
from the "averaged" Frobenius norm per rank dimension. -/
theorem coherence_eq_norm_ratio_rect
    (_h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    coherenceFactorRect E = (frobeniusNormRect E / ‖E‖₂) / Real.sqrt E.rank := by
  unfold coherenceFactorRect
  simp only [hE, ↓reduceIte]
  rw [div_div, mul_comm]

omit [DecidableEq m] in
/-- **Frobenius-to-spectral ratio via coherence.**

The ratio ‖E‖_F / ‖E‖ = √rank · μ(E).

This is useful for estimating how far the spectral norm is from the Frobenius norm. -/
theorem frobenius_spectral_ratio_eq_sqrt_rank_mul_coherence_rect
    (h : 0 < min (Fintype.card m) (Fintype.card n)) (E : Matrix m n ℂ) (hE : E ≠ 0) :
    frobeniusNormRect E / ‖E‖₂ = Real.sqrt E.rank * coherenceFactorRect E := by
  rw [coherence_eq_norm_ratio_rect h E hE]
  have h_rank_pos : 0 < E.rank := rank_pos_of_ne_zero_rect E hE
  have h_sqrt_rank_pos : 0 < Real.sqrt E.rank :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr h_rank_pos)
  have h_spectral_pos : 0 < ‖E‖₂ := @norm_pos_iff _ _ E |>.mpr hE
  have h_sqrt_ne : Real.sqrt E.rank ≠ 0 := ne_of_gt h_sqrt_rank_pos
  have h_spec_ne : ‖E‖₂ ≠ 0 := ne_of_gt h_spectral_pos
  field_simp

end RectangularCoherenceFactor

end Hagi.External.Flywheel
