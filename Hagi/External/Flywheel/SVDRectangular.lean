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
import Hagi.External.Flywheel.SVDReal

/-!
# SVDRectangular

Rectangular SVD setup: singular values of `m × n` matrices, shared nonzero eigenvalues, column norms, and left singular vectors.
-/

open Matrix Polynomial
open scoped ComplexOrder MatrixOrder

namespace Hagi.External.Flywheel

/-! ## Rectangular SVD

Extension of SVD to m × n matrices (not necessarily square).

### Mathematical Background

For an m × n matrix A:
- **Aᴴ*A** is an n × n positive semidefinite matrix
- **A*Aᴴ** is an m × m positive semidefinite matrix
- The nonzero eigenvalues of Aᴴ*A and A*Aᴴ are identical (by `Matrix.charpoly_mul_comm'`)
- Singular values σᵢ = √λᵢ where λᵢ are eigenvalues of the smaller Gram matrix

### Goal Statement

For any m × n complex matrix A, there exist:
- U ∈ unitaryGroup m ℂ (m × m unitary)
- V ∈ unitaryGroup n ℂ (n × n unitary)
- S : Matrix m n ℂ (rectangular "diagonal" with singular values)

Such that: **A = U * S * Vᴴ**

### References
- Horn & Johnson, *Matrix Analysis*, Chapter 7
- RectangularSVD-TODO.md for implementation plan
-/

namespace Matrix.SVD.Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Eigenvalue Index Relationship -/

/-- Card of nonzero eigenvalues equals card of nonzero eigenvalues₀ via bijection. -/
lemma card_nonzero_eigenvalues₀_eq_card_nonzero_eigenvalues
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Fintype.card {i : Fin (Fintype.card n) // hA.eigenvalues₀ i ≠ 0} =
    Fintype.card {j : n // hA.eigenvalues j ≠ 0} := by
  -- eigenvalues j = eigenvalues₀ (equiv.symm j), so use equiv for subtype
  let e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
  have h_eq : ∀ j : n, hA.eigenvalues j = hA.eigenvalues₀ (e j) := fun j => rfl
  -- Build equivalence between the subtypes
  let f : {i : Fin (Fintype.card n) // hA.eigenvalues₀ i ≠ 0} →
          {j : n // hA.eigenvalues j ≠ 0} :=
    fun ⟨i, hi⟩ => ⟨e.symm i, by
      simp only [ne_eq, h_eq, e, Equiv.symm_symm, Equiv.symm_apply_apply]
      exact hi⟩
  let g : {j : n // hA.eigenvalues j ≠ 0} →
          {i : Fin (Fintype.card n) // hA.eigenvalues₀ i ≠ 0} :=
    fun ⟨j, hj⟩ => ⟨e j, by rwa [h_eq] at hj⟩
  have hfg : ∀ x, f (g x) = x := fun ⟨j, _⟩ => by simp [f, g]
  have hgf : ∀ x, g (f x) = x := fun ⟨i, _⟩ => by simp [f, g]
  -- Use the equivalence to show equal cardinality
  exact Fintype.card_eq.mpr ⟨{
    toFun := f
    invFun := g
    left_inv := hgf
    right_inv := hfg
  }⟩

set_option linter.unusedSectionVars false in
/-- Eigenvalues₀ of Aᴴ*A at indices beyond rank(A) are zero.

For a matrix A : m × n, rank(Aᴴ*A) = rank(A) ≤ min(m,n).
Since eigenvalues₀ is antitone (sorted decreasing), eigenvalues at index ≥ rank are 0.
When i.val ≥ card m and card m < card n, eigenvalues₀ i = 0. -/
lemma eigenvalues₀_zero_beyond_rank (A : Matrix m n ℂ) (i : Fin (Fintype.card n))
    (h_idx : i.val ≥ Fintype.card m)
    (_h_card : Fintype.card m < Fintype.card n) :
    (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ i = 0 := by
  let hAHA := posSemidef_conjTranspose_mul_self A
  let hermAHA := hAHA.isHermitian

  -- Step 1: eigenvalues₀ is nonneg
  have h_nonneg : ∀ j, 0 ≤ hermAHA.eigenvalues₀ j := PosSemidef_eigenvalues₀_nonneg hAHA

  -- Step 2: eigenvalues₀ is antitone
  have h_anti : Antitone hermAHA.eigenvalues₀ := hermAHA.eigenvalues₀_antitone

  -- Step 3: Rank bound: rank(Aᴴ*A) = rank(A) ≤ card m
  have h_rank_eq : (Aᴴ * A).rank = A.rank := rank_conjTranspose_mul_self A
  have h_rank_le : A.rank ≤ Fintype.card m := rank_le_card_height A

  -- Step 4: Transfer rank to card of nonzero eigenvalues₀
  have h_rank_eigs : Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} = (Aᴴ * A).rank :=
    (hermAHA.rank_eq_card_non_zero_eigs).symm

  have h_card_eigs₀ : Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0} ≤ Fintype.card m := by
    calc Fintype.card {j : Fin (Fintype.card n) // hermAHA.eigenvalues₀ j ≠ 0}
      = Fintype.card {j : n // hermAHA.eigenvalues j ≠ 0} :=
          card_nonzero_eigenvalues₀_eq_card_nonzero_eigenvalues hermAHA
      _ = (Aᴴ * A).rank := h_rank_eigs
      _ = A.rank := h_rank_eq
      _ ≤ Fintype.card m := h_rank_le

  -- Step 5: Apply antitone_nonneg_zeros_after_rank
  exact antitone_nonneg_zeros_after_rank hermAHA.eigenvalues₀ h_anti h_nonneg h_card_eigs₀ i h_idx

/-! ### Singular Values for Rectangular Matrices -/

/-- Singular values for rectangular m × n matrices, indexed by `Fin (min (#m) (#n))`.

These are the square roots of eigenvalues of Aᴴ*A (the n×n Gram matrix), taking
the first `min(m,n)` eigenvalues (sorted in decreasing order by `eigenvalues₀`).

**Design choice**: We always use Aᴴ*A rather than switching between Aᴴ*A and A*Aᴴ.
This ensures consistency with `rightUnitary` (which uses eigenvectors of Aᴴ*A) and
avoids bijection mismatch issues between `equivFin` and `equivOfCardEq` when proving
the SVD equation A*V = U*S.

Mathematical justification: For A ∈ ℂ^{m×n}:
- Aᴴ*A has n eigenvalues, of which at most r = rank(A) ≤ min(m,n) are nonzero
- A*Aᴴ has the same nonzero eigenvalues (by spectrum.nonzero_mul_comm)
- Taking the first min(m,n) eigenvalues from either matrix gives the same values -/
noncomputable def singularValues (A : Matrix m n ℂ) :
    Fin (min (Fintype.card m) (Fintype.card n)) → ℝ := fun k =>
  -- Always use Aᴴ*A (n×n), consistent with rightUnitary
  let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let j : Fin (Fintype.card n) := Fin.castLE (Nat.min_le_right _ _) k
  Real.sqrt (hermAHA.eigenvalues₀ j)

set_option linter.unusedSectionVars false in
/-- Singular values are non-negative. -/
theorem singularValues_nonneg (A : Matrix m n ℂ) (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    0 ≤ singularValues A k := by
  unfold singularValues
  exact Real.sqrt_nonneg _

/-! ### Right and Left Singular Vector Matrices -/


/-- Right singular vectors V: the eigenvector unitary of Aᴴ*A (n×n matrix).

The columns of V form an orthonormal basis of eigenvectors of Aᴴ*A,
ordered by decreasing eigenvalue (and thus decreasing singular value).
This is an n×n unitary matrix. -/
noncomputable def rightUnitary (A : Matrix m n ℂ) : unitaryGroup n ℂ :=
  (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorUnitary

/-- Left singular vectors U: the eigenvector unitary of A*Aᴴ (m×m matrix).

The columns of U form an orthonormal basis of eigenvectors of A*Aᴴ,
ordered by decreasing eigenvalue (and thus decreasing singular value).
This is an m×m unitary matrix. -/
noncomputable def leftUnitary (A : Matrix m n ℂ) : unitaryGroup m ℂ :=
  (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvectorUnitary

/-- The bijection used by eigenvalues to map a Fintype to `Fin (card α)`.
    This is equivalent to `Fintype.equivFin` and matches how Mathlib's
    `eigenvalues` is defined in terms of `eigenvalues₀`.
    We define this directly as `equivFin` for better proof interaction. -/
noncomputable def eigenvaluesBijection (α : Type*) [Fintype α] : α ≃ Fin (Fintype.card α) :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card α))).symm

/-! ### Rectangular "Diagonal" Matrix -/

/-- The rectangular "diagonal" matrix S : Matrix m n ℂ containing singular values.

For a rectangular m×n matrix, S has the structure:
- `S(i, j) = σₖ` if both i and j correspond to the same diagonal index k < min(m,n)
- `S(i, j) = 0` otherwise

This uses `eigenvaluesBijection` to establish canonical orderings of the abstract
index types m and n, consistent with how Mathlib's eigenvalues are indexed.
This ensures that the singular value at diagonal position (i, j) corresponds
to the correct eigenvector column in the unitary matrices. -/
noncomputable def singularDiagonal (A : Matrix m n ℂ) : Matrix m n ℂ := fun i j =>
  let fi : Fin (Fintype.card m) := eigenvaluesBijection m i
  let fj : Fin (Fintype.card n) := eigenvaluesBijection n j
  if h : fi.val = fj.val ∧ fi.val < min (Fintype.card m) (Fintype.card n) then
    Complex.ofReal (singularValues A ⟨fi.val, h.2⟩)
  else
    0

/-! ### Key Lemmas for Rectangular SVD

These lemmas bridge the definitions to the main SVD construction.
The core challenge is relating eigenvalues of AᴴA (n×n) and AAᴴ (m×m) when m ≠ n,
plus adapting square-case column norm proofs to rectangular index types.
-/

/-! #### Index Embedding Helpers

These functions cleanly map indices from `Fin (min #m #n)` to the abstract types m and n.
They compose `Fin.castLE` with `Fintype.equivFin` for canonical bijections. -/

/-- Embed an index from `Fin (min #m #n)` into the type `m`.
    This uses the canonical bijection `Fintype.equivFin m` and `Fin.castLE`. -/
noncomputable def embedMinToM (k : Fin (min (Fintype.card m) (Fintype.card n))) : m :=
  (Fintype.equivFin m).symm (Fin.castLE (Nat.min_le_left _ _) k)

/-- Embed an index from `Fin (min #m #n)` into the type `n`.
    This uses the canonical bijection `Fintype.equivFin n` and `Fin.castLE`. -/
noncomputable def embedMinToN (k : Fin (min (Fintype.card m) (Fintype.card n))) : n :=
  (eigenvaluesBijection n).symm (Fin.castLE (Nat.min_le_right _ _) k)

set_option linter.unusedSectionVars false in
/-- The embedding `embedMinToM` is injective. -/
theorem embedMinToM_injective : Function.Injective (embedMinToM (m := m) (n := n)) := by
  intro k₁ k₂ h
  simp only [embedMinToM] at h
  have h1 : (Fintype.equivFin m).symm (Fin.castLE (Nat.min_le_left _ _) k₁) =
            (Fintype.equivFin m).symm (Fin.castLE (Nat.min_le_left _ _) k₂) := h
  have h2 := (Fintype.equivFin m).symm.injective h1
  exact Fin.castLE_injective _ h2

set_option linter.unusedSectionVars false in
/-- The embedding `embedMinToN` is injective. -/
theorem embedMinToN_injective : Function.Injective (embedMinToN (m := m) (n := n)) := by
  intro k₁ k₂ h
  simp only [embedMinToN] at h
  have h2 := (eigenvaluesBijection n).symm.injective h
  exact Fin.castLE_injective _ h2

/-! #### Type Coercion Bridge Lemmas -/


omit [DecidableEq m] [DecidableEq n] in
/-- The eigenvalues bijection composed with embedMinToN recovers castLE.
    This is the fundamental bridge: `eigenvaluesBijection n' (embedMinToN k) = castLE k`.

    Mathematical insight: Both `eigenvaluesBijection` (via equivOfCardEq.symm) and
    `embedMinToN` (via equivFin.symm) are noncomputable bijections chosen via Trunc.out.
    This lemma states they compose to give the expected castLE result. -/
theorem eigenvaluesBijection_embedMinToN (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    eigenvaluesBijection n (embedMinToN k) = Fin.castLE (Nat.min_le_right _ _) k := by
  unfold embedMinToN eigenvaluesBijection
  -- eigenvaluesBijection = equivFin, embedMinToN uses equivFin.symm
  -- So: equivFin ((equivFin).symm (castLE k)) = castLE k by apply/symm cancel
  simp only [Equiv.apply_symm_apply]

omit [DecidableEq m] [DecidableEq n] in
/-- Inverse direction: from a Fin index in range, we can find the corresponding
    element of n' that maps back to it. -/
theorem embedMinToN_eigenvaluesBijection_inverse
    (i : Fin (Fintype.card n)) (hi : i.val < min (Fintype.card m) (Fintype.card n)) :
    embedMinToN (m := m) ⟨i.val, hi⟩ = (eigenvaluesBijection n).symm i := by
  unfold embedMinToN eigenvaluesBijection
  -- Goal: (equivFin n).symm (castLE ⟨i.val, hi⟩) = (equivFin n).symm i
  -- castLE ⟨i.val, hi⟩ = i (both have the same val), so congr closes it
  congr 1

omit [DecidableEq m] in
/-- The eigenvalue at embedMinToN(k) equals the eigenvalue at castLE(k).
    This is the key lemma for bridging singular value proofs to eigenvalue proofs. -/
theorem eigenvalues_at_embedMinToN_eq_eigenvalues₀_castLE
    (A : Matrix m n ℂ) (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    let hermAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
    hermAHA.eigenvalues (embedMinToN k) = hermAHA.eigenvalues₀ (Fin.castLE (Nat.min_le_right _ _) k) := by
  intro hermAHA
  -- eigenvalues j = eigenvalues₀ ((equivOfCardEq ...).symm j) by Mathlib definition
  -- So we need: (equivOfCardEq ...).symm (embedMinToN k) = castLE k
  simp only [Matrix.IsHermitian.eigenvalues]
  congr 1
  -- eigenvaluesBijection = equivFin = (equivOfCardEq ...).symm by equivFin_eq_equivOfCardEq_symm
  have h := eigenvaluesBijection_embedMinToN (m := m) k
  unfold eigenvaluesBijection at h
  -- h : equivFin n (embedMinToN k) = castLE k
  -- Need: (equivOfCardEq ...).symm (embedMinToN k) = castLE k
  exact h

/-- For j : n' with eigenvaluesBijection(j).val < min, we can convert j to a Fin min index. -/
noncomputable def finMinOfAbstract (j : n)
    (hj : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    Fin (min (Fintype.card m) (Fintype.card n)) :=
  ⟨(eigenvaluesBijection n j).val, hj⟩

omit [DecidableEq m] [DecidableEq n] in
/-- The conversion finMinOfAbstract is inverse to embedMinToN when applied appropriately. -/
theorem embedMinToN_finMinOfAbstract (j : n)
    (hj : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    embedMinToN (m := m) (finMinOfAbstract j hj) = j := by
  unfold finMinOfAbstract embedMinToN eigenvaluesBijection
  -- Goal: (equivOfCardEq ..) (castLE ⟨(equivOfCardEq ..).symm j, hj⟩) = j
  -- Key: castLE preserves value, and equivOfCardEq (equivOfCardEq.symm j) = j
  simp only [Equiv.symm_symm, Fin.val_mk]
  have hfin : Fin.castLE (Nat.min_le_right _ _)
      ⟨((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm j).val, hj⟩
      = (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm j := Fin.ext rfl
  rw [hfin]
  exact Equiv.apply_symm_apply _ _

set_option linter.unusedSectionVars false in
/-- eigenvaluesBijection_val_eq_finMinOfAbstract -/
theorem eigenvaluesBijection_finMinOfAbstract (j : n)
    (hj : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    (eigenvaluesBijection n j).val = (finMinOfAbstract (m := m) j hj).val := rfl

omit [DecidableEq m] in
/-- Key bridge for proofs: singularValues at k equals sqrt of eigenvalue at embedMinToN k. -/
theorem singularValues_eq_sqrt_eigenvalues_at_embedMinToN
    (A : Matrix m n ℂ) (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    singularValues A k =
    Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues (embedMinToN k)) := by
  simp only [singularValues]
  -- Goal: sqrt(hermAHA.eigenvalues₀ (castLE k)) = sqrt(hermAHA.eigenvalues (embedMinToN k))
  -- We need to show the arguments to sqrt are equal
  rw [eigenvalues_at_embedMinToN_eq_eigenvalues₀_castLE]

/-! #### Shared Nonzero Eigenvalues -/

/-- The characteristic polynomials of AᴴA and AAᴴ are related by powers of X.
    X^n · charpoly(A * B) = X^m · charpoly(B * A)
    i.e., X^n · charpoly(A * Aᴴ) = X^m · charpoly(Aᴴ * A)
    Rearranging: X^m · charpoly(AᴴA) = X^n · charpoly(AAᴴ) -/
theorem charpoly_conjTranspose_mul_self_mul_comm (A : Matrix m n ℂ) :
    Polynomial.X ^ Fintype.card m * (Aᴴ * A).charpoly =
    Polynomial.X ^ Fintype.card n * (A * Aᴴ).charpoly := by
  -- Apply charpoly_mul_comm' with first matrix = A, second = Aᴴ
  have h := Matrix.charpoly_mul_comm' A Aᴴ
  -- h : X^n * (A * Aᴴ).charpoly = X^m * (Aᴴ * A).charpoly
  exact h.symm

/-- Helper: X^k * p ≠ 0 when p ≠ 0 over ℂ[X]. -/
private lemma X_pow_mul_ne_zero {k : ℕ} {p : ℂ[X]} (hp : p ≠ 0) : Polynomial.X ^ k * p ≠ 0 :=
  mul_ne_zero (pow_ne_zero k Polynomial.X_ne_zero) hp

/-- Helper: For μ ≠ 0, μ ∈ roots(X^k * p) ↔ μ ∈ roots(p).
    The X^k factor only adds zeros as roots. -/
private lemma mem_roots_X_pow_mul_iff_of_ne_zero {k : ℕ} {p : ℂ[X]} {μ : ℂ}
    (hp : p ≠ 0) (hμ : μ ≠ 0) : μ ∈ (Polynomial.X ^ k * p).roots ↔ μ ∈ p.roots := by
  have hne : Polynomial.X ^ k * p ≠ 0 := X_pow_mul_ne_zero hp
  rw [Polynomial.roots_mul hne, Multiset.mem_add, Polynomial.roots_X_pow]
  constructor
  · intro h
    rcases h with h_left | h_right
    · rw [Multiset.mem_nsmul] at h_left
      simp only [Multiset.mem_singleton] at h_left
      exact absurd h_left.2 hμ
    · exact h_right
  · intro h
    right
    exact h

/-- The nonzero eigenvalues of AᴴA and AAᴴ match.

    This is a consequence of the characteristic polynomial relation:
    X^m · charpoly(AᴴA) = X^n · charpoly(AAᴴ)

    For any nonzero μ, being an eigenvalue means being a root of the charpoly.
    Since X^k only adds zeros as roots, the nonzero roots of both sides match. -/
theorem eigenvalues_shared_rectangular_aux (A : Matrix m n ℂ) (μ : ℝ) (hμ : μ ≠ 0) :
    (∃ i : n, (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i = μ) ↔
    (∃ j : m, (posSemidef_self_mul_conjTranspose A).isHermitian.eigenvalues j = μ) := by
  let hAHA := (posSemidef_conjTranspose_mul_self A).isHermitian
  let hAAH := (posSemidef_self_mul_conjTranspose A).isHermitian
  -- The characteristic polynomial equality: X^n * (AAᴴ).charpoly = X^m * (AᴴA).charpoly
  have h_charpoly := charpoly_mul_comm' A Aᴴ
  -- Roots of charpoly = eigenvalues mapped to ℂ
  have h_roots_AHA := hAHA.roots_charpoly_eq_eigenvalues
  have h_roots_AAH := hAAH.roots_charpoly_eq_eigenvalues
  -- Convert eigenvalue existence to root membership in charpoly
  have h_mem_iff_AHA : (∃ i : n, hAHA.eigenvalues i = μ) ↔ (↑μ : ℂ) ∈ (Aᴴ * A).charpoly.roots := by
    rw [h_roots_AHA, Multiset.mem_map]
    constructor
    · intro ⟨i, hi⟩
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simp only [Function.comp_apply]
      exact congrArg _ hi
    · intro ⟨i, _, hi⟩
      exact ⟨i, Complex.ofReal_injective hi⟩
  have h_mem_iff_AAH : (∃ j : m, hAAH.eigenvalues j = μ) ↔ (↑μ : ℂ) ∈ (A * Aᴴ).charpoly.roots := by
    rw [h_roots_AAH, Multiset.mem_map]
    constructor
    · intro ⟨j, hj⟩
      refine ⟨j, Finset.mem_univ j, ?_⟩
      simp only [Function.comp_apply]
      exact congrArg _ hj
    · intro ⟨j, _, hj⟩
      exact ⟨j, Complex.ofReal_injective hj⟩
  rw [h_mem_iff_AHA, h_mem_iff_AAH]
  -- Now use the polynomial equality to show nonzero root membership is equivalent
  have hp_AHA : (Aᴴ * A).charpoly ≠ 0 := Matrix.charpoly_monic _ |>.ne_zero
  have hp_AAH : (A * Aᴴ).charpoly ≠ 0 := Matrix.charpoly_monic _ |>.ne_zero
  have hμ' : (↑μ : ℂ) ≠ 0 := by simp [hμ]
  -- μ ∈ (AᴴA).charpoly.roots ↔ μ ∈ (X^m * AᴴA.charpoly).roots  (since μ ≠ 0)
  --                          ↔ μ ∈ (X^n * AAᴴ.charpoly).roots  (by h_charpoly)
  --                          ↔ μ ∈ (AAᴴ).charpoly.roots        (since μ ≠ 0)
  rw [← mem_roots_X_pow_mul_iff_of_ne_zero hp_AHA hμ',
      ← mem_roots_X_pow_mul_iff_of_ne_zero hp_AAH hμ',
      h_charpoly.symm]


/-! #### Column Norms for Rectangular A*V

For a rectangular m×n matrix A with V = rightUnitary A (n×n), the product A*V is m×n.
The key lemma: the squared norm of column j of A*V equals the j-th eigenvalue of AᴴA,
which equals (singularValues A k)² when j corresponds to index k.
-/

set_option linter.unusedSectionVars false in
/-- Key computational lemma: (A*V)ᴴ * (A*V) = diag(eigenvalues of AᴴA)
    where V is the eigenvector matrix of AᴴA.

    This is the rectangular analogue of `conjTranspose_AV_mul_AV` from the square case.
    Note: A*V is m×n, so (A*V)ᴴ*(A*V) is n×n. -/
theorem conjTranspose_AV_mul_AV_rectangular (A : Matrix m n ℂ) :
    let V : Matrix n n ℂ := rightUnitary A
    let eig := (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues
    (A * V)ᴴ * (A * V) = diagonal (Complex.ofReal ∘ eig) := by
  intro V eig
  -- The proof follows the same structure as the square case
  rw [conjTranspose_mul]
  -- Vᴴ * Aᴴ * (A * V) = Vᴴ * (Aᴴ * A) * V
  have h_assoc : Vᴴ * Aᴴ * (A * V) = Vᴴ * (Aᴴ * A) * V := by
    simp only [Matrix.mul_assoc]
  rw [h_assoc]
  -- Apply spectral theorem: Aᴴ * A = V * diag(eig) * Vᴴ
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

/-- Squared norm of column j of A*V equals σⱼ² (eigenvalue of AᴴA).

    This is the rectangular analogue of `AV_column_norm_sq` from the square case. -/
lemma AV_column_norm_sq_rectangular (A : Matrix m n ℂ) (j : n) :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    ∑ i, star (AV i j) * AV i j =
      Complex.ofReal ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j) := by
  intro V AV
  have h_diag := conjTranspose_AV_mul_AV_rectangular A
  simp only at h_diag
  -- (AVᴴ * AV)ⱼⱼ = ∑ᵢ star(AV i j) * (AV i j)
  have h_entry : (AVᴴ * AV) j j = ∑ i, star (AV i j) * AV i j := by
    simp only [conjTranspose_apply, mul_apply]
  rw [← h_entry, h_diag, diagonal_apply_eq, Function.comp_apply]

/-- Columns of A*V are orthogonal (rectangular case).
    For j ≠ j', the inner product of columns j and j' is 0. -/
lemma AV_columns_orthogonal_rectangular (A : Matrix m n ℂ) (j j' : n) (hjj' : j ≠ j') :
    let V : Matrix n n ℂ := rightUnitary A
    let AV := A * V
    ∑ i, star (AV i j) * AV i j' = 0 := by
  intro V AV
  have h_diag := conjTranspose_AV_mul_AV_rectangular A
  simp only at h_diag
  have h_entry : (AVᴴ * AV) j j' = ∑ i, star (AV i j) * AV i j' := by
    simp only [conjTranspose_apply, mul_apply]
  rw [← h_entry, h_diag, diagonal_apply, if_neg hjj']

/-! #### Left Singular Vectors for Rectangular Matrices

For rectangular m×n matrix A with singular value σⱼ ≠ 0, the j-th left singular vector is:
  uⱼ = (1/σⱼ) · (column j of A*V)

This is an m-dimensional vector (unlike the square case which gives n-dimensional).
The vectors are orthonormal: ⟨uᵢ, uⱼ⟩ = δᵢⱼ for all i, j with σᵢ, σⱼ ≠ 0.
-/

/-- Helper: convert eigenvalue of AᴴA to singular value.
    For rectangular matrices, we use `eigenvalues j` directly (indexed by the matrix column type n)
    rather than `eigenvalues₀` to avoid bijection mismatch issues between `equivFin` and
    `equivOfCardEq`. The `eigenvalues_nonneg` lemma applies directly to this definition. -/
noncomputable def singularValueFromEigenvalue (A : Matrix m n ℂ) (j : n) : ℝ :=
  Real.sqrt ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j)

set_option linter.unusedSectionVars false in
/-- Relates the Fin-indexed `singularValues` to the n-indexed `singularValueFromEigenvalue`.

Since both `singularValues` and `singularValueFromEigenvalue` use eigenvalues of Aᴴ*A,
and we use `eigenvaluesBijection` (same as `equivOfCardEq.symm`) for indexing,
the equality follows from the definition of `eigenvalues` in Mathlib. -/
lemma singularValues_eq_singularValueFromEigenvalue (A : Matrix m n ℂ) (j : n)
    (h_in_min : (eigenvaluesBijection n j).val < min (Fintype.card m) (Fintype.card n)) :
    singularValues A ⟨(eigenvaluesBijection n j).val, h_in_min⟩ = singularValueFromEigenvalue A j := by
  -- After architectural change: both singularValues and singularValueFromEigenvalue use Aᴴ*A
  -- Since eigenvaluesBijection = equivFin and eigenvalues uses equivOfCardEq.symm bijection,
  -- we need to bridge via our equivFin_eq_equivOfCardEq_symm lemma
  simp only [singularValues, singularValueFromEigenvalue]
  congr 1


/-- The j-th left singular vector for rectangular A (when σⱼ ≠ 0).
    Output type is m → ℂ (m-dimensional vector).

    Definition: uⱼ = (1/σⱼ) · (column j of A*V) -/
noncomputable def leftSingularVectorNonzero_rectangular (A : Matrix m n ℂ) (j : n)
    (_ : singularValueFromEigenvalue A j ≠ 0) : m → ℂ :=
  let AV := A * (rightUnitary A : Matrix n n ℂ)
  fun i => (Complex.ofReal (singularValueFromEigenvalue A j))⁻¹ * AV i j

/-- The squared norm of a left singular vector is 1 (rectangular case).
    Uses: ‖uⱼ‖² = (1/σⱼ)² · ‖(A*V)[:,j]‖² = (1/σⱼ)² · σⱼ² = 1 -/
theorem leftSingularVectorNonzero_rectangular_inner_self (A : Matrix m n ℂ) (j : n)
    (hj : singularValueFromEigenvalue A j ≠ 0) :
    ∑ i, star (leftSingularVectorNonzero_rectangular A j hj i) *
             (leftSingularVectorNonzero_rectangular A j hj i) = 1 := by
  unfold leftSingularVectorNonzero_rectangular
  have h_norm := AV_column_norm_sq_rectangular A j
  simp only [star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  -- Factor out (σ⁻¹)² from the sum
  have factor : ∀ i : m,
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
        (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) *
        (((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
         (A * (rightUnitary A : Matrix n n ℂ)) i j) =
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
       ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
        ((starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) *
         (A * (rightUnitary A : Matrix n n ℂ)) i j) := by
    intro i; ring
  conv_lhs => arg 2; ext i; rw [factor i]
  rw [← Finset.mul_sum]
  have h_star_eq : ∀ i : m, (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) =
      star ((A * (rightUnitary A : Matrix n n ℂ)) i j) := fun _ => rfl
  simp_rw [h_star_eq]
  -- The sum is now ∑ᵢ star(AV i j) * (AV i j), which equals the eigenvalue
  simp only at h_norm
  -- Need to show the eigenvalue equals σ²
  have h_eig_eq_sq : Complex.ofReal ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j) =
      Complex.ofReal ((singularValueFromEigenvalue A j) ^ 2) := by
    unfold singularValueFromEigenvalue
    congr 1
    rw [Real.sq_sqrt]
    exact (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg j
  rw [h_norm, h_eig_eq_sq]
  -- Now: (σ⁻¹)² · σ² = 1
  have hj' : (Complex.ofReal (singularValueFromEigenvalue A j) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hj
  have h_sq_eq : (Complex.ofReal ((singularValueFromEigenvalue A j) ^ 2) : ℂ) =
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ)) *
       ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ)) := by
    rw [sq, Complex.ofReal_mul]
  rw [h_sq_eq]
  field_simp

/-- Left singular vectors for different indices are orthogonal (rectangular case).
    For j ≠ j' with both σⱼ, σⱼ' ≠ 0, we have ⟨uⱼ, uⱼ'⟩ = 0. -/
theorem leftSingularVectorNonzero_rectangular_orthogonal (A : Matrix m n ℂ) (j j' : n)
    (hj : singularValueFromEigenvalue A j ≠ 0) (hj' : singularValueFromEigenvalue A j' ≠ 0)
    (hjj' : j ≠ j') :
    ∑ i, star (leftSingularVectorNonzero_rectangular A j hj i) *
             (leftSingularVectorNonzero_rectangular A j' hj' i) = 0 := by
  unfold leftSingularVectorNonzero_rectangular
  have h_orth := AV_columns_orthogonal_rectangular A j j' hjj'
  simp only [star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]
  have factor : ∀ i : m,
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
        (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) *
        (((Complex.ofReal (singularValueFromEigenvalue A j') : ℂ))⁻¹ *
         (A * (rightUnitary A : Matrix n n ℂ)) i j') =
      ((Complex.ofReal (singularValueFromEigenvalue A j) : ℂ))⁻¹ *
       ((Complex.ofReal (singularValueFromEigenvalue A j') : ℂ))⁻¹ *
        ((starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) *
         (A * (rightUnitary A : Matrix n n ℂ)) i j') := by
    intro i; ring
  conv_lhs => arg 2; ext i; rw [factor i]
  rw [← Finset.mul_sum]
  have h_star_eq : ∀ i : m, (starRingEnd ℂ) ((A * (rightUnitary A : Matrix n n ℂ)) i j) =
      star ((A * (rightUnitary A : Matrix n n ℂ)) i j) := fun _ => rfl
  simp_rw [h_star_eq, h_orth, mul_zero]


end Matrix.SVD.Rectangular
end Hagi.External.Flywheel
