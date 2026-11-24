import Hagi.Contracts.GradientBottleneck
import Hagi.External.Flywheel.SVDRectangularOrdering

set_option relaxedAutoImplicit false

/-!
# Rectangular spectral identification bridge

`GradientBottleneck` embedded rectangular carriers into the square
Flywheel SVD via
the row-selector `selP inj` and proved the Eckart-Young lower bound
for the EMBEDDED spectrum, deferring its identification with the
rectangular `Matrix.SVD.Rectangular.singularValues` spectrum;
this file proves the identification.

Key observation (`selP_conjTranspose_mul_selP`): for injective
`inj`, the selector `selP inj` has orthonormal columns, so the
embedded matrix `selP inj * A` has the SAME Gram matrix as `A`:

  `(selP inj * A)ᴴ * (selP inj * A) = Aᴴ * A`

Both spectra are square roots of `eigenvalues₀` of one and the same
Hermitian Gram matrix, hence:

* `embedded_eigenvalues₀_eq` — the embedded Gram eigenvalues equal
  the rectangular Gram eigenvalues pointwise;
* `embedded_singularValues_eq_rect` — the embedded square
  `Matrix.SVD.singularValues₀` agrees with
  `Matrix.SVD.Rectangular.singularValues` on the `min`-index range;
* `tail_sum_sq_truncatedSingularValues_tail_eq` — the tail
  sum over the embedded spectrum equals the sum over the TRUE
  rectangular tail `rectangularTail`;
* `eckart_young_lower_bound_rect_true_tail` — the rectangular
  Eckart-Young lower bound restated against the rectangular
  spectrum itself (the identification);
* `gradient_bottleneck_bound_rect_true_tail` — the consumer
  instantiation for `logitGradRectM`.

The rank-head implication, previously only premise-form downstream,
is upgraded to a theorem:

* `singularValues_pos_of_lt_rank_rect` — `k.val < A.rank` forces
  the `k`-th rectangular singular value to be strictly positive
  (antitone spectrum + `rank_eq_card_nonzero_singularValues_rect`).

Mathlib note: `Mathlib.Analysis.InnerProductSpace.SingularValues`
offers a `LinearMap.singularValues` API with the analogous facts,
but no matrix ↔ `LinearMap` bridge is pinned in this repository;
this file stays in the matrix/`eigenvalues₀` carrier.
-/

open Matrix Finset
open Hagi.External.Flywheel
open scoped ComplexOrder

open Hagi.External.Flywheel.Matrix.FrobeniusNorm in
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

namespace Hagi.Contracts.GradientBottleneckIdentification

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open Hagi.Contracts.GradientBottleneck (selP)

/-! ### Orthonormality of the row-selector and the Gram bridge -/

set_option linter.unusedSectionVars false in
/-- The row-selector `selP inj` has orthonormal columns whenever
`inj` is injective: `(selP inj)ᴴ * selP inj = 1`. This is the
observation the whole rectangular spectral bridge rests on. -/
theorem selP_conjTranspose_mul_selP (inj : m → n) (hinj : Function.Injective inj) :
    (selP inj)ᴴ * selP inj = 1 := by
  ext i i'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, selP, Matrix.of_apply,
    Matrix.one_apply]
  by_cases h : inj i = inj i'
  · have hii : i = i' := hinj h
    subst hii
    simp [mul_ite]
  · have hne : i ≠ i' := fun hc => h (by rw [hc])
    have hz : ∀ j ∈ (Finset.univ : Finset n),
        star ((if inj i = j then (1:ℂ) else 0)) * (if inj i' = j then 1 else 0) = 0 := by
      intro j _
      by_cases h1 : inj i = j
      · have h2 : ¬ inj i' = j := fun hc => h (h1.trans hc.symm)
        simp [h1, h2]
      · simp [h1]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    simp [hne]

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- Gram bridge: the embedded square matrix `selP inj * A` has the
same Gram matrix as the rectangular `A`:
`(selP inj * A)ᴴ * (selP inj * A) = Aᴴ * A`. -/
theorem embedded_gram_eq (inj : m → n) (hinj : Function.Injective inj)
    (A : Matrix m n ℂ) :
    (selP inj * A)ᴴ * (selP inj * A) = Aᴴ * A := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (selP inj)ᴴ (selP inj) A,
    selP_conjTranspose_mul_selP inj hinj, Matrix.one_mul]

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- Embedded Gram eigenvalues: `eigenvalues₀` of the embedded Gram
matrix `(selP inj * A)ᴴ * (selP inj * A)` agree pointwise with
`eigenvalues₀` of `Aᴴ * A` (both index the same Hermitian matrix by
`embedded_gram_eq`; `Matrix.IsHermitian` is a `Prop`, so the two
proof terms are definitionally equal after rewriting). -/
theorem embedded_eigenvalues₀_eq (inj : m → n) (hinj : Function.Injective inj)
    (A : Matrix m n ℂ) (j : Fin (Fintype.card n)) :
    (posSemidef_conjTranspose_mul_self (selP inj * A)).isHermitian.eigenvalues₀ j =
      (posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ j := by
  have hgram : (selP inj * A)ᴴ * (selP inj * A) = Aᴴ * A :=
    embedded_gram_eq inj hinj A
  -- congruence route: equal matrices have equal charpolys, and
  -- `sort_roots_charpoly_eq_eigenvalues₀` determines the sorted
  -- eigenvalue list from the charpoly (pinned Mathlib)
  have hcp : ((selP inj * A)ᴴ * (selP inj * A)).charpoly = (Aᴴ * A).charpoly :=
    congrArg Matrix.charpoly hgram
  have hlist : List.ofFn
        ((posSemidef_conjTranspose_mul_self (selP inj * A)).isHermitian.eigenvalues₀)
      = List.ofFn ((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀) := by
    rw [← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀ _,
        ← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀ _, hcp]
  exact congrFun (List.ofFn_inj.mp hlist) j

/-! ### Spectral identification -/

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **Embedded spectrum = rectangular spectrum**: on the `min`
index range, the square `Matrix.SVD.singularValues₀` of the
embedded matrix `selP inj * A` agrees with the rectangular
`Matrix.SVD.Rectangular.singularValues` of `A`. This is the
identification `GradientBottleneck` defers. -/
theorem embedded_singularValues_eq_rect (inj : m → n) (hinj : Function.Injective inj)
    (A : Matrix m n ℂ) (k : Fin (min (Fintype.card m) (Fintype.card n))) :
    Matrix.SVD.singularValues₀ (selP inj * A)
        (Fin.castLE (Nat.min_le_right _ _) k) =
      Matrix.SVD.Rectangular.singularValues A k := by
  unfold Matrix.SVD.singularValues₀ Matrix.SVD.Rectangular.singularValues
  rw [embedded_eigenvalues₀_eq inj hinj A
    (Fin.castLE (Nat.min_le_right _ _) k)]

/-! ### Rank-head implication -/

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **Rank-head positivity**: if `k.val < A.rank`, the `k`-th
rectangular singular value of `A` is strictly positive. Upgrades
the premise-form rank-head implication to a theorem: a rank head
beyond `k` forces the spectrum head beyond `k` to be nonzero (the
spectrum is antitone, so a zero at index `k` would zero the whole
tail, bounding `rank = #{nonzero singular values}` by `k.val`). -/
theorem singularValues_pos_of_lt_rank_rect (A : Matrix m n ℂ)
    (k : Fin (min (Fintype.card m) (Fintype.card n))) (hk : k.val < A.rank) :
    0 < Matrix.SVD.Rectangular.singularValues A k := by
  by_contra hcon
  push_neg at hcon
  have hσ := Matrix.SVD.Rectangular.singularValues_antitone A
  -- a zero at k zeroes the whole tail (antitone + nonneg)
  have htail : ∀ i : Fin (min (Fintype.card m) (Fintype.card n)),
      k ≤ i → Matrix.SVD.Rectangular.singularValues A i = 0 := by
    intro i hi
    exact le_antisymm
      (le_trans (hσ hi) hcon)
      (Matrix.SVD.Rectangular.singularValues_nonneg A i)
  -- so nonzero singular values live below k: card ≤ k.val, contradicting rank
  classical
  have hsub : ∀ i : Fin (min (Fintype.card m) (Fintype.card n)),
      Matrix.SVD.Rectangular.singularValues A i ≠ 0 → i.val < k.val := by
    intro i hi
    by_contra hge
    push_neg at hge
    exact hi (htail i hge)
  have hcard : Fintype.card {i : Fin (min (Fintype.card m) (Fintype.card n)) //
      Matrix.SVD.Rectangular.singularValues A i ≠ 0} ≤ k.val := by
    classical
    have hf : Function.Injective
        (fun (i : {i : Fin (min (Fintype.card m) (Fintype.card n)) //
            Matrix.SVD.Rectangular.singularValues A i ≠ 0}) =>
          (⟨i.val.val, hsub i.val i.property⟩ : Fin k.val)) := by
      intro a b hab
      have h1 : a.val.val = b.val.val :=
        congrArg (fun x : Fin k.val => x.val) hab
      exact Subtype.ext (Fin.ext h1)
    have hle := Fintype.card_le_of_injective _ hf
    rwa [Fintype.card_fin] at hle
  have hrank := Matrix.SVD.Rectangular.rank_eq_card_nonzero_singularValues_rect A
  omega

/-! ### Tail identification -/

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- The TRUE rectangular tail: singular values of the rectangular
`A` at indices `≥ k`, zero below (`Fin (min #m #n)`-indexed). -/
noncomputable def rectangularTail (A : Matrix m n ℂ) (k : ℕ) :
    Fin (min (Fintype.card m) (Fintype.card n)) → ℝ :=
  fun i => if k ≤ i.val then Matrix.SVD.Rectangular.singularValues A i else 0

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **Tail-sum identification**: the tail sum — squares of
`truncatedSingularValues_tail` of the EMBEDDED matrix `selP inj *
A` — equals the sum of squares of the TRUE rectangular tail
`rectangularTail`. Indices at or beyond `min #m #n` contribute
nothing (the embedded Gram eigenvalues vanish there by
`Matrix.SVD.Rectangular.eigenvalues₀_zero_beyond_min` plus the
Gram bridge), and the remaining indices carry the rectangular
spectrum by `embedded_singularValues_eq_rect`. -/
theorem tail_sum_sq_truncatedSingularValues_tail_eq (inj : m → n)
    (hinj : Function.Injective inj) (A : Matrix m n ℂ) (k : ℕ) :
    ∑ j : n, (Hagi.External.Flywheel.Matrix.SVD.truncatedSingularValues_tail
        (selP inj * A) k j)^2 =
      ∑ i, (rectangularTail A k i)^2 := by
  classical
  -- Step 1: reindex the embedded sum from `n` to `Fin (card n)`
  set e : n ≃ Fin (Fintype.card n) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm
  have hstep1 : ∑ j : n, (Hagi.External.Flywheel.Matrix.SVD.truncatedSingularValues_tail
      (selP inj * A) k j)^2
      = ∑ j : Fin (Fintype.card n),
          (if k ≤ j.val then Matrix.SVD.singularValues₀ (selP inj * A) j else 0)^2 :=
    Finset.sum_equiv e (fun _ => by simp [Finset.mem_univ]) (fun _ _ => rfl)
  rw [hstep1]
  -- Step 2: split at min
  have h_split : ∑ j : Fin (Fintype.card n),
      (if k ≤ j.val then Matrix.SVD.singularValues₀ (selP inj * A) j else 0)^2
      = (∑ j ∈ Finset.univ.filter
            (fun j : Fin (Fintype.card n) => j.val < min (Fintype.card m) (Fintype.card n)),
          (if k ≤ j.val then Matrix.SVD.singularValues₀ (selP inj * A) j else 0)^2)
        + (∑ j ∈ Finset.univ.filter
            (fun j : Fin (Fintype.card n) => j.val ≥ min (Fintype.card m) (Fintype.card n)),
          (if k ≤ j.val then Matrix.SVD.singularValues₀ (selP inj * A) j else 0)^2) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun j : Fin (Fintype.card n) => j.val < min (Fintype.card m) (Fintype.card n))]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, ge_iff_le,
      le_iff_lt_or_eq]
  rw [h_split]
  -- Step 4: the ≥ min part is zero
  have h_tail_zero : (∑ j ∈ Finset.univ.filter
      (fun j : Fin (Fintype.card n) => j.val ≥ min (Fintype.card m) (Fintype.card n)),
    (if k ≤ j.val then Matrix.SVD.singularValues₀ (selP inj * A) j else 0)^2) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have h0 : Matrix.SVD.singularValues₀ (selP inj * A) j = 0 := by
      unfold Matrix.SVD.singularValues₀
      have h := Matrix.SVD.Rectangular.eigenvalues₀_zero_beyond_min A j hj
      rw [← embedded_eigenvalues₀_eq inj hinj A j] at h
      rw [h, Real.sqrt_zero]
    rw [h0]
    simp
  rw [h_tail_zero, add_zero]
  -- Step 5: bijection from filter (< min) to Fin (min)
  symm
  have hidcast : ∀ k' : Fin (min (Fintype.card m) (Fintype.card n)),
      Matrix.SVD.singularValues₀ (selP inj * A)
          (Fin.castLE (Nat.min_le_right _ _) k') =
        Matrix.SVD.Rectangular.singularValues A k' :=
    fun k' => embedded_singularValues_eq_rect inj hinj A k'
  refine Finset.sum_bij'
    (fun k' _ => Fin.castLE (Nat.min_le_right _ _) k')
    (fun j hj => ⟨j.val, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj⟩) ?_ ?_ ?_ ?_ ?_
  · intro k' _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k'.isLt
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_univ _
  · intro k' _
    ext; simp
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    ext; simp
  · intro k' _
    unfold rectangularTail
    simp only [hidcast k']
    congr 1

/-! ### Eckart-Young with the true rectangular tail -/

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **Rectangular Eckart-Young lower bound, true-tail form**: any
rectangular `B` with `B.rank ≤ k` leaves Frobenius error at least
the squared tail of the RECTANGULAR spectrum of `A` itself — the
 `eckart_young_lower_bound_rect` bound with its tail identified
via `tail_sum_sq_truncatedSingularValues_tail_eq`. -/
theorem eckart_young_lower_bound_rect_true_tail (inj : m → n)
    (hinj : Function.Injective inj) (A B : Matrix m n ℂ) (k : ℕ)
    (hB : B.rank ≤ k) :
    ∑ i, (rectangularTail A k i)^2 ≤ ‖A - B‖^2 := by
  rw [← tail_sum_sq_truncatedSingularValues_tail_eq inj hinj A k]
  exact Hagi.Contracts.GradientBottleneck.eckart_young_lower_bound_rect inj hinj A B k hB

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **Rectangular gradient bottleneck, true-tail form**
`gradient_bottleneck_bound_rect` with the tail identified as the
TRUE rectangular spectrum tail of the (un-embedded) logit gradient
matrix. Premise-form `hΔ` unchanged (the rank-`D` head derivation
stays deferred); what changes is only the spectral
identification of the tail. -/
theorem gradient_bottleneck_bound_rect_true_tail (ctxInj : m → n)
    (hinj : Function.Injective ctxInj) (z N : m → n → ℝ) (k : ℕ)
    (Δ : Matrix m n ℂ) (hΔ : Δ.rank ≤ k) :
    ∑ i, (rectangularTail
            (Matrix.of fun c v =>
              (Hagi.Contracts.LogitGrad.logitGrad z N c v : ℂ)) k i)^2
      ≤ ‖(Matrix.of fun c v =>
            (Hagi.Contracts.LogitGrad.logitGrad z N c v : ℂ)) - Δ‖^2 :=
  eckart_young_lower_bound_rect_true_tail ctxInj hinj _ _ k hΔ

end Hagi.Contracts.GradientBottleneckIdentification
