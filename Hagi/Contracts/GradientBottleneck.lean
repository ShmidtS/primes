/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.LogitGrad
import Hagi.External.Flywheel.EckartYoungLower
import Hagi.Architecture.LiveDelta

set_option relaxedAutoImplicit false

/-!
# Gradient bottleneck bound via Eckart–Young

`gradient_bottleneck_bound`: any achievable logit update `Δ` whose
matrix has rank at most `k` leaves Frobenius residual at least the
squared tail of the singular values of the logit-gradient matrix
beyond `k`. In the paper's usage `k = 2D` for a rank-`D` head, so the
residual retains the tail beyond `2D`.

Honesty notes (premise-form statement):

* The achievable-update set is formalized as the premise `hΔ : Δ.rank
  ≤ k`. The head-derivation — a rank-`D` head forces achievable logit
  updates to have rank at most `2D` — is DEFERRED, as is the
  rectangular contexts-×-vocabulary carrier: `logitGradM` is the
  square `n × n` complex matrix view (real entries coerced) required
  by the Flywheel SVD API.
* The bound can be vacuous when `k ≥ n` (empty tail); the statement
  remains true.

The entire content is the definitions plus the rank premise: the
theorem is a direct corollary of `eckart_young_lower_bound` (C226)
applied to `logitGradM`. The row facts live in
`Hagi.Contracts.LogitGrad`.
-/

open scoped BigOperators

namespace Hagi.Contracts.GradientBottleneck

open Hagi.External.Flywheel.Matrix.FrobeniusNorm in
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Matrix view of the logit gradient over contexts and vocabulary
both indexed by `n` (square complex carrier required by the Flywheel
SVD API; real entries coerced). -/
noncomputable def logitGradM (z N : n → n → ℝ) : Matrix n n ℂ :=
  Matrix.of fun c v => (Hagi.Contracts.LogitGrad.logitGrad z N c v : ℂ)

/-- Gradient bottleneck bound: any achievable logit update `Δ` with
`Δ.rank ≤ k` leaves residual at least the squared singular-value tail
of `logitGradM z N` beyond `k`. Direct corollary of
`eckart_young_lower_bound`; see the module docstring for the
premise-form honesty notes. -/
theorem gradient_bottleneck_bound (z N : n → n → ℝ) (k : ℕ)
    (Δ : Matrix n n ℂ) (hΔ : Δ.rank ≤ k) :
    ∑ i, (Hagi.External.Flywheel.Matrix.SVD.truncatedSingularValues_tail
            (logitGradM z N) k i)^2
      ≤ ‖logitGradM z N - Δ‖^2 :=
  Hagi.External.Flywheel.Matrix.FrobeniusNorm.eckart_young_lower_bound
    (logitGradM z N) k Δ hΔ


/-!
## Rectangular extension (C232)

The Flywheel truncated-SVD / Eckart–Young machinery is SQUARE
(`Matrix n n ℂ`; only `Matrix.SVD.singularValues` has a rectangular
definition, with no truncated/EY layer on top). Rectangular
contexts-×-vocabulary gradients are handled by a row-embedding
reduction into the square carrier:

* `selP inj` — the n×m row-selector (1 at `inj i`), `coSelQ` its
  m×n co-selector with `coSelQ_mul_selP : Q * P = 1` (needs
  injectivity).
* `emb_rank_eq` — embedding preserves rank exactly
  (`Q * (P * A) = A` + `rank_mul_le_left/right`).
* `frobenius_selP_eq` — embedding is a Frobenius isometry
  (rows outside `Set.range inj` are zero rows; the row at `inj i` is
  row `i` of `C`; `Finset.sum_image` redistributes).
* `eckart_young_lower_bound_rect` — MAIN: the square
  `eckart_young_lower_bound` transfers verbatim to the rectangular
  carrier: any `B : Matrix m n ℂ` with `B.rank ≤ k` leaves
  `‖A - B‖^2` at least the squared tail (beyond `k`) of the
  embedded singular values.
* `gradient_bottleneck_bound_rect` — the rectangular gradient
  bottleneck (premise-form `hΔ : Δ.rank ≤ k`, same honesty pattern
  as the square `gradient_bottleneck_bound`).

Honesty boundary (documented deferral): the tail is the tail of the
EMBEDDED square matrix; its identification with the rectangular
`Matrix.SVD.singularValues` spectrum (defined for `Matrix m n ℂ` in
Flywheel `SVD.lean` but without truncated machinery) is deferred —
it would require re-running the square SVD construction on the
padded matrix. The bound is non-vacuous: at `k = 0` the tail sum
equals `‖A‖^2` and the statement reduces to `‖A‖^2 ≤ ‖A - B‖^2` for
rank-zero `B`.

* `factor_update_rank_le` — `rank(A * Bᵀ) ≤ card r` for low-rank
  factor updates `A : m×r`, `B : n×r`; the twin of the existing
  `Hagi.Architecture.block_rank_le` (which covers the `Aᵀ * B`
  orientation for LiveDelta blocks).
-/

section Rectangular

open Matrix Finset

open Hagi.External.Flywheel.Matrix.FrobeniusNorm in
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Row-selector matrix: `selP inj` has a 1 in position `(inj i, i)`. -/
def selP (inj : m → n) : Matrix n m ℂ :=
  Matrix.of fun j i => if inj i = j then 1 else 0

/-- Co-selector matrix: `coSelQ inj` has a 1 in position `(i, inj i)`. -/
def coSelQ (inj : m → n) : Matrix m n ℂ :=
  Matrix.of fun i j => if inj i = j then 1 else 0

/-- The co-selector is a left inverse of the row-selector. -/
theorem coSelQ_mul_selP (inj : m → n) (hinj : Function.Injective inj) :
    coSelQ inj * selP inj = 1 := by
  ext i i'
  simp only [Matrix.mul_apply, selP, coSelQ, Matrix.of_apply, Matrix.one_apply]
  by_cases h : inj i = inj i'
  · have hii : i = i' := hinj h
    subst hii
    simp [mul_ite]
  · have hne : i ≠ i' := fun hc => h (by rw [hc])
    have hz : ∀ j ∈ (Finset.univ : Finset n),
        (if inj i = j then (1:ℂ) else 0) * (if inj i' = j then 1 else 0) = 0 := by
      intro j _
      by_cases h1 : inj i = j
      · have h2 : ¬ inj i' = j := fun hc => h (h1.trans hc.symm)
        simp [h1, h2]
      · simp [h1]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    simp [hne]

/-- Row-embedding preserves rank exactly. -/
theorem emb_rank_eq (inj : m → n) (hinj : Function.Injective inj)
    (A : Matrix m n ℂ) : (selP inj * A).rank = A.rank := by
  have hQA : coSelQ inj * (selP inj * A) = A := by
    rw [← Matrix.mul_assoc, coSelQ_mul_selP inj hinj, Matrix.one_mul]
  have h1 : (selP inj * A).rank ≤ A.rank := rank_mul_le_right _ _
  have h2 : A.rank ≤ (selP inj * A).rank := by
    have hh := rank_mul_le_right (coSelQ inj) (selP inj * A)
    rw [hQA] at hh
    exact hh
  exact le_antisymm h1 h2

/-- Row-embedding is a Frobenius isometry: `‖selP inj * C‖ = ‖C‖`.
Rows of `selP inj * C` outside the image of `inj` vanish; the row at
`inj i` is row `i` of `C`; `Finset.sum_image` redistributes the row
sums. -/
theorem frobenius_selP_eq (inj : m → n) (hinj : Function.Injective inj)
    (C : Matrix m n ℂ) : ‖selP inj * C‖ = ‖C‖ := by
  have hrowEq : ∀ (i : m) (j' : n),
      (selP inj * C) (inj i) j' = C i j' := by
    intro i j'
    simp only [Matrix.mul_apply, selP, Matrix.of_apply]
    rw [Finset.sum_eq_single i
      (fun i' _ hi' => by
        rw [if_neg (fun hc => hi' (hinj hc)), zero_mul])
      (fun hn => absurd (Finset.mem_univ i) hn)]
    simp
  have hrowZero : ∀ j : n, (∀ i, ¬ inj i = j) →
      ∑ j', ‖(selP inj * C) j j'‖ ^ (2 : ℝ) = 0 := by
    intro j hj
    refine Finset.sum_eq_zero fun j' _ => ?_
    have hval : (selP inj * C) j j' = 0 := by
      simp only [Matrix.mul_apply, selP, Matrix.of_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [hj i]
    rw [hval]
    simp
  have hsumImg : (∑ j ∈ Finset.univ.image inj, ∑ j', ‖(selP inj * C) j j'‖ ^ (2 : ℝ))
      = ∑ i ∈ (Finset.univ : Finset m), ∑ j', ‖C i j'‖ ^ (2 : ℝ) := by
    rw [Finset.sum_image hinj.injOn]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j' _ => by rw [hrowEq i j']
  have hkey : (∑ j ∈ (Finset.univ : Finset n), ∑ j', ‖(selP inj * C) j j'‖ ^ (2 : ℝ))
      = ∑ i ∈ (Finset.univ : Finset m), ∑ j', ‖C i j'‖ ^ (2 : ℝ) := by
    calc ∑ j ∈ (Finset.univ : Finset n), ∑ j', ‖(selP inj * C) j j'‖ ^ (2 : ℝ)
        = ∑ j ∈ Finset.univ.image inj, ∑ j', ‖(selP inj * C) j j'‖ ^ (2 : ℝ) := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro j _ hj
          exact hrowZero j (fun i hi => hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩))
      _ = ∑ i ∈ (Finset.univ : Finset m), ∑ j', ‖C i j'‖ ^ (2 : ℝ) := hsumImg
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  exact congrArg (fun t : ℝ => t ^ ((1:ℝ)/2)) hkey

/-- **Rectangular Eckart–Young lower bound**: any rectangular `B`
with `B.rank ≤ k` leaves Frobenius error at least the squared tail of
the embedded singular values of `A` beyond `k`. Direct transfer of
the square `eckart_young_lower_bound` through the isometric
row-embedding. -/
theorem eckart_young_lower_bound_rect (inj : m → n)
    (hinj : Function.Injective inj) (A B : Matrix m n ℂ) (k : ℕ)
    (hB : B.rank ≤ k) :
    ∑ j, (Hagi.External.Flywheel.Matrix.SVD.truncatedSingularValues_tail
            (selP inj * A) k j)^2
      ≤ ‖A - B‖^2 := by
  have hEmb : selP inj * A - selP inj * B = selP inj * (A - B) := by
    rw [← Matrix.mul_sub]
  have hrB : (selP inj * B).rank ≤ k := by
    rw [emb_rank_eq inj hinj B]
    exact hB
  have h := Hagi.External.Flywheel.Matrix.FrobeniusNorm.eckart_young_lower_bound
    (selP inj * A) k (selP inj * B) hrB
  rw [hEmb, frobenius_selP_eq inj hinj (A - B)] at h
  exact h

/-- Rectangular matrix view of the logit gradient: contexts indexed
by `m`, vocabulary by `n`, embedded into the square `n × n` carrier
via an injection `ctxInj`. -/
noncomputable def logitGradRectM (ctxInj : m → n) (z : m → n → ℝ)
    (N : m → n → ℝ) : Matrix n n ℂ :=
  selP ctxInj * (Matrix.of fun c v =>
    (Hagi.Contracts.LogitGrad.logitGrad (C := m) (V := n) z N c v : ℂ))

/-- **Rectangular gradient bottleneck bound**: any achievable logit
update `Δ` on the contexts-×-vocabulary carrier with `Δ.rank ≤ k`
leaves residual at least the squared embedded singular-value tail of
the logit gradient beyond `k`. Premise-form `hΔ`, mirroring the
square `gradient_bottleneck_bound`; the head rank-`D` ⇒ `k = 2D`
derivation remains deferred here as there. -/
theorem gradient_bottleneck_bound_rect (ctxInj : m → n)
    (hinj : Function.Injective ctxInj) (z N : m → n → ℝ) (k : ℕ)
    (Δ : Matrix m n ℂ) (hΔ : Δ.rank ≤ k) :
    ∑ j, (Hagi.External.Flywheel.Matrix.SVD.truncatedSingularValues_tail
            (logitGradRectM ctxInj z N) k j)^2
      ≤ ‖(Matrix.of fun c v =>
            (Hagi.Contracts.LogitGrad.logitGrad z N c v : ℂ)) - Δ‖^2 :=
  eckart_young_lower_bound_rect ctxInj hinj _ _ k hΔ

end Rectangular

section FactorRank

open Matrix

/-- Low-rank factor updates span at most `card r` directions:
`rank(A * Bᵀ) ≤ card r` for `A : m×r`, `B : n×r`. The twin of
`Hagi.Architecture.block_rank_le` (LiveDelta blocks, `Aᵀ * B`
orientation). -/
theorem factor_update_rank_le {r : Type*} [Fintype r]
    (A : Matrix m r ℝ) (B : Matrix n r ℝ) :
    (A * Bᵀ).rank ≤ Fintype.card r := by
  have h1 : (A * Bᵀ).rank ≤ Bᵀ.rank := rank_mul_le_right A Bᵀ
  have h2 : Bᵀ.rank ≤ Fintype.card r := by
    rw [rank_transpose]
    exact rank_le_card_width B
  exact le_trans h1 h2

end FactorRank

end Hagi.Contracts.GradientBottleneck

