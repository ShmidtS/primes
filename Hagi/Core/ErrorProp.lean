/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Telescopic error propagation of the sequential compression pass

The error of a sequential (telescopic) compression pass obeys the
affine recursion `δ_{l+1} = J_l δ_l + r_l`, folded by `propagate`.

* `propagate_bound` — if `‖J_l‖ ≤ α` and `‖r_l‖ ≤ ρ` for every
  layer, then `‖δ_L‖ ≤ α^L ‖δ₀‖ + ρ Σ_{i<L} αⁱ`.
* `propagate_bound_contractive` — at `α = 1` this degenerates to
  the plain sum `‖δ_L‖ ≤ ‖δ₀‖ + L ρ`.
* `propagate_sq_bound` — under a quadratic `α`-contraction
  hypothesis on each `J_l` and orthogonality of each fresh
  residual, the squared error satisfies
  `‖δ_L‖² ≤ α^(2L) ‖δ₀‖² + Σ_l w_l ρ_l²` with the layer weights
  `w_l = Π_{k>l} α_k²` given by `weightedResidual`.
-/

namespace Hagi.Core

open scoped Matrix Matrix.Norms.Operator

/-- One step of the telescopic recursion `δ_{l+1} = J_l δ_l + r_l`,
folded over the whole layer list: `propagate L δ₀` is the error vector
after running the sequential compression pass `L` starting from `δ₀`. -/
def propagate {n : Type*} [Fintype n] [DecidableEq n]
    (L : List (Matrix n n ℝ × (n → ℝ))) (δ₀ : n → ℝ) : n → ℝ :=
  L.foldl (fun δ p => p.1 *ᵥ δ + p.2) δ₀

/-- The pass over `p :: L` starting from `δ₀` is the pass over `L`
starting from one affine step `J_p δ₀ + r_p`: this is the telescoping
principle itself. -/
theorem propagate_cons {n : Type*} [Fintype n] [DecidableEq n]
    (p : Matrix n n ℝ × (n → ℝ)) (L : List (Matrix n n ℝ × (n → ℝ)))
    (δ₀ : n → ℝ) :
    propagate (p :: L) δ₀ = propagate L (p.1 *ᵥ δ₀ + p.2) := rfl

/-- If `‖p.1‖ ≤ α` (operator norm) and `‖p.2‖ ≤ ρ` for every layer
`p` of `L`, then `‖propagate L δ₀‖ ≤ α ^ L.length * ‖δ₀‖ +
(∑ i ∈ Finset.range L.length, α ^ i) * ρ`. -/
theorem propagate_bound {n : Type*} [Fintype n] [DecidableEq n] (α ρ : ℝ)
    (hα : 0 ≤ α) (L : List (Matrix n n ℝ × (n → ℝ))) (δ₀ : n → ℝ)
    (hJ : ∀ p ∈ L, ‖p.1‖ ≤ α) (hr : ∀ p ∈ L, ‖p.2‖ ≤ ρ) :
    ‖propagate L δ₀‖ ≤ α ^ L.length * ‖δ₀‖ +
      (∑ i ∈ Finset.range L.length, α ^ i) * ρ := by
  induction L generalizing δ₀ with
  | nil =>
    simp [propagate]
  | cons p L ih =>
    have hJL : ∀ q ∈ L, ‖q.1‖ ≤ α := fun q hq => hJ q (List.Mem.tail p hq)
    have hrL : ∀ q ∈ L, ‖q.2‖ ≤ ρ := fun q hq => hr q (List.Mem.tail p hq)
    have hpa : ‖p.1‖ ≤ α := hJ p (List.Mem.head L)
    have hpb : ‖p.2‖ ≤ ρ := hr p (List.Mem.head L)
    have key : ‖p.1 *ᵥ δ₀‖ ≤ α * ‖δ₀‖ :=
      (Matrix.linfty_opNorm_mulVec p.1 δ₀).trans
        (mul_le_mul_of_nonneg_right hpa (norm_nonneg δ₀))
    have hstep : ‖p.1 *ᵥ δ₀ + p.2‖ ≤ α * ‖δ₀‖ + ρ :=
      (norm_add_le _ _).trans (add_le_add key hpb)
    rw [propagate_cons]
    simp only [List.length_cons]
    refine le_trans (ih (p.1 *ᵥ δ₀ + p.2) hJL hrL) ?_
    refine le_trans
      (add_le_add (mul_le_mul_of_nonneg_left hstep (pow_nonneg hα _)) le_rfl) ?_
    rw [Finset.sum_range_succ, pow_succ]
    exact le_of_eq (by ring)

/-- If `‖p.1‖ ≤ 1` and `‖p.2‖ ≤ ρ` for every layer, then
`‖propagate L δ₀‖ ≤ ‖δ₀‖ + L.length * ρ`. -/
theorem propagate_bound_contractive {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : ℝ) (L : List (Matrix n n ℝ × (n → ℝ))) (δ₀ : n → ℝ)
    (hα : ∀ p ∈ L, ‖p.1‖ ≤ 1) (hr : ∀ p ∈ L, ‖p.2‖ ≤ ρ) :
    ‖propagate L δ₀‖ ≤ ‖δ₀‖ + L.length * ρ := by
    have h := propagate_bound (1 : ℝ) ρ zero_le_one L δ₀ hα hr
    have h2 : ∑ i ∈ Finset.range L.length, (1 : ℝ) ^ i = L.length := by
      simp
    rw [one_pow, h2, one_mul] at h
    exact h

/-! ## Second-moment (weighted) accumulation and the bit budget -/

section SecondMoment

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The weighted squared-residual budget of a compression pass:
the fresh squared residual of each layer damped by the squared
contractions `α²` of all later layers,
`weightedResidual α (p :: L) = α ^ (2 * L.length) * (p.2 ⬝ᵥ p.2) +
weightedResidual α L`. -/
def weightedResidual (α : ℝ) : List (Matrix n n ℝ × (n → ℝ)) → ℝ
  | [] => 0
  | p :: L => α ^ (2 * L.length) * (p.2 ⬝ᵥ p.2) + weightedResidual α L

/-- If every layer's Jacobian is a quadratic `α`-contraction
(`(J *ᵥ δ) ⬝ᵥ (J *ᵥ δ) ≤ α ^ 2 * (δ ⬝ᵥ δ)`) and every fresh residual
is orthogonal to the propagated error, then the squared error
satisfies `(propagate L δ₀) ⬝ᵥ (propagate L δ₀) ≤ α ^ (2 * L.length) *
(δ₀ ⬝ᵥ δ₀) + weightedResidual α L`. -/
theorem propagate_sq_bound (α : ℝ) (hα : 0 ≤ α)
    (L : List (Matrix n n ℝ × (n → ℝ))) (δ₀ : n → ℝ)
    (hJ : ∀ p ∈ L, ∀ δ, (p.1 *ᵥ δ) ⬝ᵥ (p.1 *ᵥ δ) ≤ α ^ 2 * (δ ⬝ᵥ δ))
    (horth : ∀ p ∈ L, ∀ δ, (p.1 *ᵥ δ) ⬝ᵥ p.2 = 0) :
    (propagate L δ₀) ⬝ᵥ (propagate L δ₀)
      ≤ α ^ (2 * L.length) * (δ₀ ⬝ᵥ δ₀) + weightedResidual α L := by
  induction L generalizing δ₀ with
  | nil =>
    simp [propagate, weightedResidual]
  | cons p L ih =>
    have hJL : ∀ q ∈ L, ∀ δ, (q.1 *ᵥ δ) ⬝ᵥ (q.1 *ᵥ δ) ≤ α ^ 2 * (δ ⬝ᵥ δ) :=
      fun q hq => hJ q (List.Mem.tail p hq)
    have horthL : ∀ q ∈ L, ∀ δ, (q.1 *ᵥ δ) ⬝ᵥ q.2 = 0 :=
      fun q hq => horth q (List.Mem.tail p hq)
    have hpJ : ∀ δ, (p.1 *ᵥ δ) ⬝ᵥ (p.1 *ᵥ δ) ≤ α ^ 2 * (δ ⬝ᵥ δ) :=
      hJ p (List.Mem.head L)
    have hporth : ∀ δ, (p.1 *ᵥ δ) ⬝ᵥ p.2 = 0 := horth p (List.Mem.head L)
    have hstep : (p.1 *ᵥ δ₀ + p.2) ⬝ᵥ (p.1 *ᵥ δ₀ + p.2)
        ≤ α ^ 2 * (δ₀ ⬝ᵥ δ₀) + p.2 ⬝ᵥ p.2 := by
      have hexp : (p.1 *ᵥ δ₀ + p.2) ⬝ᵥ (p.1 *ᵥ δ₀ + p.2)
          = (p.1 *ᵥ δ₀) ⬝ᵥ (p.1 *ᵥ δ₀) + 2 * ((p.1 *ᵥ δ₀) ⬝ᵥ p.2)
            + p.2 ⬝ᵥ p.2 := by
        simp only [dotProduct, Pi.add_apply]
        have h1 : ∀ i : n,
            ((p.1 *ᵥ δ₀) i + p.2 i) * ((p.1 *ᵥ δ₀) i + p.2 i)
              = (p.1 *ᵥ δ₀) i * ((p.1 *ᵥ δ₀) i)
                + 2 * ((p.1 *ᵥ δ₀) i * p.2 i) + p.2 i * p.2 i := fun _ => by ring
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hexp, hporth δ₀, mul_zero, add_zero]
      exact add_le_add_left (hpJ δ₀) _
    rw [propagate_cons]
    have ih1 := ih (p.1 *ᵥ δ₀ + p.2) hJL horthL
    refine le_trans ih1 ?_
    rw [show weightedResidual α (p :: L)
        = α ^ (2 * L.length) * (p.2 ⬝ᵥ p.2) + weightedResidual α L from rfl]
    have hpow : α ^ (2 * (L.length + 1)) = α ^ (2 * L.length) * α ^ 2 := by
      rw [show 2 * (L.length + 1) = 2 * L.length + 2 by omega, pow_add]
    have hmul : α ^ (2 * L.length) * ((p.1 *ᵥ δ₀ + p.2) ⬝ᵥ (p.1 *ᵥ δ₀ + p.2))
        ≤ α ^ (2 * L.length) * (α ^ 2 * (δ₀ ⬝ᵥ δ₀) + p.2 ⬝ᵥ p.2) :=
      mul_le_mul_of_nonneg_left hstep (pow_nonneg hα _)
    simp only [List.length_cons]
    rw [hpow]
    nlinarith [hmul, sq_nonneg (α ^ (2 * L.length))]

end SecondMoment

end Hagi.Core

namespace Hagi
export Hagi.Core (propagate propagate_cons propagate_bound propagate_bound_contractive weightedResidual propagate_sq_bound)
end Hagi
