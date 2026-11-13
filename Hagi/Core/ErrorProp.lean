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
* `propagate_sub` — the affine difference identity: the residuals
  cancel between two passes, leaving the linear fold `propagateLin`.
* `propagateLin_norm_le` — the linear fold contracts by
  `cascadeGain L = ∏ ‖J_l‖` (per-layer product, sharper than a
  uniform `α ^ L`); `cascadeGain_le_one` collapses it for
  non-expansive stacks.
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

/-! ## Linear cascade machinery: the leak of a projected adapter

The difference of two passes over the SAME stack cancels the
per-layer residuals (they appear in both evaluations), so the
perturbation (`leak`) obeys a purely linear recursion governed by
the product of the per-layer operator norms. This is the cascade
side of the A8 F1 composition bound (consumed by
`Hagi.Architecture.CascadeLeak`). -/

section LinearCascade

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The pure linear part of the telescopic pass: the fold
`δ ↦ p.1 *ᵥ δ` over the stack, without the per-layer residuals. -/
def propagateLin
    (L : List (Matrix n n ℝ × (n → ℝ))) (δ₀ : n → ℝ) : n → ℝ :=
  L.foldl (fun δ p => p.1 *ᵥ δ) δ₀

/-- The affine difference identity: the residuals of the two passes
cancel BETWEEN the evaluations, and the difference is exactly the
linear fold of the input difference. -/
theorem propagate_sub
    (L : List (Matrix n n ℝ × (n → ℝ))) (a b : n → ℝ) :
    propagate L a - propagate L b = propagateLin L (a - b) := by
  induction L generalizing a b with
  | nil => simp [propagate, propagateLin]
  | cons p L ih =>
    rw [propagate_cons, propagate_cons, ih]
    have hstep : p.1 *ᵥ a + p.2 - (p.1 *ᵥ b + p.2) = p.1 *ᵥ (a - b) := by
      funext i
      have hi : ∀ x : n, p.1 i x * (a x - b x)
          = p.1 i x * a x - p.1 i x * b x := fun _ => by ring
      simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.sub_apply]
      rw [Finset.sum_congr rfl (fun x _ => hi x), Finset.sum_sub_distrib]
      ring
    rw [hstep]
    rfl

/-- The linear fold is exactly homogeneous in the entering vector. -/
theorem propagateLin_smul
    (L : List (Matrix n n ℝ × (n → ℝ))) (w : ℝ) (δ₀ : n → ℝ) :
    propagateLin L (w • δ₀) = w • propagateLin L δ₀ := by
  induction L generalizing δ₀ with
  | nil => simp [propagateLin]
  | cons p L ih =>
    have hstep : p.1 *ᵥ (w • δ₀) = w • (p.1 *ᵥ δ₀) := by
      funext i
      simp [Matrix.mulVec, dotProduct_smul]
    show propagateLin L (p.1 *ᵥ (w • δ₀)) = w • propagateLin L (p.1 *ᵥ δ₀)
    rw [hstep, ih]

/-- The stack gain: the product of the per-layer operator norms.
This is the honest `L_stack = ∏ L_m` of the cascade leak bound
(sharper than the uniform `α ^ L.length` of `propagate_bound`). -/
noncomputable def cascadeGain
    (L : List (Matrix n n ℝ × (n → ℝ))) : ℝ :=
  (L.map fun p => ‖p.1‖).prod

/-- The linear fold contracts by the stack gain:
`‖propagateLin L δ₀‖ ≤ cascadeGain L * ‖δ₀‖`. -/
theorem propagateLin_norm_le
    (L : List (Matrix n n ℝ × (n → ℝ))) (δ₀ : n → ℝ) :
    ‖propagateLin L δ₀‖ ≤ cascadeGain L * ‖δ₀‖ := by
  induction L generalizing δ₀ with
  | nil => simp [propagateLin, cascadeGain]
  | cons p L ih =>
    have key : ‖p.1 *ᵥ δ₀‖ ≤ ‖p.1‖ * ‖δ₀‖ :=
      (Matrix.linfty_opNorm_mulVec p.1 δ₀).trans
        (mul_le_mul_of_nonneg_right le_rfl (norm_nonneg δ₀))
    have hprod : 0 ≤ cascadeGain L :=
      List.prod_nonneg (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨q, _, rfl⟩ := hx
        exact norm_nonneg q.1)
    show ‖propagateLin L (p.1 *ᵥ δ₀)‖ ≤ cascadeGain (p :: L) * ‖δ₀‖
    simp only [cascadeGain, List.map_cons, List.prod_cons]
    calc ‖propagateLin L (p.1 *ᵥ δ₀)‖ ≤ cascadeGain L * ‖p.1 *ᵥ δ₀‖ := ih _
      _ ≤ cascadeGain L * (‖p.1‖ * ‖δ₀‖) :=
          mul_le_mul_of_nonneg_left key hprod
      _ = ‖p.1‖ * cascadeGain L * ‖δ₀‖ := by ring

/-- If every layer is non-expansive (`‖p.1‖ ≤ 1`, the hypothesis
shape of `propagate_bound_contractive`), the stack gain is at most
one. -/
theorem cascadeGain_le_one
    (L : List (Matrix n n ℝ × (n → ℝ))) (hα : ∀ p ∈ L, ‖p.1‖ ≤ 1) :
    cascadeGain L ≤ 1 := by
  induction L with
  | nil => simp [cascadeGain]
  | cons p L ih =>
    have hL : ∀ q ∈ L, ‖q.1‖ ≤ 1 := fun q hq => hα q (List.Mem.tail p hq)
    have hp : ‖p.1‖ ≤ 1 := hα p (List.Mem.head L)
    have hnn : 0 ≤ cascadeGain L :=
      List.prod_nonneg (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨q, _, rfl⟩ := hx
        exact norm_nonneg q.1)
    have hnn' : 0 ≤ (List.map (fun q : Matrix n n ℝ × (n → ℝ) => ‖q.1‖) L).prod := hnn
    have hpp := mul_le_mul hp (ih hL) hnn' zero_le_one
    simp only [cascadeGain] at hpp
    simp only [cascadeGain, List.map_cons, List.prod_cons]
    linarith [hpp]

end LinearCascade

end Hagi.Core

