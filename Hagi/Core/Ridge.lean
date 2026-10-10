/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Ridge re-solve: optimality of the guarded normal equations

The row-wise ridge problem is

`min_w  ‖X w − y‖² + λ ‖w‖²`,

with the normal equation `Xᵀ (X w₀ − y) + λ w₀ = 0`
(`ridgeNormalEq`).

* `ridge` — the objective: squared residual plus `λ` times the
  squared weight.
* `ridge_optimal` — the normal equations are sufficient for
  global optimality: if `w₀` satisfies `ridgeNormalEq` and
  `0 ≤ λ`, then `ridge X y lam w ≥ ridge X y lam w₀` for every
  `w`. The proof is the complete-the-square decomposition with
  `δ = w − w₀`; the cross term vanishes by the normal equation.
-/

open scoped Matrix

namespace Hagi.Core

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The ridge objective for one row: the squared residual of
`X *ᵥ w` against the target `y`, plus `lam` times the squared
weight. -/
noncomputable def ridge (X : Matrix m n ℝ) (y : m → ℝ) (lam : ℝ)
    (w : n → ℝ) : ℝ :=
  ∑ i, ((X *ᵥ w) i - y i) ^ 2 + lam * ∑ j, w j * w j

variable {X : Matrix m n ℝ} {y : m → ℝ} {lam : ℝ}

/-- The ridge normal equation `Xᵀ (X w − y) + λ • w = 0`. -/
def ridgeNormalEq (X : Matrix m n ℝ) (y : m → ℝ) (lam : ℝ)
    (w : n → ℝ) : Prop :=
  Xᵀ *ᵥ ((X *ᵥ w) - y) + lam • w = 0

/-- The normal equations are sufficient for global optimality:
if `0 ≤ lam` and `w₀` satisfies `ridgeNormalEq X y lam w₀`, then
`ridge X y lam w ≥ ridge X y lam w₀` for every `w`, by the
complete-the-square decomposition (the cross term vanishes by the
normal equation). -/
theorem ridge_optimal (hlam : 0 ≤ lam) {w₀ : n → ℝ}
    (hne : ridgeNormalEq X y lam w₀) :
    ∀ w : n → ℝ, ridge X y lam w ≥ ridge X y lam w₀ := by
  intro w
  set δ : n → ℝ := w - w₀ with hδ
  have hw : w = w₀ + δ := by rw [hδ]; abel
  -- pointwise square expansion of the residual
  have key : ∀ i : m,
      ((X *ᵥ (w₀ + δ)) i - y i) ^ 2
        = ((X *ᵥ w₀) i - y i) ^ 2
          + 2 * (((X *ᵥ w₀) i - y i) * (X *ᵥ δ) i)
          + (X *ᵥ δ) i * (X *ᵥ δ) i := by
    intro i
    rw [Matrix.mulVec_add, Pi.add_apply]
    ring
  -- pointwise square expansion of the weight
  have keyw : ∀ j : n,
      (w₀ + δ) j * (w₀ + δ) j
        = w₀ j * w₀ j + 2 * (w₀ j * δ j) + δ j * δ j := by
    intro j
    rw [Pi.add_apply]
    ring
  -- the residual sum, split
  have hres : ∑ i, ((X *ᵥ (w₀ + δ)) i - y i) ^ 2
      = ∑ i, ((X *ᵥ w₀) i - y i) ^ 2
        + 2 * ∑ i, ((X *ᵥ w₀) i - y i) * (X *ᵥ δ) i
        + ∑ i, (X *ᵥ δ) i * (X *ᵥ δ) i := by
    simp_rw [key]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  -- the weight sum, split
  have hwsum : ∑ j, (w₀ + δ) j * (w₀ + δ) j
      = ∑ j, w₀ j * w₀ j + 2 * ∑ j, w₀ j * δ j + ∑ j, δ j * δ j := by
    simp_rw [keyw]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  -- the cross term is the dot of the normal-equation residual with δ
  have hcross : ∑ i, ((X *ᵥ w₀) i - y i) * (X *ᵥ δ) i
      = (Xᵀ *ᵥ ((X *ᵥ w₀) - y)) ⬝ᵥ δ := by
    change ((X *ᵥ w₀) - y) ⬝ᵥ (X *ᵥ δ)
      = (Xᵀ *ᵥ ((X *ᵥ w₀) - y)) ⬝ᵥ δ
    rw [Matrix.dotProduct_mulVec,
      ← Matrix.vecMul_transpose (A := Xᵀ) (x := ((X *ᵥ w₀) - y)),
      Matrix.transpose_transpose]
  -- the normal equation, dotted with δ
  have hdot : (Xᵀ *ᵥ ((X *ᵥ w₀) - y)) ⬝ᵥ δ + lam * ∑ j, w₀ j * δ j = 0 := by
    have h1 : (Xᵀ *ᵥ ((X *ᵥ w₀) - y) + lam • w₀) ⬝ᵥ δ = 0 := by
      rw [hne, zero_dotProduct]
    have h2 : ∀ j : n,
        (Xᵀ *ᵥ ((X *ᵥ w₀) - y) + lam • w₀) j
          = (Xᵀ *ᵥ ((X *ᵥ w₀) - y)) j + lam * w₀ j := by
      intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib] at h1
    have h3 : ∑ x, lam * w₀ x * δ x = lam * ∑ x, w₀ x * δ x := by
      rw [Finset.sum_congr rfl fun x _ => mul_assoc lam (w₀ x) (δ x),
        Finset.mul_sum]
    rw [h3] at h1
    change ∑ j, (Xᵀ *ᵥ ((X *ᵥ w₀) - y)) j * δ j + lam * ∑ j, w₀ j * δ j = 0
    linarith [h1]
  -- nonnegative remainders
  have hs2 : 0 ≤ ∑ i, (X *ᵥ δ) i * (X *ᵥ δ) i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hd2 : 0 ≤ lam * ∑ j, δ j * δ j :=
    mul_nonneg hlam (Finset.sum_nonneg fun j _ => mul_self_nonneg _)
  unfold ridge
  rw [hw, hres, hwsum, hcross]
  -- goal: big sum ≥ small sum; cancel via hdot
  have hdots : (w₀ : n → ℝ) ⬝ᵥ δ = ∑ j, w₀ j * δ j := rfl
  rw [← hdots] at hdot ⊢
  linarith

end Hagi.Core

namespace Hagi
export Hagi.Core (ridge ridgeNormalEq ridge_optimal)
end Hagi
