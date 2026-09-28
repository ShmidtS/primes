/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# Ridge re-solve: the optimality of the guarded normal equations

This module formalizes the **W2 re-solve** step of the HAGI_v2
terni4 recipe (`scripts/dsv4_refit_experts.py`, `ridge_solve_guarded`):

> before quantization W2 is re-solved in closed form (guarded ridge)
> to best explain the expert's target outputs *at the already-
> quantized W13* — a functional fit, not a weight fit.

The row-wise problem solved by the guarded ridge is

`min_w  ‖X w − y‖² + λ ‖w‖²`,

whose stationary point is given by the normal equations

`Xᵀ (X w₀ − y) + λ w₀ = 0`.

Formalized here:

* `Hagi.ridge` — the ridge objective for one row: the squared
  residual against the drifted targets plus the squared weight.
* `Hagi.ridgeNormalEq` — the normal equation as a vector identity
  (exactly what `ridge_solve_guarded` solves: Gram `Xᵀ X + λ I`,
  right-hand side `Xᵀ y`).
* `Hagi.ridge_optimal` — **the normal equations are sufficient for
  global optimality**: if `w*` satisfies the normal equation, then
  for every `w`, `ridge w ≥ ridge w*`. The proof is the
  complete-the-square decomposition: with `δ = w − w*`,

  `ridge w = ridge w₀ + ‖X δ‖² + λ‖δ‖²`

  — the cross term vanishes exactly by the normal equation, and the
  two square terms are nonnegative (`λ ≥ 0`). The guard (pinv
  fallback on a singular Gram) plays no role in optimality: any
  solution of the normal equation is a global minimizer; the guard
  only guarantees *existence* on ill-conditioned Grams.

This is the closed-form half of "the error must be pushed out of
W2": the re-solve provably extracts everything the (already
quantized) upstream can explain, so whatever remains is genuinely
fresh residual — the `r_l` of `Hagi.ErrorProp`.
-/

open scoped Matrix

namespace Hagi

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The ridge objective for one row of the re-solve: the squared
residual of `X w` against the (drifted) target `y`, plus the
squared weight. `X` collects the activations *as seen through the
already-quantized upstream* (`dsv4_collect_seq.py`), `y` the
expert's original outputs — the functional fit of the terni4
recipe. -/
noncomputable def ridge (X : Matrix m n ℝ) (y : m → ℝ) (lam : ℝ)
    (w : n → ℝ) : ℝ :=
  ∑ i, ((X *ᵥ w) i - y i) ^ 2 + lam * ∑ j, w j * w j

variable {X : Matrix m n ℝ} {y : m → ℝ} {lam : ℝ}

/-- The normal equation of the ridge problem, stated as a vector
identity: `Xᵀ (X w₀ − y) + λ w₀ = 0` — the stationarity condition
that `ridge_solve_guarded` solves (Gram `Xᵀ X + λ I`, right-hand
side `Xᵀ y`). -/
def ridgeNormalEq (X : Matrix m n ℝ) (y : m → ℝ) (lam : ℝ)
    (w : n → ℝ) : Prop :=
  Xᵀ *ᵥ ((X *ᵥ w) - y) + lam • w = 0

/-- **The normal equations are sufficient for global optimality.**
If `w*` satisfies the ridge normal equation, then every `w` has
`ridge w ≥ ridge w*`. The proof is the complete-the-square
decomposition

`ridge w = ridge w₀ + ‖X (w − w₀)‖² + λ‖w − w*‖²`

whose cross term vanishes exactly by the normal equation; the two
square terms are nonnegative (`λ ≥ 0`). This formalizes why the W2
re-solve step of the terni4 recipe is safe to do *before*
quantization: the re-solved `W2` provably explains everything the
quantized upstream can carry, and the residual it leaves is the
fresh `r_l` of the telescopic error budget. -/
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
    show ((X *ᵥ w₀) - y) ⬝ᵥ (X *ᵥ δ)
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
    show ∑ j, (Xᵀ *ᵥ ((X *ᵥ w₀) - y)) j * δ j + lam * ∑ j, w₀ j * δ j = 0
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

end Hagi
