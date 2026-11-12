/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib
import Hagi.Core.ErrorProp

/-!
# Manifold hyper-connectivity: doubly stochastic mixing is an L2 contraction

The mHC residual stream mixes tokens through doubly stochastic
matrices (Birkhoff-style convex mixing). This file certifies:

* `IsRowStochastic` / `IsDoublyStochastic` — the premise-form
  hypotheses (nonneg entries; row sums 1; column sums 1).
* `doublyStochastic_sq_le` — MAIN: `‖M x‖₂² ≤ ‖x‖₂²`, by the
  Jensen/Cauchy argument: each output coordinate is a convex
  combination (per-row weighted Cauchy–Schwarz, Mathlib canon
  `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`), and the column-sum
  property redistributes exactly `Σⱼ xⱼ²` back.
* `rowStochastic_opNorm_le_one` — the ℓ∞ operator norm of a
  row-stochastic matrix is ≤ 1 (row sums alone suffice); this is
  the same scoped operator-norm instance consumed by
  `Hagi.Core.propagate_bound_contractive`.
* `mhc_stack_no_growth` — a depth-L stack of doubly stochastic
  mixing layers with zero fresh residual propagates no error
  growth: `‖propagate L δ₀‖ ≤ ‖δ₀‖`, delegating to the EXISTING
  `Hagi.Core.propagate_bound_contractive` at ρ = 0.

Honest boundary: `M` is a HYPOTHESIS, not a construction — Sinkhorn
balancing (which produces doubly stochastic approximations) is not
needed and not claimed. The bound is tight: permutation matrices
are doubly stochastic and give equality. A row-stochastic-only
matrix can expand L2 (mass concentration), so the column-sum
premise is load-bearing.
-/

set_option linter.style.header false

open scoped Matrix Matrix.Norms.Operator NNReal

namespace Hagi.Architecture.ManifoldHyperConn

variable {n : Type*} [Fintype n]

/-- Row-stochastic: nonnegative entries, each row sums to 1. -/
def IsRowStochastic (M : Matrix n n ℝ) : Prop :=
  (∀ i j : n, 0 ≤ M i j) ∧ ∀ i : n, ∑ j, M i j = 1

/-- Doubly stochastic: row-stochastic AND each column sums to 1. -/
def IsDoublyStochastic (M : Matrix n n ℝ) : Prop :=
  IsRowStochastic M ∧ ∀ j : n, ∑ i, M i j = 1

/-- MAIN: a doubly stochastic matrix contracts L2 —
`Σᵢ (M x)ᵢ² ≤ Σⱼ xⱼ²`. Jensen/Cauchy per row (convex combination of
squares dominates the square of the convex combination), column
sums redistribute the mass exactly. -/
theorem doublyStochastic_sq_le (M : Matrix n n ℝ)
    (hM : IsDoublyStochastic M) (x : n → ℝ) :
    ∑ i, (M *ᵥ x) i ^ 2 ≤ ∑ i, x i ^ 2 := by
  obtain ⟨⟨hnn, hrow⟩, hcol⟩ := hM
  have hrowle : ∀ i : n,
      (M *ᵥ x) i ^ 2 ≤ ∑ j, M i j * x j ^ 2 := by
    intro i
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset n)
      (f := fun j => M i j) (g := fun j => M i j * x j ^ 2)
      (r := fun j => M i j * x j)
      (fun j _ => hnn i j) (fun j _ => mul_nonneg (hnn i j) (sq_nonneg _))
      (fun j _ => le_of_eq (by ring))
    have hMx : (M *ᵥ x) i = ∑ j, M i j * x j := by
      simp [Matrix.mulVec, dotProduct]
    rw [hMx]
    rw [hrow i] at h
    simpa using h
  calc ∑ i, (M *ᵥ x) i ^ 2 ≤ ∑ i, ∑ j, M i j * x j ^ 2 :=
        Finset.sum_le_sum (fun i _ => hrowle i)
    _ = ∑ j, ∑ i, M i j * x j ^ 2 := Finset.sum_comm
    _ = ∑ j, x j ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_mul, hcol j, one_mul]

/-- The ℓ∞ operator norm of a row-stochastic matrix is ≤ 1 (row
sums suffice; nonnegativity makes the absolute row sum equal the
row sum). Same scoped operator-norm instance as
`Hagi.Core.ErrorProp`. -/
theorem rowStochastic_opNorm_le_one (M : Matrix n n ℝ)
    (hM : IsRowStochastic M) :
    ‖M‖ ≤ 1 := by
  obtain ⟨hnn, hrow⟩ := hM
  rw [Matrix.linfty_opNorm_def]
  have hsumN : ∀ i : n, (∑ j, ‖M i j‖₊ : ℝ≥0) = 1 := by
    intro i
    have hcoe : ((∑ j, ‖M i j‖₊ : ℝ≥0) : ℝ) = 1 := by
      have h1 : ∀ j : n, ((‖M i j‖₊ : ℝ≥0) : ℝ) = |M i j| := fun j => by simp
      rw [NNReal.coe_sum, Finset.sum_congr rfl (fun j _ => h1 j),
        Finset.sum_congr rfl (fun j _ => abs_of_nonneg (hnn i j)), hrow i]
    exact Subtype.ext hcoe
  exact le_trans (by exact_mod_cast Finset.sup_le (fun i _ => le_of_eq (hsumN i)))
    (by norm_num)

/-- Corollary: a depth-L stack of doubly stochastic mixing layers
with zero fresh residual propagates NO error growth — the mHC stack
satisfies the existing contractive telescope bound
`Hagi.Core.propagate_bound_contractive` at ρ = 0:
`‖propagate L δ₀‖ ≤ ‖δ₀‖`. -/
theorem mhc_stack_no_growth {n : Type*} [Fintype n] [DecidableEq n]
    (L : List (Matrix n n ℝ × (n → ℝ))) (δ₀ : n → ℝ)
    (hM : ∀ p ∈ L, IsDoublyStochastic p.1)
    (hres : ∀ p ∈ L, p.2 = 0) :
    ‖Hagi.Core.propagate L δ₀‖ ≤ ‖δ₀‖ := by
  have h := Hagi.Core.propagate_bound_contractive (0:ℝ) L δ₀
    (fun p hp => rowStochastic_opNorm_le_one p.1 (hM p hp).1)
    (fun p hp => by rw [hres p hp]; exact norm_zero.le)
  simpa using h

end Hagi.Architecture.ManifoldHyperConn
