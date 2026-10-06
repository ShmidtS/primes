/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# StationaryFlatness: subquadratic tails bound the flatness moment (R174e)

The last module of the thermodynamic layer (§8.8 of
FORMALIZATION_PLAN.md, round R174e). Source arXiv:2607.16384:
for constant-stepsize SGD the STATIONARY MEASURE has
subquadratic tails near flat minima — the measurable
replacement of the folklore "flat minima generalize".
This module proves the finite kernel of that statement: a
natural-valued flatness functional with a power-tail bound
has a finite mean controlled by the tail constant.

**Results.**

* `tail_sum_identity` — THE TAIL-SUM IDENTITY: for a
  natural-valued functional `X ≤ M` on a finite probability
  space, `E[X] = Σ_{k=1}^{M} P[X ≥ k]` (expectation as the
  sum of tail probabilities — the discrete layer-cake
  decomposition).

* `sum_pow2_inv_le` — the p = 2 tail series bound:
  `Σ_{k=1}^{N} k^(−2) ≤ 2 − 1/N`, by the telescoping
  comparison `k^(−2) ≤ (k−1)^(−1) − k^(−1)` for `k ≥ 2`.

* `flatness_moment_bound` — THE STATIONARY-FLATNESS KERNEL:
  if the flatness functional's tail obeys `P[X ≥ k] ≤ C/k²`
  (the subquadratic-tail reading of 2607.16384), then
  `E[X] ≤ 2C` — the mean flatness is controlled by the tail
  constant, horizon-independent. "Flat minima generalize"
  becomes: the stationary measure's flatness moment is finite
  and measurable from the tail.

**Honest boundary.** No claim here connects the bound to
GENERALIZATION (that link is PAC-Bayes territory, R155); the
constant-stepsize SGD provenance of the tail hypothesis is
runtime interpretation — only the tail-to-moment calculus is
a theorem.
-/

namespace Hagi.Probability

open Finset

variable {Ω : Type} [Fintype Ω]

/-- Expectation of a natural-valued functional under a
probability vector `q`. -/
noncomputable def expectNat (q : Ω → ℝ) (X : Ω → ℕ) : ℝ :=
  ∑ ω, q ω * (X ω)

/-- Tail probability `P[X ≥ k]` under `q`. -/
noncomputable def probGe (q : Ω → ℝ) (X : Ω → ℕ) (k : ℕ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => k ≤ X ω), q ω

/-- **The tail-sum identity** (discrete layer cake): for a
natural-valued functional bounded by `M`, the expectation is
the sum of its tail probabilities. -/
theorem tail_sum_identity (q : Ω → ℝ) (X : Ω → ℕ) (M : ℕ)
    (hX : ∀ ω, X ω ≤ M) :
    expectNat q X = ∑ k ∈ Finset.range M, probGe q X (k + 1) := by
  classical
  unfold expectNat probGe
  have key : ∀ ω : Ω, ∑ k ∈ Finset.range M,
      (if k + 1 ≤ X ω then q ω else 0) = q ω * (X ω) := by
    intro ω
    have hM : X ω ≤ M := hX ω
    rw [← Finset.sum_filter]
    have hcard : (Finset.range M).filter (fun k => k + 1 ≤ X ω)
        = Finset.range (X ω) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hcard, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_comm _ _
  calc ∑ ω, q ω * (X ω)
      = ∑ ω, ∑ k ∈ Finset.range M, (if k + 1 ≤ X ω then q ω else 0) :=
        Finset.sum_congr rfl fun ω _ => (key ω).symm
    _ = ∑ k ∈ Finset.range M, ∑ ω : Ω, (if k + 1 ≤ X ω then q ω else 0) :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.range M,
          ∑ ω ∈ Finset.univ.filter (fun ω => k + 1 ≤ X ω), q ω := by
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_filter]

/-- The telescoping comparison: for `k ≥ 2`,
`k^(−2) ≤ (k−1)^(−1) − k^(−1)`. -/
theorem inv_sq_le_sub_inv {k : ℕ} (hk : 2 ≤ k) :
    ((k : ℕ) : ℝ) ⁻¹ ^ 2 ≤ (((k : ℕ) : ℝ) - 1)⁻¹ - (((k : ℕ) : ℝ))⁻¹ := by
  have h1 : (0:ℝ) < ((k : ℕ) : ℝ) := by positivity
  have h2 : (0:ℝ) < (((k : ℕ) : ℝ)) - 1 := by
    have hle : (2:ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk
    linarith
  have hsub : (((k : ℕ) : ℝ) - 1)⁻¹ - (((k : ℕ) : ℝ))⁻¹
      = 1 / ((((k : ℕ) : ℝ) - 1) * ((k : ℕ) : ℝ)) := by
    rw [inv_sub_inv (by linarith) (by linarith), div_eq_inv_mul, inv_mul_eq_div]
    field_simp
    ring
  rw [hsub, inv_pow]
  field_simp
  nlinarith [h1, h2]

/-- **The p = 2 tail series bound**: `Σ_{k=1}^{N} k^(−2) ≤
2 − 1/N` for `N ≥ 1` — the telescoping comparison summed
(the first term `1` plus the collapsed tail `1 − 1/N`). -/
theorem sum_pow2_inv_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ⁻¹ ^ 2
      ≤ 2 - ((N : ℕ) : ℝ)⁻¹ := by
  induction N with
  | zero => omega
  | succ N ih =>
      cases Nat.eq_zero_or_pos N with
      | inl h0 =>
          subst h0
          norm_num
      | inr hpos =>
          have hterm := inv_sq_le_sub_inv (k := N + 1) (by omega)
          have hprev : ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ⁻¹ ^ 2
              ≤ 2 - ((N : ℕ) : ℝ)⁻¹ := ih hpos
          rw [Finset.sum_range_succ]
          have hnew : (((N + 1 : ℕ) : ℝ) ⁻¹ ^ 2)
              ≤ ((N : ℕ) : ℝ)⁻¹ - ((N + 1 : ℕ) : ℝ)⁻¹ := by
            simpa using hterm
          have hposN : (0:ℝ) < ((N : ℕ) : ℝ)⁻¹ := by positivity
          have hposN1 : (0:ℝ) < ((N + 1 : ℕ) : ℝ)⁻¹ := by positivity
          linarith

/-- **The stationary-flatness kernel**: a natural-valued
flatness functional `X ≤ M` whose tail obeys
`P[X ≥ k] ≤ C/k²` (the subquadratic-tail reading of
2607.16384) has `E[X] ≤ 2C` — the mean flatness is controlled
by the tail constant, independent of the horizon `M`.
"Flat minima generalize" becomes: the flatness moment is
finite and measurable from the tail. -/
theorem flatness_moment_bound (q : Ω → ℝ) (X : Ω → ℕ) (M : ℕ)
    (hX : ∀ ω, X ω ≤ M) (C : ℝ) (hC : 0 ≤ C)
    (htail : ∀ k ∈ Finset.range M,
      probGe q X (k + 1) ≤ C * (((k + 1 : ℕ) : ℝ) ⁻¹ ^ 2)) :
    expectNat q X ≤ 2 * C := by
  rw [tail_sum_identity q X M hX]
  cases Nat.eq_zero_or_pos M with
  | inl h0 =>
      subst h0
      have : ∀ ω, X ω = 0 := fun ω => Nat.le_zero.mp (hX ω)
      simp [expectNat, this]
      linarith
  | inr hpos =>
      have hsum := sum_pow2_inv_le M hpos
      have hbound : ∑ k ∈ Finset.range M, probGe q X (k + 1)
          ≤ C * ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) ⁻¹ ^ 2 := by
        calc ∑ k ∈ Finset.range M, probGe q X (k + 1)
            ≤ ∑ k ∈ Finset.range M, C * ((k + 1 : ℕ) : ℝ) ⁻¹ ^ 2 :=
              Finset.sum_le_sum fun k hk => htail k hk
          _ = C * ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) ⁻¹ ^ 2 := by
              rw [← Finset.mul_sum]
      have hfinal : C * ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) ⁻¹ ^ 2 ≤ 2 * C := by
        calc C * ∑ k ∈ Finset.range M, ((k + 1 : ℕ) : ℝ) ⁻¹ ^ 2
            ≤ C * (2 - ((M : ℕ) : ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_left hsum hC
          _ ≤ 2 * C := by
              have hminv : (0:ℝ) < ((M : ℕ) : ℝ)⁻¹ := by positivity
              nlinarith
      linarith

end Hagi.Probability
