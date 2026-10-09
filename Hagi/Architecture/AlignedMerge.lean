/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.CortexFiber

set_option linter.style.header false

/-!
# AlignedMerge: the misalignment penalty

* `dotCS` — Cauchy-Schwarz for `dotProduct`, squared form.
* `frobSubord` — the Frobenius norm is subordinated:
  `(M *ᵥ w) ⬝ᵥ (M *ᵥ w) ≤ frobSq M * (w ⬝ᵥ w)`.
* `misalignCross` — the merge cross term satisfies
  `((V *ᵥ r) ⬝ᵥ (W *ᵥ s)) ^ 2 ≤
  frobSq (Vᵀ * W) * (r ⬝ᵥ r) * (s ⬝ᵥ s)`.
* `mergeEnergyPerturbed` — with orthonormal `V`, `W`, the
  merged energy deviates from the Pythagorean value
  `(r ⬝ᵥ r) + (s ⬝ᵥ s)` by at most
  `2 * (frobSq (Vᵀ * W)).sqrt * (r ⬝ᵥ r).sqrt * (s ⬝ᵥ s).sqrt`.

The principal-angle (spectral) version remains open — Mathlib
lacks Eckart-Young.
-/

namespace Hagi.Cortex

open Finset Matrix

/-- Squared Frobenius norm of a matrix (the misalignment
budget). -/
def frobSq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j) ^ 2

/-- Cauchy–Schwarz for dotProduct, squared form. -/
theorem dotCS {n : ℕ} (a b : Fin n → ℝ) :
    (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  unfold dotProduct
  have h := sum_mul_sq_le_sq_mul_sq univ a b
  simp only [← pow_two] at h ⊢
  exact h

/-- The Frobenius norm is subordinated: applying M costs at
most frobSq(M) times the input energy (per-row
Cauchy–Schwarz). -/
theorem frobSubord {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (w : Fin n → ℝ) :
    (M *ᵥ w) ⬝ᵥ (M *ᵥ w) ≤ frobSq M * (w ⬝ᵥ w) := by
  have key : ∀ i : Fin m,
      (∑ j, M i j * w j) ^ 2
        ≤ (∑ j, (M i j) ^ 2) * (∑ j, (w j) ^ 2) :=
    fun i => sum_mul_sq_le_sq_mul_sq univ (fun j => M i j) w
  unfold frobSq dotProduct
  simp only [pow_two, Matrix.mulVec]
  show (∑ i, (∑ j, M i j * w j) * (∑ j, M i j * w j))
      ≤ (∑ i, ∑ j, M i j * M i j) * (∑ i, w i * w i)
  have key : ∀ i : Fin m,
      (∑ j, M i j * w j) * (∑ j, M i j * w j)
        ≤ (∑ j, M i j * M i j) * (∑ j, w j * w j) := by
    intro i
    have h := sum_mul_sq_le_sq_mul_sq univ (fun j => M i j) w
    simp only [pow_two] at h
    exact h
  calc (∑ i, (∑ j, M i j * w j) * (∑ j, M i j * w j))
      ≤ ∑ i, ((∑ j, M i j * M i j) * (∑ j, w j * w j)) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (∑ i, ∑ j, M i j * M i j) * (∑ j, w j * w j) := by
        rw [← Finset.sum_mul]

/-- The merge cross term between two fibers satisfies
`((V *ᵥ r) ⬝ᵥ (W *ᵥ s)) ^ 2 ≤ frobSq (Vᵀ * W) * (r ⬝ᵥ r) * (s ⬝ᵥ s)`;
aligned fibers (`Vᵀ * W = 0`) pay nothing. -/
theorem misalignCross {d r1 r2 : ℕ} (V : Matrix (Fin d) (Fin r1) ℝ)
    (W : Matrix (Fin d) (Fin r2) ℝ)
    (r : Fin r1 → ℝ) (s : Fin r2 → ℝ) :
    ((V *ᵥ r) ⬝ᵥ (W *ᵥ s)) ^ 2
      ≤ frobSq (Vᵀ * W) * (r ⬝ᵥ r) * (s ⬝ᵥ s) := by
  have hgram : (V *ᵥ r) ⬝ᵥ (W *ᵥ s) = r ⬝ᵥ ((Vᵀ * W) *ᵥ s) := by
    rw [Matrix.dotProduct_mulVec, mulVec_vecMul_gram, Matrix.dotProduct_mulVec]
  rw [hgram]
  have h1 := dotCS r ((Vᵀ * W) *ᵥ s)
  have h2 := frobSubord (Vᵀ * W) s
  have hfrob : 0 ≤ frobSq (Vᵀ * W) := by
    unfold frobSq
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact sq_nonneg _
  have hr : 0 ≤ r ⬝ᵥ r := by
    unfold dotProduct
    apply Finset.sum_nonneg
    intro i _
    exact mul_self_nonneg _
  have hs : 0 ≤ s ⬝ᵥ s := by
    unfold dotProduct
    apply Finset.sum_nonneg
    intro i _
    exact mul_self_nonneg _
  calc (r ⬝ᵥ ((Vᵀ * W) *ᵥ s)) ^ 2
      ≤ (r ⬝ᵥ r) * (((Vᵀ * W) *ᵥ s) ⬝ᵥ ((Vᵀ * W) *ᵥ s)) := h1
    _ ≤ (r ⬝ᵥ r) * (frobSq (Vᵀ * W) * (s ⬝ᵥ s)) :=
          mul_le_mul_of_nonneg_left h2 hr
    _ = frobSq (Vᵀ * W) * (r ⬝ᵥ r) * (s ⬝ᵥ s) := by ring

/-- With orthonormal fiber bases `V` and `W`, the merged
energy deviates from the Pythagorean value `(r ⬝ᵥ r) + (s ⬝ᵥ s)`
by at most `2 * (frobSq (Vᵀ * W)).sqrt * (r ⬝ᵥ r).sqrt *
(s ⬝ᵥ s).sqrt`. -/
theorem mergeEnergyPerturbed {d r1 r2 : ℕ} (V : Matrix (Fin d) (Fin r1) ℝ)
    (W : Matrix (Fin d) (Fin r2) ℝ)
    (hV : IsOrthoCol V) (hW : IsOrthoCol W)
    (r : Fin r1 → ℝ) (s : Fin r2 → ℝ) :
    (V *ᵥ r + W *ᵥ s) ⬝ᵥ (V *ᵥ r + W *ᵥ s)
      ≤ (r ⬝ᵥ r) + (s ⬝ᵥ s)
        + 2 * (frobSq (Vᵀ * W)).sqrt * (r ⬝ᵥ r).sqrt * (s ⬝ᵥ s).sqrt := by
  have hsplit : (V *ᵥ r + W *ᵥ s) ⬝ᵥ (V *ᵥ r + W *ᵥ s)
      = (V *ᵥ r) ⬝ᵥ (V *ᵥ r) + 2 * ((V *ᵥ r) ⬝ᵥ (W *ᵥ s))
        + (W *ᵥ s) ⬝ᵥ (W *ᵥ s) := by
    rw [dotProduct_add, add_dotProduct, add_dotProduct]
    linarith [dotProduct_comm (V *ᵥ r) (W *ᵥ s)]
  have hfrob : 0 ≤ frobSq (Vᵀ * W) := by
    unfold frobSq
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _
  have hr : 0 ≤ r ⬝ᵥ r := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hs : 0 ≤ s ⬝ᵥ s := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  set X : ℝ := (frobSq (Vᵀ * W)).sqrt * (r ⬝ᵥ r).sqrt * (s ⬝ᵥ s).sqrt with hXdef
  have hXpos : 0 ≤ X := by
    rw [hXdef]
    positivity
  have hXsq : X ^ 2 = frobSq (Vᵀ * W) * (r ⬝ᵥ r) * (s ⬝ᵥ s) := by
    rw [hXdef, mul_pow, mul_pow, Real.sq_sqrt hfrob, Real.sq_sqrt hr,
      Real.sq_sqrt hs]
  have hcrossle : (V *ᵥ r) ⬝ᵥ (W *ᵥ s) ≤ X :=
    le_of_sq_le_sq (by
      rw [hXsq]
      exact misalignCross V W r s) hXpos
  rw [hsplit, orthoNorm V hV r, orthoNorm W hW s]
  nlinarith [hcrossle, hXpos]

end Hagi.Cortex
