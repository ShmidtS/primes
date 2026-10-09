/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# LatentAlign — latent misalignment between factorized experts

Two independently trained experts may carry functionally
equivalent factorizations `W = U * Vᵀ` whose latent
coordinates differ by an orthogonal transform. (source:
arXiv:2506.13771)

* `rotated_factors_same_matrix` — the map `(U, V) ↦ (U * Q,
  V * Q)` with orthogonal `Q` preserves the product exactly.
* `sign_flip_functional_equiv` — per-column sign flips keep
  `U * Vᵀ` identical while flipping the latents.
* `naive_latent_merge_kills_flipped` — averaging the latents
  of two functionally-equivalent experts zeroes exactly the
  flipped columns.
-/

open scoped BigOperators
open Matrix

namespace Hagi.Latent

variable {d r : ℕ}

/-- Orthogonality hypothesis in the form the cancellation
arguments need (square real Q with Q Qᵀ = 1). -/
def IsOrthogonal (Q : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  Q * Qᵀ = 1

/-- **Alignment is free**: rotating both factors by the same
orthogonal Q preserves the product exactly. -/
theorem rotated_factors_same_matrix
    (U : Matrix (Fin d) (Fin r) ℝ) (V : Matrix (Fin d) (Fin r) ℝ)
    (Q : Matrix (Fin r) (Fin r) ℝ) (hQ : IsOrthogonal Q) :
    (U * Q) * (V * Q)ᵀ = U * Vᵀ := by
  rw [Matrix.mul_assoc, Matrix.transpose_mul, ← Matrix.mul_assoc Q Qᵀ Vᵀ,
    hQ, Matrix.one_mul]

/-- A per-column sign matrix: diagonal ±1. -/
def signMatrix (s : Fin r → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    Matrix (Fin r) (Fin r) ℝ := Matrix.diagonal s

theorem signMatrix_orthogonal (s : Fin r → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    IsOrthogonal (signMatrix s hs) := by
  unfold IsOrthogonal signMatrix
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · have := hs i
    rcases this with h | h <;> simp [h]
  · simp [hij]

/-- Sign squares to one: S * S = 1. -/
theorem signMatrix_mul_self (s : Fin r → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    signMatrix s hs * signMatrix s hs = 1 := by
  unfold signMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · have := hs i
    rcases this with h | h <;> simp [h]
  · simp [hij]

/-- Flipping the sign of latent columns in both factors
leaves the product `U * Vᵀ` untouched. -/
theorem sign_flip_functional_equiv
    (U V : Matrix (Fin d) (Fin r) ℝ) (s : Fin r → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    (U * signMatrix s hs) * (V * signMatrix s hs)ᵀ = U * Vᵀ := by
  rw [rotated_factors_same_matrix _ _ _ (signMatrix_orthogonal s hs)]

/-- Averaging `U` with its sign-flipped copy zeroes exactly
the flipped columns: the mean maps `Pi.single j 1` to `0` for
every `j` with `s j = -1`. -/
theorem naive_latent_merge_kills_flipped
    (U : Matrix (Fin d) (Fin r) ℝ) (s : Fin r → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (j : Fin r) (hj : s j = -1) :
    ((2:ℝ)⁻¹ • (U + U * signMatrix s hs)) *ᵥ (Pi.single j (1:ℝ)) = 0 := by
  set e : Fin r → ℝ := Pi.single j (1:ℝ) with he
  have hflip : (U * signMatrix s hs) *ᵥ e = -(U *ᵥ e) := by
    rw [← Matrix.mulVec_mulVec]
    have hdiag : (signMatrix s hs) *ᵥ e = s j • e := by
      unfold signMatrix
      funext i
      by_cases hij : i = j
      · subst hij
        simp [Matrix.mulVec, Matrix.diagonal_apply, he,
          Pi.single_apply, mul_one]
      · rw [Matrix.mulVec]
        simp [he, Pi.single_apply, hij]
    rw [hdiag, hj, Matrix.mulVec_smul]
    simp
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, hflip]
  simp




end Hagi.Latent
