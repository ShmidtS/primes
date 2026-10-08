/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# LatentAlign — the missing layer between factorization and
root/contrast merge (R242; source: LittleBit / LittleBit-2,
arXiv:2506.13771, PMLR v306 — latent geometry misalignment)

Two independently trained experts may carry FUNCTIONALLY
EQUIVALENT low-rank factorizations W = U Vᵀ whose latent
coordinates do not correspond: the second expert's basis can
be any orthogonal transform (rotation/sign flip) of the
first's. Averaging latents across experts then annihilates
columns — the latent-space face of `MergeCancellation` —
even though the expert MATRICES are equal or nearly equal.

LittleBit-2 fixes this with Internal Latent Rotation +
Joint-ITQ (a geometric preconditioner) BEFORE low-bit
quantization. For HAGI the merge pipeline becomes:

  factorize → latent-align → root/contrast → spectral
  compress → F3 merge

This module formalizes the three alignment facts that make
that pipeline sound:

* `rotated_factors_same_matrix` — INVARIANCE: the map
  (U, V) ↦ (U Q, V Q) over an orthogonal Q preserves W
  exactly — alignment costs nothing in function;
* `sign_flip_functional_equiv` — the canonical
  misalignment: per-column sign flips S (S² = 1) keep W
  identical while making the latents maximally opposed;
* `naive_latent_merge_kills_flipped` — THE CANCELLATION:
  averaging the latents of two functionally-equivalent
  experts zeroes exactly the flipped columns — the
  0.5·(U + U S) operator keeps only the unflipped block,
  so E_dev measured on raw latents overestimates the
  mergeable signal by the flipped share.
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

/-- **Functional equivalence under maximal latent
misalignment**: flipping the sign of latent column j in BOTH
factors leaves the matrix W = U Vᵀ untouched. -/
theorem sign_flip_functional_equiv
    (U V : Matrix (Fin d) (Fin r) ℝ) (s : Fin r → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    (U * signMatrix s hs) * (V * signMatrix s hs)ᵀ = U * Vᵀ := by
  rw [rotated_factors_same_matrix _ _ _ (signMatrix_orthogonal s hs)]

/-- **The latent cancellation**: averaging the latents of two
functionally-equivalent experts zeroes exactly the flipped
columns — the naive latent merge keeps only the unflipped
block and destroys the flipped disagreement outright. -/
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
