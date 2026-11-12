/-
Copyright (c) 2025 FLYWHEEL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksandar Markovski
-/
import Hagi.External.Flywheel.FrobeniusNorm

/-!
# Strict diagonal-dominance rank lemma for sign-pattern matrices

A real square matrix with negative diagonal, nonnegative off-diagonal
entries and STRICTLY negative row sums acts injectively: the kernel of
`Matrix.mulVecLin` is trivial. The proof is the max-|x| argument and is
self-contained; Mathlib's Gershgorin lemmas
(`Matrix.det_ne_zero_of_sum_row_lt_diag`) require strict norm dominance
and do not cover this sign-aware, non-strict-off-diagonal form.

WHY STRICT ROW SUMS: with weak row sums (`≤ 0`) the statement is FALSE.
The graph-laplacian BELOW has negative
diagonal, nonnegative off-diagonal entries and row sums equal to zero,
yet kills the constant vector (see the example below). This matches the
addendum's own caveat that the Laplacian case only yields rank `n - 1`;
the weak/irreducible version is deferred and NOT claimed here.

Created: 2026-11-12
-/

open Matrix
open scoped BigOperators

set_option relaxedAutoImplicit false

namespace Hagi.External.Flywheel.NegDiagRank

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Max-|x| kernel argument: strict row sums force the kernel of `M` to
be trivial. -/
theorem neg_diag_pos_off_diag_kernel_trivial (M : Matrix n n ℝ)
    (hd : ∀ i, M i i < 0) (ho : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hr : ∀ i, ∑ j, M i j < 0) :
    ∀ x : n → ℝ, M *ᵥ x = 0 → x = 0 := by
  intro x hx
  classical
  -- argmax of |x|
  obtain ⟨i, _, himax⟩ := Finset.exists_max_image (Finset.univ) (fun j => |x j|)
    Finset.univ_nonempty
  -- off-diagonal entries of row i are nonneg
  have hoe : ∀ j ∈ Finset.univ.erase i, 0 ≤ M i j := by
    intro j hj
    exact ho i j (Ne.symm (fun h => (Finset.mem_erase.mp hj).1 h))
  -- row equation
  have hrow : ∑ j, M i j * x j = 0 := by
    have := congrFun hx i
    simpa [Matrix.mulVec, dotProduct] using this
  have hsum_erase : ∑ j ∈ Finset.univ.erase i, M i j = ∑ j, M i j - M i i := by
    have := Finset.add_sum_erase Finset.univ (fun j => M i j) (Finset.mem_univ i)
    linarith [this]
  have hsum_erase' : ∑ j ∈ Finset.univ.erase i, M i j * x j = -M i i * x i := by
    have := Finset.add_sum_erase Finset.univ (fun j => M i j * x j) (Finset.mem_univ i)
    linarith [this, hrow]
  -- off-diagonal row sum strictly below |M i i|
  have hS : ∑ j ∈ Finset.univ.erase i, M i j < -M i i := by
    rw [hsum_erase]; linarith [hr i]
  -- triangle chain: |M i i| * |x i| ≤ |x i| * S
  have hchain : (-M i i) * |x i| ≤ |x i| * ∑ j ∈ Finset.univ.erase i, M i j := by
    have h_abs_diag : |M i i * x i| = (-M i i) * |x i| := by
      rw [abs_mul, abs_of_neg (hd i)]
    have h_tri : |∑ j ∈ Finset.univ.erase i, M i j * x j| ≤
        ∑ j ∈ Finset.univ.erase i, M i j * |x j| := by
      calc |∑ j ∈ Finset.univ.erase i, M i j * x j| ≤
          ∑ j ∈ Finset.univ.erase i, |M i j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j ∈ Finset.univ.erase i, M i j * |x j| :=
            Finset.sum_congr rfl fun j hj => by
              rw [abs_mul, abs_of_nonneg (hoe j hj)]
    have h_max : ∑ j ∈ Finset.univ.erase i, M i j * |x j| ≤
        |x i| * ∑ j ∈ Finset.univ.erase i, M i j := by
      have hle : ∀ j ∈ Finset.univ.erase i, M i j * |x j| ≤ |x i| * M i j := by
        intro j hj
        rw [mul_comm (|x i|) (M i j)]
        exact mul_le_mul_of_nonneg_left (himax j (Finset.mem_univ j)) (hoe j hj)
      calc ∑ j ∈ Finset.univ.erase i, M i j * |x j| ≤
          ∑ j ∈ Finset.univ.erase i, |x i| * M i j :=
            Finset.sum_le_sum hle
        _ = |x i| * ∑ j ∈ Finset.univ.erase i, M i j := by rw [Finset.mul_sum]
    calc (-M i i) * |x i| = |M i i * x i| := h_abs_diag.symm
      _ = |∑ j ∈ Finset.univ.erase i, M i j * x j| := by
            rw [hsum_erase', neg_mul, abs_neg]
      _ ≤ ∑ j ∈ Finset.univ.erase i, M i j * |x j| := h_tri
      _ ≤ |x i| * ∑ j ∈ Finset.univ.erase i, M i j := h_max
  -- conclude |x i| = 0, hence x = 0
  rcases eq_or_lt_of_le (abs_nonneg (x i)) with h0 | hpos
  · funext j
    have hj := himax j (Finset.mem_univ j)
    have hle : |x j| ≤ 0 := by linarith [hj, h0, abs_nonneg (x j)]
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · exfalso
    have hstrict : |x i| * ∑ j ∈ Finset.univ.erase i, M i j < |x i| * (-M i i) :=
      mul_lt_mul_of_pos_left hS hpos
    have hlt := lt_of_le_of_lt hchain hstrict
    have hcomm : |x i| * (-M i i) = (-M i i) * |x i| := mul_comm _ _
    linarith

/-- Injectivity of multiplication by `M` under the strict sign-pattern
hypotheses of `neg_diag_pos_off_diag_kernel_trivial`. -/
theorem neg_diag_pos_off_diag_injective (M : Matrix n n ℝ)
    (hd : ∀ i, M i i < 0) (ho : ∀ i j, i ≠ j → 0 ≤ M i j)
    (hr : ∀ i, ∑ j, M i j < 0) :
    Function.Injective (Matrix.mulVecLin M) := by
  intro x y hxy
  have h : M *ᵥ (x - y) = 0 := by
    rw [← Matrix.mulVecLin_apply, map_sub, hxy, sub_self]
  have hker := neg_diag_pos_off_diag_kernel_trivial M hd ho hr _ h
  exact sub_eq_zero.mp hker

end Hagi.External.Flywheel.NegDiagRank

/-- The laplacian matrix (here on `Fin 2`) kills the constant vector
while meeting every weak (non-strict) row-sum hypothesis — negative
diagonal, nonnegative off-diagonal entries, row sums equal to zero.
Hence no injectivity lemma can hold under weak row sums, and only the
strict version is landed. -/
example :
    (Matrix.of fun i j : Fin 2 => if i = j then (-1 : ℝ) else 1) *ᵥ
      (fun _ => (1 : ℝ)) = fun _ => (0 : ℝ) := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.of_apply]
