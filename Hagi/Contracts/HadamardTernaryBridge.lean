/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Hadamard
import Hagi.Runtime.TernaryExact
import Hagi.Model.CEGroupedScale
set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# The Hadamard-incoherence ↔ ternary-quantization bridge

Motivated by QuIP# (Theorem 4.1 incoherence quantization), this
module formalizes the MATH, not the paper: how μ-incoherence of the
Hadamard transform output kills the ternary saturation tail, and how
orthogonality of `H` leaves logits exactly invariant
pre-quantization.

Honesty note (pinned by `hadamard_not_universally_incoherent`): the
Hadamard matrix does NOT universally suppress the ∞-norm — there are
vectors with `‖Hx‖∞ = ‖x‖₂` (effective μ = √d > 1). μ-incoherence is
always a PREMISE here, never a conclusion of Hadamard structure
alone.
-/

open scoped Matrix Classical
open Hagi.Core Hagi.Runtime Hagi.Model Hagi.Model.CEGroupedScale

namespace Hagi.Contracts.HadamardTernaryBridge

private theorem card_finPi_zmod (k : ℕ) :
    Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  simp

/-- The Hadamard image `H x` reindexed onto `Fin (2 ^ k)`, so the
`Fin n`-indexed ternary carrier (`satTail`, the `qTern` error split)
applies. The reindex is an arbitrary but fixed bijection; the
`satTail = 0` statements below are reindex-independent (the filter
is empty). -/
noncomputable def hadamardImage {k : ℕ} (x : (Fin k → ZMod 2) → ℝ) :
    Fin (2 ^ k) → ℝ :=
  fun i => (hadamardOrthonormal k *ᵥ x)
    ((Fintype.equivFinOfCardEq (card_finPi_zmod k)).symm i)

/-! ## Theorem 1: μ-incoherence kills the saturation tail -/

/-- **Theorem 1 (premise form).** If `‖x‖₂ ≤ s·√d` (with `d = 2^k`,
`s > 0`) and the transform output is μ-incoherent with `0 ≤ μ ≤ 1`,
i.e. `‖Hx‖∞ ≤ μ·‖x‖₂/√d`, then every coordinate of `Hx` lies in the
ternary range `|y| ≤ 3s/2`, so the saturation tail of the reindexed
image vanishes. The μ-incoherence bound is a PREMISE: the Hadamard
matrix does not universally suppress the ∞-norm (see
`hadamard_not_universally_incoherent`). -/
theorem hadamard_satTail_zero_of_l2_bound {k : ℕ} (s μ : ℝ)
    (x : (Fin k → ZMod 2) → ℝ) (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1)
    (hl2 : Real.sqrt (∑ i, x i * x i) ≤ s * Real.sqrt ((2 : ℝ) ^ k))
    (hinc : ∀ j, |(hadamardOrthonormal k *ᵥ x) j| ≤
      μ * Real.sqrt (∑ i, x i * x i) / Real.sqrt ((2 : ℝ) ^ k)) :
    (∀ j, ternInRange s ((hadamardOrthonormal k *ᵥ x) j))
      ∧ satTail s (hadamardImage x) = 0 := by
  have hdpos : 0 < Real.sqrt ((2 : ℝ) ^ k) := Real.sqrt_pos.mpr (by positivity)
  have hall : ∀ j, ternInRange s ((hadamardOrthonormal k *ᵥ x) j) := by
    intro j
    have h1 := hinc j
    have h2 : μ * Real.sqrt (∑ i, x i * x i) / Real.sqrt ((2 : ℝ) ^ k) ≤ s := by
      have hc : (μ / Real.sqrt ((2 : ℝ) ^ k)) * (s * Real.sqrt ((2 : ℝ) ^ k)) = s * μ := by
        field_simp
      have hμn : 0 ≤ μ / Real.sqrt ((2 : ℝ) ^ k) := div_nonneg hμ0 hdpos.le
      calc μ * Real.sqrt (∑ i, x i * x i) / Real.sqrt ((2 : ℝ) ^ k)
          = (μ / Real.sqrt ((2 : ℝ) ^ k)) * Real.sqrt (∑ i, x i * x i) := by ring
        _ ≤ (μ / Real.sqrt ((2 : ℝ) ^ k)) * (s * Real.sqrt ((2 : ℝ) ^ k)) :=
            mul_le_mul_of_nonneg_left hl2 hμn
        _ = s * μ := hc
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left hμ (le_of_lt hs)
        _ = s := by ring
    have h3 : |(hadamardOrthonormal k *ᵥ x) j| ≤ s := le_trans h1 h2
    unfold ternInRange
    calc |(hadamardOrthonormal k *ᵥ x) j| ≤ s := h3
      _ ≤ 3 * s / 2 := by linarith
  refine ⟨hall, ?_⟩
  unfold satTail
  rw [Finset.sum_eq_zero]
  intro i hi
  have hin : ternInRange s (hadamardImage x i) :=
    hall ((Fintype.equivFinOfCardEq (card_finPi_zmod k)).symm i)
  exact absurd hin (Finset.mem_filter.mp hi).2

/-- **Theorem 1, quantitative half.** Under the same premises, the
total squared quantization error of the ternary quantizer on the
Hadamard image is at most `d · (s/2)²` with `d = 2^k`: pure
half-step rounding, no saturation term. -/
theorem hadamard_quant_error_le_of_l2_bound {k : ℕ} (s μ : ℝ)
    (x : (Fin k → ZMod 2) → ℝ) (hs : 0 < s) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1)
    (hl2 : Real.sqrt (∑ i, x i * x i) ≤ s * Real.sqrt ((2 : ℝ) ^ k))
    (hinc : ∀ j, |(hadamardOrthonormal k *ᵥ x) j| ≤
      μ * Real.sqrt (∑ i, x i * x i) / Real.sqrt ((2 : ℝ) ^ k)) :
    ∑ i, (hadamardImage x i - qTern s (hadamardImage x i)) ^ 2
      ≤ (2 ^ k : ℝ) * (s / 2) ^ 2 := by
  have h1 := (hadamard_satTail_zero_of_l2_bound s μ x hs hμ0 hμ hl2 hinc).2
  have h2 := ternary_split_le s hs (hadamardImage x)
  rw [h1] at h2
  simpa using h2

/-! ## The generic helper -/

/-- If every coordinate is in ternary range, the saturation tail is
zero (standalone extraction; used by the penalty reduction). -/
theorem satTail_eq_zero_of_forall_ternInRange {n : ℕ} (s : ℝ) (w : Fin n → ℝ)
    (hall : ∀ i, ternInRange s (w i)) : satTail s w = 0 := by
  unfold satTail
  rw [Finset.sum_eq_zero]
  intro i hi
  exact absurd (hall i) (Finset.mem_filter.mp hi).2

/-! ## Negative example: no universal incoherence -/

/-- **Pinned counterexample (universality denial).** The Hadamard
matrix does NOT universally suppress the ∞-norm: for `k = 1`, the
constant vector `x = (2, 2)` has first transform coordinate
`4/√2 = 2√2 ≈ 2.83` while `‖x‖₂ = 2√2`, i.e. `‖Hx‖∞ = ‖x‖₂`
(effective μ = √d = √2 > 1). At ternary scale `s = 1` the coordinate
`2√2 > 3/2` saturates: `¬ternInRange 1 (H x 0)`, so without the
μ/l² premises the saturation tail is nonzero. -/
theorem hadamard_not_universally_incoherent : ¬ ternInRange 1
    ((hadamardOrthonormal 1 *ᵥ (fun _ : Fin 1 → ZMod 2 => (2 : ℝ)))
      (fun _ => (0 : ZMod 2))) := by
  have hval : ((hadamardOrthonormal 1 *ᵥ (fun _ : Fin 1 → ZMod 2 => (2 : ℝ)))
      (fun _ => (0 : ZMod 2))) = 4 / Real.sqrt 2 := by
    unfold hadamardOrthonormal hadamardReal Matrix.mulVec
    simp [dotProduct, sylvester, chi2, Fin.isValue]
    field_simp
    norm_num
  have hgt : (3 : ℝ) * 1 / 2 < 4 / Real.sqrt 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2)]
    have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  have habs : |4 / Real.sqrt 2| = 4 / Real.sqrt 2 := abs_of_nonneg (by positivity)
  unfold ternInRange
  rw [hval, habs]
  exact not_le.mpr hgt

/-! ## Theorem 2: logits invariance and the penalty reduction -/

/-- The orthonormal Sylvester matrix is symmetric: `Hᵀ = H`. -/
theorem hadamardOrthonormal_transpose (k : ℕ) :
    (hadamardOrthonormal k)ᵀ = hadamardOrthonormal k := by
  unfold hadamardOrthonormal hadamardReal
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply, sylvester_apply]
  rw [congrArg chi2 (Finset.sum_congr rfl fun l _ => mul_comm (j l) (i l))]

/-- **Theorem 2, part (a): logits are invariant pre-quantization.**
For any weight matrix `W`, pre-multiplying the input by the
orthonormal `H` and post-compensating the weights (`W·Hᵀ`) leaves
every logit unchanged: `(W·Hᵀ) *ᵥ (H *ᵥ x) = W *ᵥ x`. This is pure
matrix associativity plus `Hᵀ·H = 1` (symmetry + orthonormality);
no quantization has happened yet — after quantization of `H x` the
identity is approximate, governed by Theorem 1's error bound. -/
theorem hadamard_logits_invariance_mulVec {k : ℕ} {m : Type} [Fintype m]
    (W : Matrix m (Fin k → ZMod 2) ℝ)
    (x : (Fin k → ZMod 2) → ℝ) :
    (W * (hadamardOrthonormal k)ᵀ) *ᵥ (hadamardOrthonormal k *ᵥ x)
      = W *ᵥ x := by
  have hassoc : ((W * (hadamardOrthonormal k)ᵀ) *ᵥ (hadamardOrthonormal k *ᵥ x))
      = ((W * (hadamardOrthonormal k)ᵀ) * hadamardOrthonormal k) *ᵥ x := by
    simp
  have hsymm := hadamardOrthonormal_transpose k
  have hHT : (hadamardOrthonormal k)ᵀ * hadamardOrthonormal k = 1 := by
    have h2 := hadamardOrthonormal_mul_transpose (k := k)
    rw [hsymm] at h2
    rw [hsymm]
    exact h2
  rw [hassoc, Matrix.mul_assoc W, hHT, Matrix.mul_one]

/-- **Theorem 2, part (b): the penalty reduction.** If every raw block
weight is in ternary range at the block's dyadic level, the saturation
tail inside `groupStructuralPenalty` vanishes, and the certified local
objective `blockPenalty` (the min of the observed and structural
branches) is at most the pure in-range rounding term
`2 · featureAbsSum X · √5 · lvl / 2`. -/
theorem blockPenalty_le_of_all_ternInRange {G : ℕ} {V : Type} [Fintype V]
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (k : DyadicScaleCode)
    (hall : ∀ i, ternInRange (dyadicLevel k) (blockWeights e w g i)) :
    blockPenalty e X w g k
      ≤ 2 * featureAbsSum X * Real.sqrt 5 * dyadicLevel k / 2 := by
  have hs0 : satTail (dyadicLevel k) (blockWeights e w g) = 0 :=
    satTail_eq_zero_of_forall_ternInRange _ _ hall
  have hred : groupStructuralPenalty e X w g k
      = 2 * featureAbsSum X * Real.sqrt 5 * dyadicLevel k / 2 := by
    unfold groupStructuralPenalty
    rw [hs0, add_zero]
    have hpos : 0 < dyadicLevel k := dyadicLevel_pos k
    have h5 : Real.sqrt (5 * (dyadicLevel k / 2) ^ 2)
        = Real.sqrt 5 * dyadicLevel k / 2 := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 5), Real.sqrt_sq_eq_abs,
        abs_of_pos (by linarith : 0 < dyadicLevel k / 2)]
      ring
    rw [h5]
    ring
  unfold blockPenalty
  rw [hred]
  exact min_le_right _ _

/-- **Theorem 2 (combined bridge).** Under the Theorem-1 premises on a
source `x` (dimension `2^kk`, scale `s = dyadicLevel k`), a block whose
raw weights are the Hadamard image of `x` has every weight
ternary-in-range (Theorem 1 pointwise), so the certified local
objective collapses to the pure rounding bound — while logits computed
with the compensated weights `W·Hᵀ` on `H x` equal the original `W *ᵥ x`
exactly, pre-quantization. -/
theorem hadamard_ce_blockPenalty_reduction {kk G : ℕ} {V : Type} [Fintype V]
    (μ : ℝ) (x : (Fin kk → ZMod 2) → ℝ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1)
    (k : DyadicScaleCode)
    (hl2 : Real.sqrt (∑ i, x i * x i)
      ≤ dyadicLevel k * Real.sqrt ((2 : ℝ) ^ kk))
    (hinc : ∀ j, |(hadamardOrthonormal kk *ᵥ x) j| ≤
      μ * Real.sqrt (∑ i, x i * x i) / Real.sqrt ((2 : ℝ) ^ kk))
    (e : (Fin G × Fin 5) ≃ Fin (5 * G))
    (π : Fin 5 → (Fin kk → ZMod 2))
    (X : Matrix V (Fin (5 * G)) ℝ)
    (w : EuclideanSpace ℝ (Fin (5 * G))) (g : Fin G)
    (hwt : blockWeights e w g = fun i => (hadamardOrthonormal kk *ᵥ x) (π i))
    (W : Matrix V (Fin kk → ZMod 2) ℝ) :
    (W * (hadamardOrthonormal kk)ᵀ) *ᵥ (hadamardOrthonormal kk *ᵥ x) = W *ᵥ x
      ∧ blockPenalty e X w g k
        ≤ 2 * featureAbsSum X * Real.sqrt 5 * dyadicLevel k / 2 := by
  refine ⟨hadamard_logits_invariance_mulVec W x, ?_⟩
  have hall : ∀ i, ternInRange (dyadicLevel k) (blockWeights e w g i) := by
    intro i
    rw [hwt]
    exact (hadamard_satTail_zero_of_l2_bound (dyadicLevel k) μ x
      (dyadicLevel_pos k) hμ0 hμ hl2 hinc).1 (π i)
  exact blockPenalty_le_of_all_ternInRange e X w g k hall

end Hagi.Contracts.HadamardTernaryBridge
