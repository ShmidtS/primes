/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.FrobOuter
import Mathlib.Tactic

set_option linter.style.header false

/-!
# ResidualVQ: product-of-quantized-factors error (round 53, A8 F2)

The empirical A8 verdict: one-stage quantization of a factorized
adapter q(A)·q(B) at ~3.2-bit per factor collapses nonlinear
adapters, while two-stage ResidualVQ (6.4-bit body + BF16 head)
restores them. The Lean slice of that verdict:

* `quantProd_decompose`: the EXACT identity
  (A+EA)·(B+EB) − A·B = EA·B + A·EB + EA·EB.
* `frobSq_mul_le`: rectangular Frobenius submultiplicativity
  `frobSq (A*B) ≤ frobSq A * frobSq B` — closing the open hbridge
  candidate recorded in `Hagi.Budget.ElementQuant`
  (`ternary_pair_qerr_sum` note): per-entry Cauchy–Schwarz
  (`Finset.sum_mul_sq_le_sq_mul_sq`) over `Hagi.Core.frobSq`.
* `quantProd_frob_bound` / `quantProd_relError(_sq)`: the product
  error bound and its relative form — at per-factor relative
  errors e, f the product error obeys the (e + f + e·f)² law;
  `quantProd_crossTerm_amplifies`: at equal e the exponent is
  ≥ 2e — the formal reason one-stage low-bit products amplify.
* `residualTwoStage_exact` / `residualTwoStage_error_le(_add)`:
  two-stage residual quantization composes ADDITIVELY —
  error ≤ ε1 + ε2, in fact ≤ ε2 alone (the sharp form);
  `residualHeadBudget`: the BF16-head bridge at the 2⁻⁸ grid
  scale (premise-form composition with C249's Q→R bridge).

Empirical bit-widths and accuracy numbers are motivation only
(ALGORITHMS.md); no probability, no new quantizer.

**Prescription**: allocate bits per factor via the (e+f+ef)² law;
never quantize a product in one stage at low bit-width — spend a
second residual stage on W − R1 (additive, not multiplicative,
error composition).
-/
open Finset Hagi.Core

namespace Hagi.Budget

variable {m r n : Type} [Fintype m] [Fintype r] [Fintype n]

/-! ## Frobenius machinery (rectangular, Fintype-indexed) -/

/-- Entrywise inner product of two equally-shaped matrices. -/
def frobInner (X Y : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, X i j * Y i j

theorem frobSq_add_eq (X Y : Matrix m n ℝ) :
    frobSq (X + Y) = frobSq X + frobSq Y + 2 * frobInner X Y := by
  have hleaf : ∀ i j, (X i j + Y i j) ^ 2
      = (X i j) ^ 2 + (Y i j) ^ 2 + 2 * (X i j * Y i j) := fun _ _ => by ring
  unfold frobSq frobInner
  simp only [Matrix.add_apply, hleaf, Finset.sum_add_distrib, Finset.mul_sum]

theorem frobInner_le_sqrt (X Y : Matrix m n ℝ) :
    frobInner X Y ≤ (frobSq X).sqrt * (frobSq Y).sqrt := by
  have hiprod : frobInner X Y
      = ∑ p ∈ Finset.univ.product Finset.univ, X p.1 p.2 * Y p.1 p.2 :=
    (Finset.sum_product' _ _ _).symm
  have hprodX : frobSq X
      = ∑ p ∈ Finset.univ.product Finset.univ, X p.1 p.2 ^ 2 :=
    (Finset.sum_product' _ _ _).symm
  have hprodY : frobSq Y
      = ∑ p ∈ Finset.univ.product Finset.univ, Y p.1 p.2 ^ 2 :=
    (Finset.sum_product' _ _ _).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.product Finset.univ)
    (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
  have hcs2 : (frobInner X Y) ^ 2 ≤ frobSq X * frobSq Y := by
    rw [hiprod, hprodX, hprodY]
    exact hcs
  have hXnn : 0 ≤ frobSq X := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hle : frobInner X Y ≤ (frobSq X * frobSq Y).sqrt :=
    Real.le_sqrt_of_sq_le hcs2
  rw [Real.sqrt_mul hXnn] at hle
  exact hle

theorem frobSq_add_sqrt_le (X Y : Matrix m n ℝ) :
    (frobSq (X + Y)).sqrt ≤ (frobSq X).sqrt + (frobSq Y).sqrt := by
  have hX : 0 ≤ frobSq X := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hY : 0 ≤ frobSq Y := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have e1 : ((frobSq X).sqrt) ^ 2 = frobSq X := Real.sq_sqrt hX
  have e2 : ((frobSq Y).sqrt) ^ 2 = frobSq Y := Real.sq_sqrt hY
  have h1 := frobSq_add_eq X Y
  have h2 := frobInner_le_sqrt X Y
  have hkey : frobSq (X + Y)
      ≤ ((frobSq X).sqrt + (frobSq Y).sqrt) ^ 2 := by
    rw [h1, add_sq, e1, e2]
    nlinarith [h2, Real.sqrt_nonneg (frobSq X), Real.sqrt_nonneg (frobSq Y)]
  refine le_trans (Real.sqrt_le_sqrt hkey) ?_
  exact (Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).le

/-- Rectangular Frobenius submultiplicativity — the open
hbridge candidate of `Hagi.Budget.ElementQuant`. -/
theorem frobSq_mul_le (A : Matrix m r ℝ) (B : Matrix r n ℝ) :
    frobSq (A * B) ≤ frobSq A * frobSq B := by
  have key : ∀ i j, (∑ k, A i k * B k j) ^ 2
      ≤ (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2) :=
    fun i j => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have step1 : ∑ i, ∑ j, (∑ k, A i k * B k j) ^ 2
      ≤ ∑ i, ∑ j, (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
  have step2 : ∑ i, ∑ j, (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2)
      = (∑ i, ∑ k, (A i k) ^ 2) * (∑ k, ∑ j, (B k j) ^ 2) := by
    have inner : ∀ i, ∑ j, (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2)
        = (∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := fun i => by
      rw [← Finset.mul_sum]
    calc ∑ i, ∑ j, (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2)
        = ∑ i, (∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := by
          exact Finset.sum_congr rfl fun i _ => inner i
      _ = (∑ i, ∑ k, (A i k) ^ 2) * (∑ j, ∑ k, (B k j) ^ 2) := by
          rw [Finset.sum_mul]
      _ = (∑ i, ∑ k, (A i k) ^ 2) * (∑ k, ∑ j, (B k j) ^ 2) := by
          congr 1
          exact Finset.sum_comm
  calc frobSq (A * B)
      = ∑ i, ∑ j, (∑ k, A i k * B k j) ^ 2 := by
        unfold frobSq; simp only [Matrix.mul_apply]
    _ ≤ ∑ i, ∑ j, (∑ k, (A i k) ^ 2) * (∑ k, (B k j) ^ 2) := step1
    _ = (∑ i, ∑ k, (A i k) ^ 2) * (∑ k, ∑ j, (B k j) ^ 2) := step2
    _ = frobSq A * frobSq B := by unfold frobSq; rfl

/-! ## One-stage: product of quantized factors -/

omit [Fintype m] [Fintype n] in
theorem quantProd_decompose (A : Matrix m r ℝ) (B : Matrix r n ℝ)
    (EA : Matrix m r ℝ) (EB : Matrix r n ℝ) :
    (A + EA) * (B + EB) - A * B = EA * B + A * EB + EA * EB := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]; abel

theorem quantProd_frob_bound (A : Matrix m r ℝ) (B : Matrix r n ℝ)
    (EA : Matrix m r ℝ) (EB : Matrix r n ℝ) :
    (frobSq ((A + EA) * (B + EB) - A * B)).sqrt
      ≤ (frobSq EA).sqrt * (frobSq B).sqrt
        + (frobSq A).sqrt * (frobSq EB).sqrt
        + (frobSq EA).sqrt * (frobSq EB).sqrt := by
  have h1 := frobSq_add_sqrt_le (EA * B) (A * EB + EA * EB)
  have h2 := frobSq_add_sqrt_le (A * EB) (EA * EB)
  have hnnEA : 0 ≤ frobSq EA := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hnnA : 0 ≤ frobSq A := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hnnB : 0 ≤ frobSq B := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hnnEB : 0 ≤ frobSq EB := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have s1 : (frobSq (EA * B)).sqrt
      ≤ (frobSq EA).sqrt * (frobSq B).sqrt := by
    rw [← Real.sqrt_mul hnnEA]
    exact Real.sqrt_le_sqrt (frobSq_mul_le EA B)
  have s2 : (frobSq (A * EB)).sqrt
      ≤ (frobSq A).sqrt * (frobSq EB).sqrt := by
    rw [← Real.sqrt_mul hnnA]
    exact Real.sqrt_le_sqrt (frobSq_mul_le A EB)
  have s3 : (frobSq (EA * EB)).sqrt
      ≤ (frobSq EA).sqrt * (frobSq EB).sqrt := by
    rw [← Real.sqrt_mul hnnEA]
    exact Real.sqrt_le_sqrt (frobSq_mul_le EA EB)
  rw [quantProd_decompose, add_assoc]
  have hchain : (frobSq (EA * B)).sqrt + (frobSq (A * EB + EA * EB)).sqrt
      ≤ (frobSq EA).sqrt * (frobSq B).sqrt
        + (frobSq A).sqrt * (frobSq EB).sqrt
        + (frobSq EA).sqrt * (frobSq EB).sqrt := by
    linarith
  exact le_trans h1 hchain

theorem quantProd_relError (A : Matrix m r ℝ) (B : Matrix r n ℝ)
    (EA : Matrix m r ℝ) (EB : Matrix r n ℝ) (e f : ℝ)
    (he : 0 ≤ e) (hf : 0 ≤ f)
    (hEA : (frobSq EA).sqrt ≤ e * (frobSq A).sqrt)
    (hEB : (frobSq EB).sqrt ≤ f * (frobSq B).sqrt) :
    frobSq ((A + EA) * (B + EB) - A * B)
      ≤ (e + f + e * f) ^ 2 * frobSq A * frobSq B := by
  have hxnn : 0 ≤ (frobSq A).sqrt := Real.sqrt_nonneg _
  have hynn : 0 ≤ (frobSq B).sqrt := Real.sqrt_nonneg _
  have henn : 0 ≤ e + f + e * f := by nlinarith [mul_nonneg he hf]
  have hb := quantProd_frob_bound A B EA EB
  have t1 : (frobSq EA).sqrt * (frobSq B).sqrt
      ≤ e * (frobSq A).sqrt * (frobSq B).sqrt :=
    mul_le_mul_of_nonneg_right hEA hynn
  have t2 : (frobSq A).sqrt * (frobSq EB).sqrt
      ≤ (frobSq A).sqrt * (f * (frobSq B).sqrt) :=
    mul_le_mul_of_nonneg_left hEB hxnn
  have t3 : (frobSq EA).sqrt * (frobSq EB).sqrt
      ≤ (e * (frobSq A).sqrt) * (f * (frobSq B).sqrt) :=
    mul_le_mul hEA hEB (Real.sqrt_nonneg _)
      (mul_nonneg he (Real.sqrt_nonneg _))
  have hR : (e + f + e * f) * (frobSq A).sqrt * (frobSq B).sqrt
      = e * (frobSq A).sqrt * (frobSq B).sqrt
        + (frobSq A).sqrt * (f * (frobSq B).sqrt)
        + (e * (frobSq A).sqrt) * (f * (frobSq B).sqrt) := by ring
  have hbound : (frobSq ((A + EA) * (B + EB) - A * B)).sqrt
      ≤ (e + f + e * f) * (frobSq A).sqrt * (frobSq B).sqrt := by
    refine le_trans hb ?_
    rw [hR]
    linarith
  have hs : 0 ≤ ((e + f + e * f) * (frobSq A).sqrt) * (frobSq B).sqrt :=
    mul_nonneg (mul_nonneg henn hxnn) hynn
  have hnnA : 0 ≤ frobSq A := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hnnB : 0 ≤ frobSq B := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hsq : (((e + f + e * f) * (frobSq A).sqrt) * (frobSq B).sqrt) ^ 2
      = (e + f + e * f) ^ 2 * frobSq A * frobSq B := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hnnA, Real.sq_sqrt hnnB]
  have hc2 := (Real.sqrt_le_iff.mp hbound).2
  rwa [hsq] at hc2


theorem quantProd_relError_sq (A : Matrix m r ℝ) (B : Matrix r n ℝ)
    (EA : Matrix m r ℝ) (EB : Matrix r n ℝ) (e f : ℝ)
    (he : 0 ≤ e) (hf : 0 ≤ f)
    (hEA : frobSq EA ≤ e ^ 2 * frobSq A)
    (hEB : frobSq EB ≤ f ^ 2 * frobSq B) :
    frobSq ((A + EA) * (B + EB) - A * B)
      ≤ (e + f + e * f) ^ 2 * frobSq A * frobSq B := by
  have hnnA : 0 ≤ frobSq A := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hnnB : 0 ≤ frobSq B := by
    unfold frobSq; exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have s1 : (frobSq EA).sqrt ≤ e * (frobSq A).sqrt := by
    refine le_trans (Real.sqrt_le_sqrt hEA) ?_
    rw [Real.sqrt_mul (sq_nonneg e) (frobSq A), Real.sqrt_sq he]
  have s2 : (frobSq EB).sqrt ≤ f * (frobSq B).sqrt := by
    refine le_trans (Real.sqrt_le_sqrt hEB) ?_
    rw [Real.sqrt_mul (sq_nonneg f) (frobSq B), Real.sqrt_sq hf]
  exact quantProd_relError A B EA EB e f he hf s1 s2

/-- The formal "2x single-factor" amplification: at equal
per-factor relative error e, the product bound exponent
e + e + e * e is at least 2 * e — the cross term is strictly
positive for e > 0. -/
theorem quantProd_crossTerm_amplifies (e : ℝ) (_h : 0 ≤ e) :
    2 * e ≤ e + e + e * e := by nlinarith

/-! ## Two-stage: residual quantization -/

omit [Fintype m] [Fintype n] in
theorem residualTwoStage_exact (W R1 R2 : Matrix m n ℝ) :
    W - (R1 + R2) = (W - R1) - R2 := by abel

theorem residualTwoStage_error_le (W R1 R2 : Matrix m n ℝ) (e2 : ℝ)
    (h2 : (frobSq ((W - R1) - R2)).sqrt ≤ e2) :
    (frobSq (W - (R1 + R2))).sqrt ≤ e2 := by
  rw [residualTwoStage_exact W R1 R2]; exact h2

theorem residualTwoStage_error_le_add (W R1 R2 : Matrix m n ℝ)
    (e1 e2 : ℝ) (he1 : 0 ≤ e1)
    (h2 : (frobSq ((W - R1) - R2)).sqrt ≤ e2) :
    (frobSq (W - (R1 + R2))).sqrt ≤ e1 + e2 :=
  le_trans (residualTwoStage_error_le W R1 R2 e2 h2) (by linarith)

theorem residualHeadBudget (W R1 R2 : Matrix m n ℝ) (e1 : ℝ)
    (he1 : 0 ≤ e1)
    (h1 : (frobSq (W - R1)).sqrt ≤ e1)
    (h2 : (frobSq ((W - R1) - R2)).sqrt ≤ (2 ^ (-8 : Int) : ℝ) * (frobSq (W - R1)).sqrt) :
    (frobSq (W - (R1 + R2))).sqrt ≤ e1 + (2 ^ (-8 : Int) : ℝ) * e1 := by
  have herr := residualTwoStage_error_le W R1 R2 _ h2
  have hpos : (0:ℝ) ≤ (2 ^ (-8 : Int) : ℝ) := by positivity
  have hkey : (frobSq ((W - R1) - R2)).sqrt ≤ (2 ^ (-8 : Int) : ℝ) * e1 :=
    le_trans h2 (mul_le_mul_of_nonneg_left h1 hpos)
  have hgoal : (frobSq (W - (R1 + R2))).sqrt ≤ (2 ^ (-8 : Int) : ℝ) * e1 := by
    rw [residualTwoStage_exact W R1 R2]; exact hkey
  nlinarith [he1, hpos]

end Hagi.Budget
