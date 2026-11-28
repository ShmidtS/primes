/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.FrobOuter
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option linter.style.header false

/-!
# ResidualVQ: product-of-quantized-factors error

The empirical verdict: one-stage quantization of a factorized
adapter q(A)·q(B) at ~3.2-bit per factor collapses nonlinear
adapters, while two-stage ResidualVQ (6.4-bit body + BF16 head)
restores them. The Lean slice of that verdict:

* `quantProd_decompose`: the EXACT identity
  (A+EA)·(B+EB) − A·B = EA·B + A·EB + EA·EB.
* `frobSq_mul_le`: rectangular Frobenius submultiplicativity
  `frobSq (A*B) ≤ frobSq A * frobSq B` — the rectangular bridge needed by
  `Hagi.Budget.ElementQuant` (`ternary_pair_qerr_sum`): per-entry
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
  scale (premise-form composition with the Q→R bridge).

Empirical bit-widths and accuracy numbers are motivation only
(ALGORITHMS.md); no probability, no new quantizer.

**Prescription**: never quantize a product in one stage at low
bit-width — spend a second residual stage on W − R1 (additive, not
multiplicative, error composition).
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

/-- Rectangular Frobenius submultiplicativity. -/
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

variable {n : ℕ}

/-- Взвешенная ошибка строки при фиксированных уровнях `q` и весах важности `I`
(HAGI_v2 fisher_opt, candidates `s_j = Σ I w q / Σ I q²`). -/
noncomputable def fisherErr (I w q : Fin n → ℝ) (s : ℝ) : ℝ := ∑ i, I i * (w i - s * q i) ^ 2
/-- Оптимальный масштаб для фиксированных уровней — взвешенный МНК:
`s* = Σ I w q / Σ I q²`; при `Σ I q² > 0` ошибка в оптимуме минимальна,
`E(s) − E(s*) = D·(s − s*)²`. -/
theorem fisher_optimal_scale (I w q : Fin n → ℝ) (hD : 0 < ∑ i, I i * q i ^ 2) :
    ∀ s, fisherErr I w q ((∑ i, I i * w i * q i) / ∑ i, I i * q i ^ 2) ≤ fisherErr I w q s := by
  set D := ∑ i, I i * q i ^ 2 with hDdef
  set N := ∑ i, I i * w i * q i with hNdef
  intro s
  have expand (s : ℝ) : fisherErr I w q s = (∑ i, I i * w i ^ 2) - 2 * s * N + s ^ 2 * D := by
    unfold fisherErr N D
    symm
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have hsq : 0 ≤ D * (s - N / D) ^ 2 := mul_nonneg (by unfold D; positivity) (sq_nonneg _)
  have hDne : D ≠ 0 := ne_of_gt hD
  have hkey : fisherErr I w q s - fisherErr I w q (N / D) = D * (s - N / D) ^ 2 := by
    rw [expand s, expand (N / D)]; field_simp [hDne]; ring
  linarith

/-- Обмен одним битом при фиксированном бюджете `b₁ + b₂` (ошибка ∝ `4^{-b}`):
перенос бита от строки 2 к строке 1 (`b₁ + 1`, `b₂ − 1`) снижает суммарную
ошибку тогда и только тогда, когда `4·y < x` — вклад строки 1 больше вклада
строки 2 более чем в 4 раза. Обмен прекращается, когда вклады отличаются
менее чем в 4 раза: дискретное обратное water-filling (HAWQ-V2: вклад —
след Гессе). -/
theorem bit_swap_improves_iff (x y : ℝ) :
    x / 4 + y * 4 < x + y ↔ 4 * y < x := by
  constructor <;> intro h <;> linarith

/-- Стационарность распределения стадий: если вклад каждой строки со второй
стадией (`i ∈ S`) превышает вклад любой строки без неё (`j ∉ S`) не более чем
в 4 раза, то ни один обмен (снять стадию с `i`, дать `j`) не снижает суммарную
ошибку — локальный оптимум относительно обменов (правило остановки в
PROPOSAL 29). -/
theorem stage2_swap_stationary (x y : ℝ) (h : x ≤ 4 * y) :
    ¬ (x / 4 + y * 4 < x + y) := by
  rw [bit_swap_improves_iff]; linarith

/-! ## Stage-two row selection: top-k by residual is exactly optimal -/

/-- Если мощности двух наборов строк упорядочены (`#S ≤ #T`), а вклад каждой
строки из `T` не меньше вклада любой строки вне `T`, то суммарный вклад `T`
не меньше суммарного вклада `S` — при неотрицательных вкладах `c`.
Доказательство: `S \ T` инъективно вкладывается в `T \ S` по мощности, каждый
элемент `S \ T` мажорируется своим образом. -/
theorem sum_le_of_dominating {ι : Type} [Fintype ι] [DecidableEq ι] (S T : Finset ι)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hcard : S.card ≤ T.card)
    (hdom : ∀ i ∈ T, ∀ j ∉ T, c j ≤ c i) :
    ∑ i ∈ S, c i ≤ ∑ i ∈ T, c i := by
  classical
  have e1 := Finset.card_inter_add_card_sdiff (s := S) (t := T)
  have e2 := Finset.card_inter_add_card_sdiff (s := T) (t := S)
  rw [Finset.inter_comm T S] at e2
  have hc' : Fintype.card ↥(S \ T) ≤ Fintype.card ↥(T \ S) := by
    simp only [Fintype.card_coe]; omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hc'
  have hinj : Set.InjOn (fun i : ↥(S \ T) => (g i : ι)) Set.univ := by
    intro a _ b _ h; exact g.injective (Subtype.ext h)
  have hsub : Finset.image (fun i : ↥(S \ T) => (g i : ι)) Finset.univ ⊆ T \ S := by
    intro x hx; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact (g i).2
  have hle : ∀ x : ↥(S \ T), c x ≤ c (g x) :=
    fun x => hdom (g x) (Finset.mem_sdiff.mp (g x).2).1 x (Finset.mem_sdiff.mp x.2).2
  have hstep : ∑ i ∈ S \ T, c i ≤ ∑ j ∈ T \ S, c j := calc
    _ = ∑ x : ↥(S \ T), c x := (Finset.sum_attach _ _).symm
    _ ≤ ∑ x : ↥(S \ T), c (g x) := Finset.sum_le_sum (fun x _ => hle x)
    _ = ∑ i ∈ Finset.image (fun i : ↥(S \ T) => (g i : ι)) Finset.univ, c i := by
        rw [Finset.sum_image (by simpa using hinj)]
    _ ≤ ∑ j ∈ T \ S, c j := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hc j)
  have hsd (A B : Finset ι) : A \ (A ∩ B) = A \ B := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hS : (∑ i ∈ S, c i) = (∑ i ∈ S \ T, c i) + ∑ i ∈ S ∩ T, c i := by
    have h := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := S) Finset.inter_subset_left (f := c)
    rw [hsd S T] at h; exact h.symm
  have hT : (∑ i ∈ T, c i) = (∑ i ∈ T \ S, c i) + ∑ i ∈ S ∩ T, c i := by
    have h := Finset.sum_sdiff (s₁ := T ∩ S) (s₂ := T) Finset.inter_subset_left (f := c)
    rw [hsd T S, Finset.inter_comm T S] at h; exact h.symm
  rw [hS, hT]; linarith

/-- Выбор строк для второй стадии квантования (HAGI_v2 HAGI_EMB_ROWS2, commit
1b55ac4): вклад строки после первой стадии `c i = ‖W_i − R1_i‖²`; вторая
стадия сжимает вклад выбранной строки в `ρ ≥ 1` раз, поэтому снижение
суммарной ошибки на наборе `S` равно `(1 − 1/ρ)·Σ_{i∈S} c i`. Среди всех
наборов мощности не более `k` максимум достигается на наборе `T`, где каждый
вклад внутри `T` не меньше любого вклада вне `T` (в коде: `argsort(-contrib)[:k]`).
Следовательно жадный выбор по остатку — точный оптимум, а не эвристика; размер
`k` остаётся единственным свободным параметром (измерено: knee при 128 строках,
PROPOSAL 29). -/
theorem topk_residual_is_optimal {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (S T : Finset ι) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hcard : S.card ≤ T.card) (hdom : ∀ i ∈ T, ∀ j ∉ T, c j ≤ c i) :
    (∑ i ∈ S, c i) * (1 - 1 / ρ) ≤ (∑ i ∈ T, c i) * (1 - 1 / ρ) := by
  have h := sum_le_of_dominating S T c hc hcard hdom
  have hn : 0 ≤ 1 - 1 / ρ := by
    have : 1 / ρ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  simpa [mul_comm] using mul_le_mul_of_nonneg_left h hn

/-! ## Optimal number of stage-two rows: marginal rule -/
/-- Кумулятивный вклад top-k: `C k = ∑ i < k, c i` для невозрастающей `c`. -/
noncomputable def C (c : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, c i
theorem C_succ (c : ℕ → ℝ) (k : ℕ) : C c (k+1) = C c k + c k := by
  unfold C; rw [Finset.sum_range_succ]
/-- Целевая функция: ошибка после второй стадии на k строках плюс стоимость байтов. -/
noncomputable def J (c : ℕ → ℝ) (lam b rho : ℝ) (k : ℕ) : ℝ :=
  -(1 - 1/rho) * C c k + lam * b * k
theorem J_step (c : ℕ → ℝ) (lam b rho : ℝ) (k : ℕ) :
    J c lam b rho (k+1) = J c lam b rho k + (lam * b - (1 - 1/rho) * c k) := by
  unfold J; rw [C_succ]; push_cast; ring
theorem J_decr_iff (c : ℕ → ℝ) (lam b rho : ℝ) (k : ℕ) :
    J c lam b rho (k+1) < J c lam b rho k ↔ (1 - 1/rho) * c k > lam * b := by
  rw [J_step]; constructor <;> intro h <;> linarith
theorem J_desc_iff (c : ℕ → ℝ) (lam b rho : ℝ) (k : ℕ) :
    J c lam b rho (k+1) ≤ J c lam b rho k ↔ (1 - 1/rho) * c k ≥ lam * b := by
  rw [J_step]; constructor <;> intro h <;> linarith
theorem J_nincr_iff (c : ℕ → ℝ) (lam b rho : ℝ) (k : ℕ) :
    J c lam b rho k ≤ J c lam b rho (k+1) ↔ (1 - 1/rho) * c k ≤ lam * b := by
  rw [J_step]; constructor <;> intro h <;> linarith
/-- J не возрастает на `[a, a+n]`, если каждая строка `k ∈ [a, a+n)` не убывает по шагу. -/
theorem J_mono_desc (c : ℕ → ℝ) (lam b rho : ℝ) (a n : ℕ)
    (h : ∀ k, a ≤ k → k < a + n → (1 - 1/rho) * c k ≥ lam * b) :
    J c lam b rho (a + n) ≤ J c lam b rho a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : J c lam b rho (a + n) ≤ J c lam b rho a :=
      ih (fun k hk1 hk2 => h k hk1 (by omega))
    have h2 : J c lam b rho (a + n + 1) ≤ J c lam b rho (a + n) :=
      (J_desc_iff c lam b rho (a + n)).mpr (h (a + n) (by omega) (by omega))
    rw [show a + (n + 1) = a + n + 1 by omega]
    exact le_trans h2 h1
theorem J_mono_nincr (c : ℕ → ℝ) (lam b rho : ℝ) (a n : ℕ)
    (h : ∀ k, a ≤ k → k < a + n → (1 - 1/rho) * c k ≤ lam * b) :
    J c lam b rho a ≤ J c lam b rho (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : J c lam b rho a ≤ J c lam b rho (a + n) := ih (fun k hk1 hk2 => h k hk1 (by omega))
    have h2 : J c lam b rho (a + n) ≤ J c lam b rho (a + n + 1) := by
      rw [J_nincr_iff]; exact h (a + n) (by omega) (by omega)
    rw [show a + (n + 1) = a + n + 1 by omega]
    exact le_trans h1 h2
theorem mono_at (c : ℕ → ℝ) (hmono : ∀ k, c (k+1) ≤ c k) : ∀ k m, k ≤ m → c m ≤ c k := by
  intro k m hkm
  induction m with
  | zero => simp at hkm; subst hkm; exact le_rfl
  | succ m ih =>
    by_cases h : k ≤ m
    · exact le_trans (hmono m) (ih h)
    · have : k = m + 1 := by omega
      subst this; exact le_rfl
/-- Оптимальное число строк второй стадии: первый индекс, где предельное снижение
`(1 − 1/ρ)·c k` не превышает цены строки `lam·b`. Для невозрастающей `c` это
глобальный минимум `J` (ошибка + стоимость байтов): до `kstar` J строго убывает,
после — не убывает, поэтому минимум в `kstar`. Для остатка, отсортированного по
вкладу, `kstar` — первое `k` с `(1 − 1/ρ)·c k ≤ λ·b`: байты второй стадии окупаются,
пока вклад строки превышает цену её хранения (измерено: knee при 128 строках,
PROPOSAL 29). -/
theorem kstar_minimal (c : ℕ → ℝ) (lam b rho : ℝ) (hρ : 1 ≤ rho) (hmono : ∀ k, c (k+1) ≤ c k)
    (kstar : ℕ) (hstop : (1 - 1/rho) * c kstar ≤ lam * b)
    (hbefore : ∀ k < kstar, (1 - 1/rho) * c k > lam * b) :
    ∀ k, J c lam b rho kstar ≤ J c lam b rho k := by
  have h1 : 1 / rho ≤ 1 := (div_le_one (by linarith : (0:ℝ) < rho)).mpr hρ
  have hn : 0 ≤ 1 - 1 / rho := sub_nonneg.mpr h1
  have hmon' := mono_at c hmono
  have hinc : ∀ n, J c lam b rho kstar ≤ J c lam b rho (kstar + n) := fun n =>
    J_mono_nincr c lam b rho kstar n (fun k hk1 _ =>
      le_trans (mul_le_mul_of_nonneg_left (hmon' kstar k hk1) hn) hstop)
  intro k
  by_cases h : k ≤ kstar
  · have e : kstar = k + (kstar - k) := by omega
    rw [e]
    exact J_mono_desc c lam b rho k (kstar - k) (fun m _ hm => le_of_lt (hbefore m (by omega)))
  · rw [show k = kstar + (k - kstar) by omega]; exact hinc (k - kstar)

/-- Правило auto (HAGI_v2 89d663a): брать строки, пока `c k ≥ θ·c 0`. Это в точности
маржинальное правило `kstar_minimal` при цене строки `lam·b = θ·(1 − 1/ρ)·c 0`:
порог задаёт цену байта, а не наоборот. Измерено (scripts/ab_rows2_kstar.py,
θ = 0.10, словарь из 256 строк): auto берёт 255 строк — подразумеваемая цена
байта 1.7e-3 nat/байт, тогда как перебор даёт оптимум при 64 строках и цене
до 3e-4; вклады остатка убывают медленно (c 255 / c 0 = 0.09), поэтому
относительный порог к первой строке почти не отсекает. Порог надо задавать
через цену байта: θ = λ·b / ((1 − 1/ρ)·c 0). Нестрогое условие кода (вклад
не меньше порога) даёт `kstar + 1` строку. -/
theorem auto_rule_is_kstar (c : ℕ → ℝ) (lam b rho θ : ℝ) (hρ : 1 < rho) (hc0 : 0 ≤ c 0)
    (hθ : 0 ≤ θ) (hmono : ∀ k, c (k+1) ≤ c k) (kstar : ℕ)
    (hprice : lam * b = θ * (1 - 1 / rho) * c 0)
    (hstop : c kstar < θ * c 0) (hbefore : ∀ k < kstar, θ * c 0 < c k) :
    (1 - 1 / rho) * c kstar ≤ lam * b ∧ ∀ k < kstar, lam * b < (1 - 1 / rho) * c k := by
  have hn : 0 < 1 - 1 / rho := by
    have h1 : 1 / rho < 1 := (div_lt_one (by linarith : (0:ℝ) < rho)).mpr hρ
    linarith
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hprice]; have := mul_lt_mul_of_pos_left hstop hn; nlinarith
  · rw [hprice]; have := mul_lt_mul_of_pos_left (hbefore k hk) hn; nlinarith

/-! ### CE weight of an embedding row: why the residual norm is not the right score -/

/-- Измерено на HAGI_v2 (scripts/ab_rows2_kstar.py, словарь из 256 строк):
корреляция прироста CE от второй стадии блока строк с суммой `‖res‖²` по блоку
равна 0.008 — выбор строк по норме остатка оптимален для MSE весов
(`topk_residual_is_optimal`), но не для CE. Причина — в производной: сдвиг
одного логита даёт в среднем по данным второй порядок `½·p·(1 − p)·d²`, где
`p` — вероятность класса; строка словаря, которую модель почти не предсказывает,
не даёт CE-выигрыша при любой норме остатка. Правильный балл строки для CE —
`p_i·‖ε_i‖²` (Fisher-вес), а не `‖ε_i‖²`.

`ceShift p q d = log(p·e^d + 1 − p) − q·d` — точный сдвиг CE при возмущении
одного логита на `d` (`p` — исходная вероятность класса, `q` — индикатор метки). -/

noncomputable def ceShift (p q : ℝ) (d : ℝ) : ℝ :=
  Real.log (p * Real.exp d + (1 - p)) - q * d

theorem ceShift_zero (p q : ℝ) : ceShift p q 0 = 0 := by
  have e : p * Real.exp 0 + (1 - p) = 1 := by rw [Real.exp_zero]; ring
  unfold ceShift; rw [e, Real.log_one]; ring

set_option maxHeartbeats 1000000 in
/-- Первая производная — смещение `p − q`: в среднем по данным (когда
метка — сдвинутый класс с вероятностью `p`) первый член обнуляется, остаётся
второй порядок. -/
theorem hasDerivAt_ceShift_zero (p q : ℝ) (_hp : 0 < p) (_hp1 : p < 1) :
    HasDerivAt (ceShift p q) (p - q) 0 := by
  have e1 : p * Real.exp 0 + (1 - p) = 1 := by rw [Real.exp_zero]; ring
  have hpos : p * Real.exp 0 + (1 - p) ≠ 0 := by rw [e1]; exact one_ne_zero
  have h0 : HasDerivAt (fun d => p * Real.exp d + (1 - p)) p 0 := by
    have h := (Real.hasDerivAt_exp (0:ℝ)).const_mul p
    rw [Real.exp_zero, mul_one] at h
    have e2 : (fun d : ℝ => p * Real.exp d) + (fun _ : ℝ => 1 - p) =
        fun d => p * Real.exp d + (1 - p) := by funext d; rfl
    rw [← e2]
    simpa using h.add (hasDerivAt_const (0:ℝ) (1 - p))
  have h2 := (Real.hasDerivAt_log hpos).comp 0 h0
  rw [e1, inv_one, one_mul] at h2
  have h3 : HasDerivAt (fun d : ℝ => q * d) q 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_mul q
  have h4 := h2.sub h3
  show HasDerivAt (fun d => Real.log (p * Real.exp d + (1 - p)) - q * d) (p - q) 0
  have e3 : (Real.log ∘ fun d : ℝ => p * Real.exp d + (1 - p)) - (fun d : ℝ => q * d) =
      (fun d => Real.log (p * Real.exp d + (1 - p)) - q * d) := by
    funext d; simp [Function.comp_def]
  rw [e3] at h4; exact h4

end Hagi.Budget
