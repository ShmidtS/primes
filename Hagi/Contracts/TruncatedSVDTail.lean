/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.SparseInferenceCert

set_option linter.style.header false

/-!
# The truncated-SVD tail bridge: the approximant ACHIEVES the tail

The missing UPPER side of the rectangular Eckart–Young pair. C232/C281
proved the LOWER bound — no rank-`k` approximant beats the rectangular
spectral tail (`eckart_young_lower_bound_rect_true_tail`, cited by
C328 `sparse_inference_error` at its `hE` premise sites). This module
proves the upper side for the EXPLICITLY CONSTRUCTED truncated-SVD
approximant, under the SVD premise (the C297 `ns_contraction_svd`
premise-form decomposition — `A = U·S·Vᴴ` with `S` the diagonal carrier
of the rectangular singular spectrum):

* `tailCarrier` — the m×n diagonal carrier on paired injections
  (`σ_q` at `(eM q, eN q)` for `q ≥ k`, zero elsewhere);
* `frob_sq_eq_trace` — `‖M‖_F² = (trace (Mᴴ M)).re` (no spectrum
  needed — the entry/normSq bridge);
* `rot_trace` — unitary invariance of the Gram trace (pure matrix
  algebra + `trace_mul_comm`);
* `tail_trace` — the double-sparsity collapse of the carrier Gram;
* `rot_tail_sq` — `‖U·S_k·Vᴴ‖_F² = ∑_{q≥k} σ_q²`;
* `truncated_svd_error_eq_tail` — **MAIN**: under the SVD premise,
  `‖A − A_k‖_F² = ∑ i, (rectangularTail A k i)²` — EQUALITY;
* `sparse_premise_discharged` — the `hE` premise of C328 becomes a
  theorem for SVD-decomposable `A`: `‖A − A_k‖ = (∑ tail²)^{1/2}`.

The proof route by-passes singular-value identification of the rotated
difference entirely: Frobenius² = Gram trace (entry computation), Gram
trace is unitary-invariant (trace cycling), and the carrier Gram trace
collapses by double sparsity. No root sorting — which is exactly what
the deferred legs need (see pins).

Honest scope (pins):

* SPECTRAL leg deferred: `‖A − A_k‖₂ = σ_{k+1}` needs the singular-value
  IDENTIFICATION of `U·S_k·Vᴴ` (rotated Gram, same charpoly
  root-sorting wall as C232/C281). The Frobenius form is the one C328
  consumes (`Matrix.frobeniusSeminormedAddCommGroup` local instance).
* NO new SVD existence: `A = U·S·Vᴴ` is premise-form (every real matrix
  has an SVD mathematically; constructiveness stays behind the premise,
  C297 discipline). The spectrum identification `hσ` (the diagonal IS
  the rectangular singular spectrum) is likewise premise-form — the
  honest general case.
* Matrix ↔ `LinearMap` gap stays pinned (C281 Mathlib note).

Created: 2026-11-16 (C342, A13 priority P-3)
-/

open Matrix Finset
open Hagi.External.Flywheel
open Hagi.Contracts.GradientBottleneckIdentification (rectangularTail)
open scoped ComplexConjugate

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup

namespace Hagi.Contracts.TruncatedSVDTail

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ## The tail carrier -/

/-- The tail carrier: the rectangular diagonal matrix with `σ_q` at the
paired diagonal position `(eM q, eN q)` for indices `q ≥ k`, zero
elsewhere. `tailCarrier eM eN σ 0` is the full singular-value carrier
`S` of the SVD premise; `tailCarrier eM eN σ k` is its truncated tail
`S_k`. -/
noncomputable def tailCarrier (eM : Fin (min (Fintype.card m) (Fintype.card n)) → m)
    (eN : Fin (min (Fintype.card m) (Fintype.card n)) → n)
    (σ : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ) (k : ℕ) : Matrix m n ℂ :=
  Matrix.of fun i j =>
    if h : ∃ q, eM q = i ∧ eN q = j then
      (if k ≤ (Classical.choose h).val then (σ (Classical.choose h) : ℂ) else 0)
    else 0

/-- Entry form of the tail carrier as a single index sum — the sparsity
workhorse: at most one diagonal index hits any entry (injectivity of
`eM`). -/
theorem tailCarrier_eq_sum (eM : Fin (min (Fintype.card m) (Fintype.card n)) → m)
    (hM : Function.Injective eM)
    (eN : Fin (min (Fintype.card m) (Fintype.card n)) → n)
    (hN : Function.Injective eN)
    (σ : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ) (k : ℕ)
    (i : m) (j : n) :
    tailCarrier eM eN σ k i j
      = ∑ r, (if eM r = i ∧ eN r = j then
          (if k ≤ r.val then (σ r : ℂ) else 0) else 0) := by
  have huniq : ∀ q r : Fin (min (Fintype.card m) (Fintype.card n)),
      eM q = i ∧ eN q = j → eM r = i ∧ eN r = j → r = q := by
    intro q r hq hr
    exact hM (hr.1.trans hq.1.symm)
  show (if h : ∃ q, eM q = i ∧ eN q = j then
      (if k ≤ (Classical.choose h).val then (σ (Classical.choose h) : ℂ) else 0) else 0)
    = _
  by_cases h : ∃ q, eM q = i ∧ eN q = j
  · rw [dif_pos h]
    rw [Finset.sum_eq_single_of_mem (Classical.choose h) (Finset.mem_univ _)]
    · rw [if_pos (Classical.choose_spec h)]
    · intro r _ hr
      rw [if_neg]
      intro hcon
      exact hr (huniq (Classical.choose h) r (Classical.choose_spec h) hcon)
  · rw [dif_neg h]
    refine (Finset.sum_eq_zero fun r _ => if_neg ?_).symm
    intro hcon
    exact h ⟨r, hcon⟩

/-! ## The Frobenius-trace bridge (no spectrum needed) -/

set_option linter.unusedSectionVars false in
/-- Frobenius norm squared is the real trace of the Gram matrix:
`‖M‖_F² = (trace (Mᴴ M)).re`. Entry-level computation (the
`frobenius_norm_def` rpow form + the per-entry `normSq` bridge); no
singular values anywhere. -/
theorem frob_sq_eq_trace (M : Matrix m n ℂ) :
    ‖M‖ ^ 2 = ((Mᴴ * M).trace : ℂ).re := by
  rw [Matrix.frobenius_norm_def]
  have hnn : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hsq : ((∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2
      = ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]; norm_num
  rw [hsq]
  have hentry : ∀ z : ℂ, ‖z‖ ^ (2 : ℝ) = ((starRingEnd ℂ) z * z).re := by
    intro z
    have hc : ((starRingEnd ℂ) z * z) = (Complex.normSq z : ℂ) := by
      show star z * z = _
      rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
    rw [Real.rpow_two, hc, Complex.ofReal_re,
      ← Complex.normSq_eq_norm_sq z]
  have hre : ∑ i, ∑ j, ‖M i j‖ ^ (2 : ℝ)
      = ((Mᴴ * M).trace : ℂ).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact hentry (M j i)
  rw [hre]

/-- Unitary invariance of the Gram trace: for `Uᴴ U = Vᴴ V = 1` the
rotated matrix has the same Gram trace — `trace((U T Vᴴ)ᴴ (U T Vᴴ))
= trace(Tᴴ T)`. Pure matrix-ring algebra plus `trace_mul_comm`. -/
theorem rot_trace (T : Matrix m n ℂ) (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    ((U * T * Vᴴ)ᴴ * (U * T * Vᴴ)).trace = (Tᴴ * T).trace := by
  have hmid : (Tᴴ * Uᴴ) * (U * T * Vᴴ) = (Tᴴ * T) * Vᴴ := by
    rw [Matrix.mul_assoc U T Vᴴ,
      ← Matrix.mul_assoc (Tᴴ * Uᴴ) U (T * Vᴴ),
      Matrix.mul_assoc Tᴴ Uᴴ U, hU, Matrix.mul_one,
      ← Matrix.mul_assoc Tᴴ T Vᴴ]
  have h1 : (U * T * Vᴴ)ᴴ * (U * T * Vᴴ) = V * (Tᴴ * T) * Vᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc V (Tᴴ * Uᴴ) (U * T * Vᴴ), hmid,
      Matrix.mul_assoc V (Tᴴ * T) Vᴴ]
  rw [h1, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]

/-- The carrier Gram trace collapses by double sparsity:
`trace(S_kᴴ S_k) = ∑_r tailval_r · tailval_r` — each diagonal Gram
entry is a single-index product (at most one carrier index per entry on
each side). -/
theorem tail_trace (eM : Fin (min (Fintype.card m) (Fintype.card n)) → m)
    (hM : Function.Injective eM)
    (eN : Fin (min (Fintype.card m) (Fintype.card n)) → n)
    (hN : Function.Injective eN)
    (σ : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ) (k : ℕ) :
    ((tailCarrier eM eN σ k)ᴴ * tailCarrier eM eN σ k).trace
      = ∑ r, ((if k ≤ r.val then (σ r : ℂ) else 0)
          * (if k ≤ r.val then (σ r : ℂ) else 0)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, tailCarrier_eq_sum eM hM eN hN σ k]
  have hc : ∀ r : Fin (min (Fintype.card m) (Fintype.card n)),
      star (if k ≤ r.val then (σ r : ℂ) else 0)
        = if k ≤ r.val then (σ r : ℂ) else 0 := by
    intro r
    by_cases hk : k ≤ r.val <;> simp [Complex.conj_ofReal, hk]
  have hprod : ∀ (x : m) (j : n),
      (star (∑ r, (if eM r = x ∧ eN r = j then (if k ≤ r.val then (σ r : ℂ) else 0) else 0))
        * ∑ r, (if eM r = x ∧ eN r = j then (if k ≤ r.val then (σ r : ℂ) else 0) else 0))
      = (∑ r, (if eM r = x ∧ eN r = j
          then (if k ≤ r.val then (σ r : ℂ) else 0)
            * (if k ≤ r.val then (σ r : ℂ) else 0) else 0)) := by
    intro x j
    by_cases hex : ∃ r, eM r = x ∧ eN r = j
    · obtain ⟨r₀, hr₀⟩ := hex
      rw [Finset.sum_eq_single_of_mem r₀ (Finset.mem_univ _)]
      · rw [Finset.sum_eq_single_of_mem r₀ (Finset.mem_univ _)]
        · rw [if_pos hr₀, hc r₀, if_pos hr₀]
        · intro r _ hr
          rw [if_neg]
          intro hcon
          exact hr (hM (hcon.1.trans hr₀.1.symm))
      · intro r _ hr
        rw [if_neg]
        intro hcon
        exact hr (hM (hcon.1.trans hr₀.1.symm))
    · have hz1 : ∀ r : Fin (min (Fintype.card m) (Fintype.card n)),
        ¬(eM r = x ∧ eN r = j) := fun r hcon => hex ⟨r, hcon⟩
      rw [Finset.sum_eq_zero fun r _ => if_neg (hz1 r),
        Finset.sum_eq_zero fun r _ => if_neg (hz1 r), star_zero, zero_mul]
  have step1 : (∑ j : n, ∑ x : m,
      star (∑ r : Fin (min (Fintype.card m) (Fintype.card n)),
          if eM r = x ∧ eN r = j then (if k ≤ r.val then (σ r : ℂ) else 0) else 0)
        * ∑ r : Fin (min (Fintype.card m) (Fintype.card n)),
          if eM r = x ∧ eN r = j then (if k ≤ r.val then (σ r : ℂ) else 0) else 0)
      = ∑ j : n, ∑ x : m, ∑ r : Fin (min (Fintype.card m) (Fintype.card n)),
          (if eM r = x ∧ eN r = j
          then (if k ≤ r.val then (σ r : ℂ) else 0)
            * (if k ≤ r.val then (σ r : ℂ) else 0) else 0) :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => hprod x j
  rw [step1]
  have key : ∀ (F : n → m → Fin (min (Fintype.card m) (Fintype.card n)) → ℂ),
      ∑ a, ∑ b, ∑ r, F a b r = ∑ r, ∑ b, ∑ a, F a b r := by
    intro F
    have h1 : ∑ a, ∑ b, ∑ r, F a b r = ∑ b, ∑ a, ∑ r, F a b r := Finset.sum_comm
    have h2 : ∑ b, ∑ a, ∑ r, F a b r = ∑ b, ∑ r, ∑ a, F a b r :=
      Finset.sum_congr rfl fun b _ => Finset.sum_comm (f := fun a r => F a b r)
    have h3 : ∑ b, ∑ r, ∑ a, F a b r = ∑ r, ∑ b, ∑ a, F a b r := Finset.sum_comm
    exact h1.trans (h2.trans h3)
  rw [key (fun j x r => if eM r = x ∧ eN r = j
    then (if k ≤ r.val then (σ r : ℂ) else 0)
      * (if k ≤ r.val then (σ r : ℂ) else 0) else 0)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single_of_mem (eM r) (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem (eN r) (Finset.mem_univ _)]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro j _ hj
      rw [if_neg (show ¬(eM r = eM r ∧ eN r = j) from fun hcon => hj hcon.2.symm)]
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (show ¬(eM r = b ∧ eN r = j) from fun hcon => hb hcon.1.symm)]

/-- **The rotated-tail Frobenius identity**: `‖U·S_k·Vᴴ‖_F²` equals the
tail square sum `∑_r (if k ≤ r then σ_r else 0)²` for unitary `U, V`.
Composition: Frobenius² = Gram trace (`frob_sq_eq_trace`), Gram trace is
rotation-invariant (`rot_trace`), the carrier Gram trace collapses
(`tail_trace`). NO singular-value identification of the rotated
difference — the root-sorting wall is by-passed. -/
theorem rot_tail_sq (eM : Fin (min (Fintype.card m) (Fintype.card n)) → m)
    (hM : Function.Injective eM)
    (eN : Fin (min (Fintype.card m) (Fintype.card n)) → n)
    (hN : Function.Injective eN)
    (σ : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ) (k : ℕ)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    ‖U * tailCarrier eM eN σ k * Vᴴ‖ ^ 2
      = ∑ r, (if k ≤ r.val then σ r else 0) ^ 2 := by
  rw [frob_sq_eq_trace, rot_trace (tailCarrier eM eN σ k) U V hU hV,
    tail_trace eM hM eN hN σ k]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hk : k ≤ r.val
  · rw [if_pos hk, if_pos hk]
    norm_num [Complex.mul_re, Complex.ofReal_re, sq]
  · rw [if_neg hk, if_neg hk]
    simp

/-! ## The truncated approximant -/

/-- The truncated-SVD approximant under the SVD premise:
`A_k = U·(S − S_k)·Vᴴ` — the full singular-value carrier minus its
tail (the head keeps the top `k` directions). -/
noncomputable def approxK (eM : Fin (min (Fintype.card m) (Fintype.card n)) → m)
    (eN : Fin (min (Fintype.card m) (Fintype.card n)) → n)
    (σ : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ) (k : ℕ)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ) : Matrix m n ℂ :=
  U * (tailCarrier eM eN σ 0 - tailCarrier eM eN σ k) * Vᴴ

/-- Difference identity: under the SVD premise `A = U·S·Vᴴ` the
approximation error IS the rotated tail carrier — `A − A_k =
U·S_k·Vᴴ` (pure ring algebra). -/
theorem diff_eq_rot (eM : Fin (min (Fintype.card m) (Fintype.card n)) → m)
    (eN : Fin (min (Fintype.card m) (Fintype.card n)) → n)
    (σ : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ) (k : ℕ)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (A : Matrix m n ℂ) (hA : A = U * tailCarrier eM eN σ 0 * Vᴴ) :
    A - approxK eM eN σ k U V = U * tailCarrier eM eN σ k * Vᴴ := by
  unfold approxK
  rw [hA]
  have hsplit : U * (tailCarrier eM eN σ 0 - tailCarrier eM eN σ k) * Vᴴ
      = U * tailCarrier eM eN σ 0 * Vᴴ - U * tailCarrier eM eN σ k * Vᴴ := by
    rw [Matrix.mul_assoc U (tailCarrier eM eN σ 0 - tailCarrier eM eN σ k) Vᴴ,
      Matrix.sub_mul, Matrix.mul_sub,
      ← Matrix.mul_assoc U (tailCarrier eM eN σ 0) Vᴴ,
      ← Matrix.mul_assoc U (tailCarrier eM eN σ k) Vᴴ]
  rw [hsplit, sub_sub_cancel]

/-! ## The main identity and the premise discharge -/

/-- **MAIN — the truncated-SVD tail error bridge**: under the SVD
premise (`A = U·S·Vᴴ` with `UᴴU = VᴴV = 1`, the diagonal carrier on
paired injections, and `hσ` identifying the diagonal with the carrier's
rectangular singular spectrum — premise-form, the honest general case),
the truncated approximant `A_k` ACHIEVES the rectangular spectral-tail
error with EQUALITY in the Frobenius form — exactly the `hE` bound of
C328 `sparse_inference_error`, now with `:=` instead of hypothesis.
Together with C281 `eckart_young_lower_bound_rect_true_tail` (no rank-`k`
approximant does better) this closes the rectangular Eckart–Young pair
for SVD-decomposable `A`. Frobenius only; the spectral leg is deferred
with the C232/C281 root-sorting gap. -/
theorem truncated_svd_error_eq_tail
    (A : Matrix m n ℂ) (k : ℕ)
    (eM : Fin (min (Fintype.card m) (Fintype.card n)) → m)
    (hM : Function.Injective eM)
    (eN : Fin (min (Fintype.card m) (Fintype.card n)) → n)
    (hN : Function.Injective eN)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (σ : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ)
    (hσ : ∀ q, σ q = Matrix.SVD.Rectangular.singularValues A q)
    (hA : A = U * tailCarrier eM eN σ 0 * Vᴴ) :
    ‖A - approxK eM eN σ k U V‖ ^ 2
      = ∑ i, (rectangularTail A k i) ^ 2 := by
  rw [diff_eq_rot eM eN σ k U V A hA,
    rot_tail_sq eM hM eN hN σ k U V hU hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold rectangularTail
  rw [← hσ i]

/-- **The C328 premise discharged**: under the same SVD premise, the
`hE` hypothesis of `sparse_inference_error` holds with EQUALITY for the
constructed approximant — `‖A − A_k‖ = (∑ i, (rectangularTail A k i)²)
^{1/2}`. The premise-form becomes theorem-form for explicit
SVD-decomposable `A` (every real matrix has an SVD mathematically; the
premise remains for constructiveness — the C297 discipline). -/
theorem sparse_premise_discharged
    (A : Matrix m n ℂ) (k : ℕ)
    (eM : Fin (min (Fintype.card m) (Fintype.card n)) → m)
    (hM : Function.Injective eM)
    (eN : Fin (min (Fintype.card m) (Fintype.card n)) → n)
    (hN : Function.Injective eN)
    (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (σ : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ)
    (hσ : ∀ q, σ q = Matrix.SVD.Rectangular.singularValues A q)
    (hA : A = U * tailCarrier eM eN σ 0 * Vᴴ) :
    ‖A - approxK eM eN σ k U V‖
      = (∑ i, (rectangularTail A k i) ^ 2).sqrt := by
  rw [← Real.sqrt_sq (norm_nonneg _),
    truncated_svd_error_eq_tail A k eM hM eN hN U V hU hV σ hσ hA]

/-! ## Numeric anchor note

The 2x2 diagonal(3,1), k=1 anchor (tail = 1) is deferred: the
`Fin (min (Fintype.card (Fin 2)) ...)` carrier-index casts resist
`decide` reduction (classical Decidable instances in card proofs).
Recorded as an honest gap; the main theorems
`truncated_svd_error_eq_tail` / `sparse_premise_discharged` carry
the mathematical content. See .tmp/C342-343 receipts.
-/
end TruncatedSVDTail
