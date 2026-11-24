/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Contracts.TruncatedSVDTail
import Hagi.Architecture.FactorizedMerge

set_option linter.style.header false

/-!
# ε_total: the joint output-space compression error

Audit 4.3: "суммарную ошибку сжатия и слияния экспертов считать
совместно (ε_total) по выходу/логитам, а не только по весам".

The per-stage error certificates of the repo are mostly WEIGHT-space:
the truncated-SVD tail (`Hagi.Contracts.TruncatedSVDTail`,
`truncated_svd_error_eq_tail` — Frobenius EQUALITY to the rectangular
tail), the ternary quantizer (`Hagi.Runtime.TernaryExact`,
`qTern_error_in` — scalar), and the expert merge
(`Hagi.Architecture.FactorizedMerge`, `unified_error_budget` — the
five-term weight-space triangle `‖W − S‖ ≤ e_shared + e_spectral +
e_rank + e_quant + e_routing`). The output-side transfer machinery
(`Hagi.Model.BackboneTransfer`, `resStack_lipschitz` — the ∏(1+μᵢ)
composite) composes only endo-maps `X → X`.

This module supplies the missing bridge — stage errors mapped to
OUTPUT/LOGIT space through a bounded input and chained across a
downstream Lipschitz head:

* `two_stage_output_error` — the abstract two-stage triangle: a
  stage-1 pointwise output error `‖f x − g x‖ ≤ e₁` propagated
  through a `L`-Lipschitz downstream map `F`, plus the downstream
  map's own pointwise error `‖F y − G y‖ ≤ e₂`, gives
  `‖F (f x) − G (g x)‖ ≤ L·e₁ + e₂` (triangle over Lipschitz
  composition);
* `linear_pair_output_error` — two WEIGHT-space stages on the linear
  head (`‖W − Wq‖ ≤ e₁`, `‖Wq − Wqq‖ ≤ e₂`, operator norm) mapped to
  output space by the input bound `‖x‖ ≤ B`:
  `‖W x − Wqq x‖ ≤ (e₁ + e₂)·B`;
* `logit_head_total_error` — **MAIN**: the concrete ε_total for a
  compressed logit head — low-rank truncation (stage 1, `e_svd`:
  the premise discharged theorem-form
  `sparse_premise_discharged` on the Frobenius side) then
  quantization (stage 2, `e_quant`), both through the bounded input
  and the `L`-Lipschitz decoder with its own error `e_dec`:
  `‖D (W x) − D' (Wqq x)‖ ≤ L·((e_svd + e_quant)·B) + e_dec`.

Honest scope (pins — stage combinations NOT yet composable):

* FROBENIUS → OPNORM: `truncated_svd_error_eq_tail` is Frobenius;
  the stage premise `‖W − Wq‖op ≤ e_svd` needs `‖·‖op ≤ ‖·‖F`,
  absent from the repo (the `External/Flywheel/MatrixNormRelations`
  spectral identification wall is the same root-sorting
  gap). The instantiation keeps this bridge premise-form.
* SCALAR → VECTOR QUANT: `qTern_error_in` is scalar per-coordinate;
  the lift to a `ContinuousLinearMap` stage bound (`‖Wq − Wqq‖op ≤
  e_quant` from a `Fin n` coordinate sum) is not yet stated.
* MERGE CARRIER: `factorized_error_bound` bounds the merge error in
  EXPERT WEIGHT space `X`; composing it with the logit chain needs a
  merge-to-head carrier map, not yet in the repo.
* STACK CARRIER: `resStack_lipschitz` (∏(1+μᵢ)) is endo `X → X`;
  cross-carrier heads use the general `LipschitzWith` form above;
  instantiating `D` by a concrete stack needs an endo `Y → Y` head.

-/

open ContinuousLinearMap

namespace Hagi.Contracts.TotalError

/-! ## The abstract two-stage triangle -/

section Abstract

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]

omit [NormedAddCommGroup X] in
/-- Two chained stages' output errors ADD: a stage-1 pointwise output
error `e₁` propagates through an `L`-Lipschitz downstream map `F`, and
the downstream approximation error `e₂` (pointwise, between `F` and
its served replacement `G`) is added on top —
`‖F (f x) − G (g x)‖ ≤ L·e₁ + e₂`. -/
theorem two_stage_output_error
    (f g : X → Y) (F G : Y → Y) (L : NNReal) (e₁ e₂ : ℝ) (x : X)
    (h1 : ‖f x - g x‖ ≤ e₁)
    (hL : LipschitzWith L F)
    (h2 : ∀ y, ‖F y - G y‖ ≤ e₂) :
    ‖F (f x) - G (g x)‖ ≤ (L : ℝ) * e₁ + e₂ := by
  have hsplit : F (f x) - G (g x)
      = (F (f x) - F (g x)) + (F (g x) - G (g x)) := by abel
  calc ‖F (f x) - G (g x)‖
      = ‖F (f x) - F (g x) + (F (g x) - G (g x))‖ := by rw [hsplit]
    _ ≤ ‖F (f x) - F (g x)‖ + ‖F (g x) - G (g x)‖ :=
          norm_add_le _ _
    _ ≤ (L : ℝ) * ‖f x - g x‖ + e₂ :=
          add_le_add (hL.norm_sub_le (f x) (g x)) (h2 (g x))
    _ ≤ (L : ℝ) * e₁ + e₂ :=
          add_le_add_left
            (mul_le_mul_of_nonneg_left h1 (by positivity)) e₂

end Abstract

/-! ## Two weight-space stages on a linear head, mapped to output -/

section Linear

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace ℝ X] [NormedSpace ℝ Y]

/-- Two operator-norm weight-space stages on the same linear head
(e.g. low-rank truncation then quantization), mapped to output space
by the input bound: `‖W x − Wqq x‖ ≤ (e₁ + e₂)·B` when `‖x‖ ≤ B`,
`‖W − Wq‖op ≤ e₁`, `‖Wq − Wqq‖op ≤ e₂`. -/
theorem linear_pair_output_error
    (W Wq Wqq : X →L[ℝ] Y) (x : X) (B e₁ e₂ : ℝ)
    (hB : ‖x‖ ≤ B)
    (h1 : ‖(W - Wq : X →L[ℝ] Y)‖ ≤ e₁)
    (h2 : ‖(Wq - Wqq : X →L[ℝ] Y)‖ ≤ e₂) :
    ‖W x - Wqq x‖ ≤ (e₁ + e₂) * B := by
  have hsplit : W x - Wqq x = (W x - Wq x) + (Wq x - Wqq x) := by abel
  have hleg1 : ‖W x - Wq x‖ ≤ e₁ * B :=
    calc ‖W x - Wq x‖ = ‖(W - Wq : X →L[ℝ] Y) x‖ := by
          rw [sub_apply]
    _ ≤ ‖(W - Wq : X →L[ℝ] Y)‖ * ‖x‖ := le_opNorm (W - Wq : X →L[ℝ] Y) x
    _ ≤ e₁ * B := mul_le_mul h1 hB (norm_nonneg x)
      (le_trans (norm_nonneg (W - Wq : X →L[ℝ] Y)) h1)
  have hleg2 : ‖Wq x - Wqq x‖ ≤ e₂ * B :=
    calc ‖Wq x - Wqq x‖ = ‖(Wq - Wqq : X →L[ℝ] Y) x‖ := by
          rw [sub_apply]
    _ ≤ ‖(Wq - Wqq : X →L[ℝ] Y)‖ * ‖x‖ :=
          le_opNorm (Wq - Wqq : X →L[ℝ] Y) x
    _ ≤ e₂ * B := mul_le_mul h2 hB (norm_nonneg x)
      (le_trans (norm_nonneg (Wq - Wqq : X →L[ℝ] Y)) h2)
  rw [hsplit]
  calc ‖(W x - Wq x) + (Wq x - Wqq x)‖
      ≤ ‖W x - Wq x‖ + ‖Wq x - Wqq x‖ := norm_add_le _ _
    _ ≤ e₁ * B + e₂ * B := add_le_add hleg1 hleg2
    _ = (e₁ + e₂) * B := by ring

/-- **ε_total for a compressed logit head** (MAIN): stage 1 = low-rank
truncation (`e_svd`; the Frobenius side is `sparse_premise_discharged`),
stage 2 = quantization (`e_quant`), both mapped to output space
by the input bound `B`, then chained through the `L`-Lipschitz decoder
`D` whose own served error is `e_dec`:
`‖D (W x) − D' (Wqq x)‖ ≤ L·((e_svd + e_quant)·B) + e_dec`. -/
theorem logit_head_total_error
    (W Wq Wqq : X →L[ℝ] Y) (D D' : Y → Y) (L : NNReal)
    (x : X) (B e_svd e_quant e_dec : ℝ)
    (hB : ‖x‖ ≤ B)
    (h1 : ‖(W - Wq : X →L[ℝ] Y)‖ ≤ e_svd)
    (h2 : ‖(Wq - Wqq : X →L[ℝ] Y)‖ ≤ e_quant)
    (hL : LipschitzWith L D)
    (h3 : ∀ y, ‖D y - D' y‖ ≤ e_dec) :
    ‖D (W x) - D' (Wqq x)‖
      ≤ (L : ℝ) * ((e_svd + e_quant) * B) + e_dec := by
  refine two_stage_output_error (f := W) (g := Wqq)
    (F := D) (G := D') L ((e_svd + e_quant) * B) e_dec x ?_ hL h3
  exact linear_pair_output_error W Wq Wqq x B e_svd e_quant hB h1 h2

end Linear

end Hagi.Contracts.TotalError
