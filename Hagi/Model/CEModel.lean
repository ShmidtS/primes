/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.SoftmaxHead
import Hagi.Model.CEDescent
import Hagi.Model.BatchCEDescent

/-!
# The common cross-entropy model interface

Audit 4.1: the CE family (~40 modules in `Hagi/Model`) repeats one
theory under three variance axes — carrier (single sample / batch /
stochastic), head (identity / gated / nonlinear), numeric regime
(exact / quantized).  The single-sample (`Model.CEDescent`) and batch
(`Model.BatchCEDescentSafeStep`) tranches already share, statement for
statement, the *safe-step descent contract*: quantities
`A(θ)` (alignment, the squared norm of the negative residual-gradient
direction), `R²(θ)` (quadratic range coefficient, the Böhning
curvature term), the update `next θ` taken at the safe step
`η = 4A/R²`, the floor `0 ≤ L`, the nondegeneracy transfer
`0 < R² → 0 < A`, and the guaranteed decrease
`L(next θ) ≤ L(θ) − 2A²/R²`.

This module is that contract, once: `CEModel Θ` is a structure of
carrier data plus the contract proofs.  Two bridged specializations
instantiate it from the existing SSOT theorems — every proof field
delegates to an existing theorem, no statement is duplicated — and
the consumer theorems (`strictDescent`, `safeStep_decrease_le_loss`)
are proved once on the interface and instantiated twice, replacing
the per-tranche duplicated strict-descent tails.

## Honest ledger (outside the interface, pinned migration tranches)

- `StochasticCE`: the end-to-end stochastic learning theorem lives in
  `Hagi.Unified.StochasticCELearning` (C360), above this layer; it is
  a consumer of the same `ceOneHot` SSOT and is a pointer target, not
  a bridge, here.
- `GatedCE`: the `Model.GatedCE*` family uses a curvature-selected
  step (`nSize`), a different contract shape.
- `NonlinearCE`: `Model.CEJacobianMajorizer` majorizes through a
  Jacobian remainder ball; adapting its `A`/`R`/remainder split to
  this interface is a tranche.
- `QuantizedCE`: `Model.CEQuantized` alters penalty constants, not
  the functional; a tranche.

The CE functional itself stays `Hagi.ceOneHot` (`Core.Concat`); the
parametric head stays `Model.SoftmaxHead` (`headCE`, `headLoss`).
Nothing outside this file changes.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model

variable {Θ : Type}

/-- The common safe-step descent contract of the CE family: the loss,
its safe update, the alignment `A` and range-square `R²` of the
underlying quadratic majorizer, plus the laws every mature CE tranche
already proves: the floor, alignment nonnegativity, the
nondegeneracy transfer, and the guaranteed decrease
`L(next θ) ≤ L(θ) − 2A²/R²` of the step taken at `η = 4A/R²`. -/
structure CEModel (Θ : Type) where
  /-- The loss being descended. -/
  loss : Θ → ℝ
  /-- The parameter update at the safe step. -/
  next : Θ → Θ
  /-- First-order alignment: the squared norm of the negative
  residual-gradient direction. -/
  alignment : Θ → ℝ
  /-- Quadratic range coefficient of the majorizer (the Böhning
  curvature term). -/
  rangeSquare : Θ → ℝ
  /-- Floor: the loss is nonnegative. -/
  loss_nonneg : ∀ θ : Θ, 0 ≤ loss θ
  /-- The alignment is nonnegative. -/
  alignment_nonneg : ∀ θ : Θ, 0 ≤ alignment θ
  /-- Nondegeneracy transfer: a positive range gives positive
  alignment. -/
  alignment_pos_of_range_pos :
    ∀ θ : Θ, 0 < rangeSquare θ → 0 < alignment θ
  /-- The safe-step descent contract: the update at `η = 4A/R²`
  decreases the loss by at least `2A²/R²`. -/
  safeStep_descent :
    ∀ θ : Θ, 0 < rangeSquare θ →
      loss (next θ) ≤ loss θ - 2 * (alignment θ) ^ 2 / rangeSquare θ

/-! ## Generic consumers: proved once on the interface -/

/-- Strict descent at a nondegenerate point, once for every CE model;
instantiations replace the per-tranche duplicated strict-descent
tails. -/
theorem strictDescent (M : CEModel Θ) (θ : Θ) (hR : 0 < M.rangeSquare θ) :
    M.loss (M.next θ) < M.loss θ := by
  have hA := M.alignment_pos_of_range_pos θ hR
  have hbound := M.safeStep_descent θ hR
  have hpos : 0 < 2 * (M.alignment θ) ^ 2 / M.rangeSquare θ := by
    positivity
  linarith

/-- The guaranteed decrease cannot exceed the current loss, because
the next loss is still above the floor. -/
theorem safeStep_decrease_le_loss (M : CEModel Θ) (θ : Θ)
    (hR : 0 < M.rangeSquare θ) :
    2 * (M.alignment θ) ^ 2 / M.rangeSquare θ ≤ M.loss θ := by
  have hbound := M.safeStep_descent θ hR
  have hfloor := M.loss_nonneg (M.next θ)
  linarith

/-! ## Bridge: the single-sample specialization (CEDescent) -/

variable {V : Type} [Fintype V] [Nonempty V] {d : ℕ}

/-- The single-sample CE model: the carrier data of `Model.CEDescent`
at feature matrix `X` and target `t`.  Every proof field is an
existing `Model.CEDescent` theorem; `rangeSquare` packages the step
range as its square, matching the batch tranche's `batchRangeSquare`. -/
noncomputable def singleSampleCE (X : Matrix V (Fin d) ℝ) (t : V) :
    CEModel (EuclideanSpace ℝ (Fin d)) where
  loss θ := Hagi.ceOneHot t (ceLogits X θ)
  next θ := ceNextParameters X θ t (safeStepSize X θ t)
  alignment θ := ceAlignment X θ t
  rangeSquare θ := (ceStepRange X θ t) ^ 2
  loss_nonneg θ := Hagi.Model.CEHeldout.ceOneHot_nonneg _ _
  alignment_nonneg θ := ceAlignment_nonneg X θ t
  alignment_pos_of_range_pos θ hR := by
    exact ceAlignment_pos_of_range_pos X θ t
      (lt_of_le_of_ne (ceStepRange_nonneg X θ t) (Ne.symm (sq_pos_iff.mp hR)))
  safeStep_descent θ hR :=
    ceOneHot_safeStep_le_residual X θ t
      (lt_of_le_of_ne (ceStepRange_nonneg X θ t) (Ne.symm (sq_pos_iff.mp hR)))

/-! ## Bridge: the batch specialization (BatchCEDescentSafeStep) -/

variable [Nonempty V]

/-- The arithmetic-mean batch CE model: the carrier data of
`Model.BatchCEDescentSafeStep` at feature batch `X` and labels `y`.
Every proof field is an existing `BatchCEDescent` theorem; the floor
is the empirical mean of nonnegative per-sample losses. -/
noncomputable def batchCE {B : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (y : Fin B → V) : CEModel (EuclideanSpace ℝ (Fin d)) where
  loss θ := BatchCEDescent.batchLoss X θ y
  next θ := BatchCEDescent.batchNextParameters X θ y
  alignment θ := BatchCEDescent.batchAlignment X θ y
  rangeSquare θ := BatchCEDescent.batchRangeSquare X θ y
  loss_nonneg θ := by
    unfold BatchCEDescent.batchLoss
      Hagi.Probability.FiniteFamilyConfidence.empiricalMean ceLogits
    exact div_nonneg
      (Finset.sum_nonneg fun b _ =>
        Hagi.Model.CEHeldout.ceOneHot_nonneg _ _)
      (by positivity)
  alignment_nonneg θ := BatchCEDescent.batchAlignment_nonneg X θ y
  alignment_pos_of_range_pos θ hR :=
    BatchCEDescent.batchAlignment_pos_of_rangeSquare_pos X θ y hR
  safeStep_descent θ hR :=
    BatchCEDescent.batchLoss_safeStep_le_residual X θ y hR

/-! ## Demonstration: one generic theorem, two instantiations -/

/-- Interface corollary (proof: the generic `strictDescent`): strict
single-sample CE descent of `Model.CEDescent` at the safe step. -/
theorem singleSampleCE_strictDescent (X : Matrix V (Fin d) ℝ) (t : V)
    (θ : EuclideanSpace ℝ (Fin d))
    (hR : 0 < (singleSampleCE X t).rangeSquare θ) :
    (singleSampleCE X t).loss ((singleSampleCE X t).next θ)
      < (singleSampleCE X t).loss θ :=
  strictDescent _ θ hR

/-- Interface corollary (proof: the generic `strictDescent`): strict
batch CE descent of `Model.BatchCEDescentSafeStep` at the common safe
step. -/
theorem batchCE_strictDescent {B : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (y : Fin B → V) (θ : EuclideanSpace ℝ (Fin d))
    (hR : 0 < (batchCE X y).rangeSquare θ) :
    (batchCE X y).loss ((batchCE X y).next θ) < (batchCE X y).loss θ :=
  strictDescent _ θ hR

end Hagi.Model
