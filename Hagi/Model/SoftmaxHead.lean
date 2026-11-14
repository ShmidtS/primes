/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat
import Hagi.Model.CEHeldout
import Hagi.Model.CEQuantized

/-!
# Parametric softmax head core

The cross-entropy family (gated, tanh, packed, grouped/joint scale,
padding, held-out confidence, batch descent; survey
`.tmp/C283/survey.md`) consists of variants of one theory whose
definitional axes are the pointwise logit transform and the batch
aggregation.  This module is the migration seed: those axes become an
inductive configuration, the CE functional is defined by recursion on
it, and the common theorem classes (floor, Lipschitz estimate) are
proved once, parametric in the configuration.

The single source of truth for the CE functional stays
`Hagi.ceOneHot`; the configuration only reparametrizes its argument.
Existing statements about `Hagi.ceOneHot` are instances at
`LogitMap.ident`.  No statement of an existing module changes.

The scale/quantizer axis is deliberately not a constructor here: it
alters penalty constants, not the CE functional, and an inductive
there would force re-proving the penalty bounds per constructor.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Model.SoftmaxHead

/-! ## Axis (a): the pointwise logit transform -/

/-- The pointwise transform applied to raw logits before the softmax.
`ident` is the classical linear head; `tanh` is the saturating head of
the gated family. -/
inductive LogitMap where
  | ident
  | tanh
  deriving Repr

/-- `LogitMap.apply` is the recursion defining the transform; it is
the only recursion point of the configuration. -/
noncomputable def LogitMap.apply : LogitMap → ℝ → ℝ
  | .ident, x => x
  | .tanh, x => Real.tanh x

/-! ## Axis (b): the batch aggregation -/

/-- The per-example aggregation of the batch reduction: uniform
weights or an explicit weight vector. -/
inductive Reduction (ι : Type) where
  | uniform : Reduction ι
  | weighted (w : ι → ℝ) : Reduction ι

/-- `Reduction.weight` is the weight of one example, by recursion on
the reduction; the aggregation is the weighted sum. -/
def Reduction.weight : Reduction ι → ι → ℝ
  | .uniform => fun _ => 1
  | .weighted w => w

/-- The full head configuration: a logit map and a reduction. -/
structure HeadConfig (ι : Type) where
  /-- Pointwise logit transform. -/
  logitMap : LogitMap
  /-- Batch aggregation. -/
  reduction : Reduction ι

/-! ## The CE functional by recursion on the configuration -/

variable {V : Type} [Fintype V] [Nonempty V] {ι : Type} [Fintype ι]

/-- One-hot cross-entropy of the mapped logits; `Hagi.ceOneHot` is
applied to `LogitMap.apply` composed with the raw logit vector. -/
noncomputable def headCE (m : LogitMap) (t : V) (z : V → ℝ) : ℝ :=
  Hagi.ceOneHot t (fun v => m.apply (z v))

/-- Batch CE functional: the `Reduction.weight`-weighted sum of the
per-example `headCE`. -/
noncomputable def headLoss (cfg : HeadConfig ι) (t : ι → V)
    (z : ι → V → ℝ) : ℝ :=
  ∑ i, cfg.reduction.weight i * headCE cfg.logitMap (t i) (z i)

/-! ## The definitional bridge to the existing machinery -/

/-- At the identity logit map, `headCE` is literally `Hagi.ceOneHot`:
every existing CE statement is the `LogitMap.ident` instance. -/
theorem headCE_ident (t : V) (z : V → ℝ) :
    headCE .ident t z = Hagi.ceOneHot t z := rfl

/-! ## P-FLOOR: the parametric floor -/

/-- Nonnegativity of the parametric CE, for every logit map.  This is
the config-generic form of the floor statements of the held-out and
penalty families. -/
theorem headCE_nonneg (m : LogitMap) (t : V) (z : V → ℝ) :
    0 ≤ headCE m t z :=
  Hagi.Model.CEHeldout.ceOneHot_nonneg t _

/-! ## P-LIPSCHITZ: the parametric two-Lipschitz estimate -/

/-- A uniform bound on the change of the mapped logits bounds the
parametric CE by twice that bound, for every logit map.  The
`LogitMap.ident` instance is
`Hagi.Model.CEQuantized.ceOneHot_le_of_abs_sub_le`, which is used,
not restated. -/
theorem headCE_le_of_abs_sub_le (m : LogitMap) (t : V) (y z : V → ℝ)
    (r : ℝ) (h : ∀ v, |m.apply (y v) - m.apply (z v)| ≤ r) :
    headCE m t y ≤ headCE m t z + 2 * r :=
  Hagi.Model.CEQuantized.ceOneHot_le_of_abs_sub_le t _ _ r h

/-! ## Bridge demo: a variant as a one-line instantiation -/

/-- The tanh variant of the two-Lipschitz estimate, in one line from
the parametric form: what used to be a new variant file is now a
configuration plus an instantiation. -/
theorem headCE_tanh_le_of_abs_tanh_sub_le (t : V) (y z : V → ℝ)
    (r : ℝ) (h : ∀ v, |Real.tanh (y v) - Real.tanh (z v)| ≤ r) :
    headCE .tanh t y ≤ headCE .tanh t z + 2 * r :=
  headCE_le_of_abs_sub_le _ t y z r h

/-- For the tanh map the hypothesis of the Lipschitz estimate always
holds with `r = 2`, because `|tanh| < 1`; this is a genuinely new
constant bound of the saturating family. -/
theorem headCE_tanh_le_add_four (t : V) (y z : V → ℝ) :
    headCE .tanh t y ≤ headCE .tanh t z + 4 := by
  have h2 : headCE .tanh t y ≤ headCE .tanh t z + 2 * 2 := by
    refine headCE_le_of_abs_sub_le _ t y z 2 ?_
    intro v
    simp only [LogitMap.apply]
    have h1 : |Real.tanh (y v)| < 1 := Real.abs_tanh_lt_one _
    have h2' : |Real.tanh (z v)| < 1 := Real.abs_tanh_lt_one _
    have h3 : |Real.tanh (y v) - Real.tanh (z v)| ≤
        |Real.tanh (y v)| + |Real.tanh (z v)| := abs_sub _ _
    linarith
  linarith

/-! ## The reduction-agnostic floor -/

/-- The batch floor: nonnegative weights give a nonnegative
`headLoss`, for every logit map and every reduction. -/
theorem headLoss_nonneg_of_nonneg_weight
    (cfg : HeadConfig ι) (t : ι → V) (z : ι → V → ℝ)
    (hw : ∀ i, 0 ≤ cfg.reduction.weight i) :
    0 ≤ headLoss cfg t z := by
  refine Finset.sum_nonneg ?_
  intro i _hi
  exact mul_nonneg (hw i) (headCE_nonneg _ _ _)

/-- The uniform reduction carries nonnegative weights, so the batch
floor holds for it unconditionally. -/
theorem headLoss_nonneg_uniform (m : LogitMap) (t : ι → V)
    (z : ι → V → ℝ) :
    0 ≤ headLoss ⟨m, .uniform⟩ t z := by
  refine headLoss_nonneg_of_nonneg_weight _ t z ?_
  intro i
  simp [Reduction.weight]
