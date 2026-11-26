/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Core.Concat
import Hagi.Model.CEHeldout
import Hagi.Model.CEDescent
import Hagi.Model.CEModel

/-!
# Independent model and objective specs, combined in semantics

The model side and the objective side of a learning problem are
defined INDEPENDENTLY,

over shared types of features and predictions; their concrete
combinations are created here, in semantics — not through cyclic
imports between model and objective modules.

- `ModelSpec Θ X V` — the model side: a logit (feature) map
  `head : Θ → X → (V → ℝ)` plus a model-side range law.
- `ObjectiveSpec V` — the objective side: a loss on predicted logits
  and a target vector, plus the floor law.
- `combineObjective` — the only way the two meet: pure composition
  `loss (head θ x) y`, with the floor law transported from the
  objective spec and the range law from the model spec.

The two demo combinations below (identity head × cross-entropy, and
identity head × squared difference) prove the independence concretely:
the same model part combines with two different objective parts, and
the resulting semantics genuinely differ.  A definitional bridge
(`singleSampleCE_eq_combine`) exhibits the existing CE safe-step
interface `Model.CEModel.singleSampleCE` as one such combination.

## Ledger: model-side / objective-side / mixed

- Model side (head/logit maps and their facts): `Model.SoftmaxHead`
  (`LogitMap`, parametric head core), `Model.CEDescent.ceLogits`
  (linear head), the gated/tanh/packed head families (`GatedCE*`,
  `TanhCEStep`, `CEPackedStep`).
- Objective side (loss functionals and their laws): `Hagi.ceOneHot` /
  `Hagi.Core.lse` (`Core.Concat`, the SSOT CE functional),
  `Model.CEHeldout.ceOneHot_nonneg` (the floor), `Model.LabelSmoothing`,
  `Model.Mixup`, `Model.Losses`, the contrastive family `Data.InfoNCE` /
  `Step.NCEExact`.
- Mixed (head, loss and descent fused in one statement):
  `Model.CEDescent` and the whole `Model.BatchCEDescent*` family, and
  the gated/nonlinear/quantized CE steps.
- `sqDiffObjective` below is a DEMO objective (no L2-on-logits SSOT
  exists in the repo).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Semantics

/-! ## The model side -/

/-- The model side of a learning problem, independent of any loss: a
logit map sending parameters and features to predicted logits over
the vocabulary `V`, together with the model-side range law (the
quadratic range coefficient of the logit displacement the head can
induce).  The law is hypothesis-form: a datum every instance carries,
not a theorem about a fixed head. -/
structure ModelSpec (Θ X V : Type) where
  /-- The logit (feature) map: parameters and one feature to
  predicted logits over the vocabulary. -/
  head : Θ → X → (V → ℝ)
  /-- Model-side quadratic range coefficient. -/
  rangeSquare : Θ → X → ℝ
  /-- The model-side range law: the coefficient is nonnegative. -/
  rangeSquare_nonneg : ∀ θ x, 0 ≤ rangeSquare θ x

/-! ## The objective side -/

/-- The objective side of a learning problem, independent of any
model: a loss on predicted logits and a target vector, with the floor
law.  The law is hypothesis-form.  (Convexity in logits is not a
field: the CE majorizer lives in consumer theorems.) -/
structure ObjectiveSpec (V : Type) where
  /-- The loss: predicted logits and target vector to a real cost. -/
  loss : (V → ℝ) → (V → ℝ) → ℝ
  /-- The floor law: the loss is nonnegative. -/
  loss_nonneg : ∀ z y, 0 ≤ loss z y

/-! ## The combination, in semantics -/

variable {Θ X V : Type}

/-- The combined semantic objective: the objective spec's loss applied
to the model spec's predicted logits.  Built ONLY from the two
records — no concrete model or objective module is involved. -/
def combineObjective (m : ModelSpec Θ X V) (o : ObjectiveSpec V) :
    Θ → X → (V → ℝ) → ℝ :=
  fun θ x y => o.loss (m.head θ x) y

/-- The floor law transports: the combined objective is nonnegative
because the objective spec's floor law holds — the model side plays
no role. -/
theorem combineObjective_nonneg (m : ModelSpec Θ X V) (o : ObjectiveSpec V)
    (θ : Θ) (x : X) (y : V → ℝ) :
    0 ≤ combineObjective m o θ x y :=
  o.loss_nonneg _ _

/-! ## Model-side instances -/

variable {V : Type} [Fintype V]

/-- The identity head: the feature vector itself is the logit vector
(the semantic analogue of `Model.SoftmaxHead.LogitMap.ident`); the
feature carrier is the raw logit feature vector `V → ℝ`.  The range
coefficient is zero: the identity head contributes no model-side
curvature. -/
def identHeadSpec : ModelSpec (V → ℝ) (V → ℝ) V where
  head _ x := x
  rangeSquare _ _ := 0
  rangeSquare_nonneg θ x := le_refl 0

/-- The fixed finite categorical linear head of `Model.CEDescent`:
features are carried by the matrix `X`, so the feature slot is
occupied by `Unit`. -/
noncomputable def linearHeadSpec {d : ℕ} (X : Matrix V (Fin d) ℝ) :
    ModelSpec (EuclideanSpace ℝ (Fin d)) Unit V where
  head θ _ := Hagi.Model.ceLogits X θ
  rangeSquare _ _ := 0
  rangeSquare_nonneg θ x := le_refl 0

/-! ## Objective-side instances -/

variable {V : Type} [Fintype V] [Nonempty V]

/-- The one-hot cross-entropy objective: the repo SSOT `Hagi.ceOneHot`
at target index `t`.  The target vector slot keeps the interface
uniform; this objective pins the target by its one-hot index (the
SSOT's own shape).  The floor is `Model.CEHeldout.ceOneHot_nonneg`. -/
noncomputable def ceOneHotObjective (t : V) : ObjectiveSpec V where
  loss z _ := Hagi.ceOneHot t z
  loss_nonneg z _ := Hagi.Model.CEHeldout.ceOneHot_nonneg t z

/-- The squared-difference objective: the sum of squared differences
between predicted logits and the target vector.  A DEMO objective;
the floor is the trivial
sum-of-squares nonnegativity. -/
def sqDiffObjective : ObjectiveSpec V where
  loss z y := ∑ v, (z v - y v) ^ 2
  loss_nonneg z y := Finset.sum_nonneg fun v _ => sq_nonneg _

/-! ## Bridge: the existing CE interface as one combination -/

open Hagi.Model in
/-- The single-sample CE safe-step interface `Model.CEModel`
 IS the combination of the linear head spec with the one-hot
cross-entropy objective: definitionally, both sides are
`Hagi.ceOneHot t (Model.CEDescent.ceLogits X θ)`. -/
theorem singleSampleCE_eq_combine {d : ℕ} (X : Matrix V (Fin d) ℝ) (t : V)
    (θ : EuclideanSpace ℝ (Fin d)) (y : V → ℝ) :
    combineObjective (linearHeadSpec X) (ceOneHotObjective t) θ () y
      = (Hagi.Model.singleSampleCE X t).loss θ := by
  simp only [combineObjective, linearHeadSpec, ceOneHotObjective,
    Hagi.Model.singleSampleCE, Hagi.Model.ceLogits]

/-! ## Independence demo: one model, two objectives -/

/-- The one-hot witness logits on the two-letter vocabulary: `z true
= 1`, `z false = 0` — exactly the target's one-hot embedding. -/
private def witnessZ : Bool → ℝ := fun v => if v = true then 1 else 0

/-- At the one-hot witness, the combined squared-difference objective
is zero: the logits equal the target exactly. -/
theorem combine_sqDiff_witness_eq_zero :
    combineObjective (identHeadSpec : ModelSpec (Bool → ℝ) (Bool → ℝ) Bool)
      sqDiffObjective witnessZ witnessZ witnessZ = 0 := by
  unfold combineObjective identHeadSpec sqDiffObjective witnessZ
  simp

/-- At the one-hot witness, the combined cross-entropy objective is
strictly positive: `log(e + 1) − 1 = log((e+1)/e) > 0` because the
target exponential is strictly below the log-sum-exp normalizer. -/
theorem combine_ce_witness_pos :
    0 < combineObjective
      (identHeadSpec : ModelSpec (Bool → ℝ) (Bool → ℝ) Bool)
      (ceOneHotObjective true) witnessZ witnessZ witnessZ := by
  have hval : Hagi.ceOneHot true witnessZ
      = Real.log (Real.exp 1 + 1) - 1 := by
    unfold Hagi.ceOneHot Hagi.Core.lse witnessZ
    simp [Real.exp_zero]
  have he : Real.exp (1:ℝ) ≠ 0 := Real.exp_ne_zero 1
  have hgt : (1:ℝ) < (Real.exp 1 + 1) / Real.exp 1 := by
    rw [one_lt_div (Real.exp_pos 1)]
    linarith [Real.exp_pos 1]
  have hlog : 0 < Real.log ((Real.exp 1 + 1) / Real.exp 1) :=
    Real.log_pos hgt
  rw [Real.log_div (by positivity) he] at hlog
  rw [Real.log_exp] at hlog
  show 0 < Hagi.ceOneHot true witnessZ
  rw [hval]
  linarith

/-- Independence, concretely: the SAME model part combined with the
two objective parts yields genuinely different semantics — the
squared-difference semantics is zero at the witness while the
cross-entropy semantics is strictly positive there. -/
theorem objectives_differ :
    combineObjective (identHeadSpec : ModelSpec (Bool → ℝ) (Bool → ℝ) Bool)
        sqDiffObjective witnessZ witnessZ witnessZ
      ≠ combineObjective
        (identHeadSpec : ModelSpec (Bool → ℝ) (Bool → ℝ) Bool)
        (ceOneHotObjective true) witnessZ witnessZ witnessZ := by
  rw [combine_sqDiff_witness_eq_zero]
  exact (ne_of_gt combine_ce_witness_pos).symm

end Hagi.Semantics
