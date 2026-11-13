import Mathlib.Tactic
import Hagi.Model.BatchCEDescent
import Hagi.Model.Logic.VennHead
import Hagi.Cert.Adapters
import Hagi.Contracts.BatchCETrajectory

/-!
# CE-trained mask choice over the exact Venn head

Track B7 (master plan v3 addendum A4), C243 — the first hybrid
neuro-symbolic certificate. The 16 Boolean masks of the Venn lattice
(`Fin 4 → Bool`, a `Fintype` of size 16) are the CLASSES of a choice
problem: a log-linear head over the four Venn atom features scores
each candidate mask, and the choice is trained by cross-entropy under
the existing certified descent guard.

Wiring, end-to-end:

- `choiceFeatures` — the choice head's feature matrix:
  `X v j = vAtoms A B j * maskReal (cand v) j`, so the class-`v` logit
  of the all-ones parameterization is EXACTLY `vennHead (maskReal
  (cand v)) A B` (`choiceFeatures_logit_ones`): the log-linear choice
  head scores a mask by the exact output of the C242 Venn head for
  that mask on the same inputs.
- The choice-CE is the C223 batch CE machinery
  (`Hagi.Model.BatchCEDescent`) instantiated on the choice batch: the
  certified drop `2 * batchAlignment^2 / batchLogitRangeSquare`
  (`batchLoss_logitSafeStep_le_residual`) and the strict descent
  `batchLoss_logitSafeStep_lt` apply verbatim — no new descent math.
- `choiceCEMetrics` + `choiceCE_transitionStep_progress` — the
  canonical `Hagi.Cert` transition: a `TransitionStep` whose `CertStep`
  objective is the choice-CE descent and whose floors are kept
  trivially by nonnegativity of the CE, with the EXECUTION exactness
  supplied by `Hagi.Model.Logic.VennHead.vennHead_exact` (the executed
  head of any candidate mask computes that mask's truth value).
- `choice_certified_behavior` — witness instance: a concrete tiny batch
  (two candidate masks — constant-false and AND — one sample on
  inputs `(1, 1)`, zero start parameters, AND target) where the
  certified safe step provably strictly decreases the choice-CE
  (`batchLogitRangeSquare = 1/4`, computed exactly) AND every executed
  candidate head is exact (the 64-case bridge).

HONEST BOUNDARY (qwenbend: 'exact ≠ true'): the CE-choice certificate
covers DESCENT OF THE CHOICE-CE — training progress toward the labeled
mask — and EXACT EXECUTION of whatever mask the head settles on. It
does NOT certify that the chosen function is the right one: a head can
descend its CE faithfully and still select the wrong mask, and the
exact Venn head faithfully computes a mask that may be false of the
world. Descent is a property of training, exactness a property of
execution; correctness of the chosen hypothesis is neither.
-/

set_option linter.style.header false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace Hagi.Contracts.LogicChoiceCert

open Hagi.Model Hagi.Model.BatchCEDescent Hagi.Model.Logic
open Hagi.Data.BoolVenn Hagi.Cert.Adapters

/-! ## The choice bridge: log-linear head over Venn atom features -/

/-- All-ones parameters of the choice head (the parameterization under
which the choice logits ARE the Venn head outputs). -/
noncomputable def onesV : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 fun _ => (1 : ℝ)

theorem onesV_ofLp (j : Fin 4) : onesV.ofLp j = 1 := rfl

/-- Choice features: class `v` (a candidate mask) is scored by the
atoms it selects — `X v j = atom j * mask weight of v at j`. For the
full lattice take `ι = (Fin 4 → Bool)` (16 classes); any candidate
family embeds the same way. -/
noncomputable def choiceFeatures {ι : Type} [Fintype ι]
    (cand : ι → (Fin 4 → Bool)) (A B : ℝ) : Matrix ι (Fin 4) ℝ :=
  Matrix.of fun v j => vAtoms A B j * maskReal (cand v) j

/-- BRIDGE: at all-ones parameters the logit of class `v` is exactly
the Venn head output of mask `cand v` on the same inputs — the
neuro-symbolic join of the choice head and the exact logic layer. -/
theorem choiceFeatures_logit_ones {ι : Type} [Fintype ι]
    (cand : ι → (Fin 4 → Bool)) (A B : ℝ) (v : ι) :
    ceLogits (choiceFeatures cand A B) onesV v
      = vennHead (maskReal (cand v)) A B := by
  simp only [ceLogits, choiceFeatures, vennHead, Matrix.mulVec,
    Matrix.of_apply, dotProduct, onesV_ofLp]
  exact Finset.sum_congr rfl fun j _hj => by ring

/-! ## Witness batch: certified descent of the choice-CE -/

/-- Witness candidate masks: constant-false and AND. -/
def witCand : Fin 2 → (Fin 4 → Bool) :=
  ![fun _ => false, ![true, false, false, false]]

/-- Witness features on inputs `(A, B) = (1, 1)`: the AND atom is
hot. -/
noncomputable def witX : Fin 1 → Matrix (Fin 2) (Fin 4) ℝ :=
  ![choiceFeatures witCand 1 1]

/-- Witness start parameters: zero. -/
noncomputable def witθ : EuclideanSpace ℝ (Fin 4) := 0

/-- Witness targets: class 1 = the AND mask. -/
def witY : Fin 1 → Fin 2 := ![1]

/-- Witness feature entries: exactly one hot (class 1, atom 0). -/
theorem wit_entry (v : Fin 2) (j : Fin 4) :
    witX 0 v j = if v = 1 ∧ j = 0 then (1:ℝ) else 0 := by
  simp only [witX, choiceFeatures, witCand, vAtoms, vAtom, relu,
    maskReal]
  fin_cases v <;> fin_cases j <;> norm_num

theorem wit_logits_zero (v : Fin 2) : ceLogits (witX 0) witθ v = 0 := by
  simp [ceLogits, witθ]

theorem wit_smax (v : Fin 2) :
    Hagi.Energy.smax (ceLogits (witX 0) witθ) v = 1 / 2 := by
  unfold Hagi.Energy.smax Hagi.Prelude.softDef
  simp only [wit_logits_zero]
  simp

theorem wit_residual (v : Fin 2) :
    Hagi.Model.ceResidual (witX 0) witθ (witY 0) v
      = if v = 1 then -1 / 2 else 1 / 2 := by
  unfold Hagi.Model.ceResidual
  simp only [wit_smax, witY]
  fin_cases v <;> norm_num

theorem wit_residualTranspose (j : Fin 4) :
    Hagi.Model.residualTranspose (witX 0) witθ (witY 0) j
      = if j = 0 then -1 / 2 else 0 := by
  unfold Hagi.Model.residualTranspose
  simp only [Fin.sum_univ_two, wit_entry, wit_residual]
  fin_cases j <;> norm_num

theorem wit_meanDirection (j : Fin 4) :
    (batchMeanDirection witX witθ witY).ofLp j
      = if j = 0 then 1 / 2 else 0 := by
  rw [batchMeanDirection_eq_neg_meanResidualTranspose]
  show -(meanResidualTranspose witX witθ witY j) = _
  unfold meanResidualTranspose
  rw [Finset.sum_eq_single 0
    (fun b _ hb => absurd (Subsingleton.elim b 0) hb)
    (by simp)]
  rw [wit_residualTranspose]
  split <;> norm_num

theorem wit_dirLogit (v : Fin 2) :
    ceLogits (witX 0) (batchMeanDirection witX witθ witY) v
      = if v = 1 then 1 / 2 else 0 := by
  simp only [ceLogits, Matrix.mulVec, dotProduct, wit_meanDirection,
    wit_entry]
  fin_cases v <;> norm_num

theorem wit_sup_pos :
    Finset.sup' (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty
      (fun v => ceLogits (witX 0) (batchMeanDirection witX witθ witY) v)
      = 1 / 2 := by
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le Finset.univ_nonempty
      (fun v => ceLogits (witX 0) (batchMeanDirection witX witθ witY) v)
      (fun v _ => by rw [wit_dirLogit]; split <;> norm_num)
  · have hf1 : ceLogits (witX 0) (batchMeanDirection witX witθ witY) 1
        = 1 / 2 := by rw [wit_dirLogit]; norm_num
    exact (le_of_eq hf1.symm).trans (Finset.le_sup'
      (f := fun v => ceLogits (witX 0) (batchMeanDirection witX witθ witY) v)
      (Finset.mem_univ 1))

theorem wit_sup_neg :
    Finset.sup' (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty
      (fun v => -ceLogits (witX 0) (batchMeanDirection witX witθ witY) v)
      = 0 := by
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le Finset.univ_nonempty
      (fun v => -ceLogits (witX 0) (batchMeanDirection witX witθ witY) v)
      (fun v _ => by rw [wit_dirLogit]; split <;> norm_num)
  · have hf0 : -ceLogits (witX 0) (batchMeanDirection witX witθ witY) 0
        = 0 := by rw [wit_dirLogit]; norm_num
    exact (le_of_eq hf0.symm).trans (Finset.le_sup'
      (f := fun v => -ceLogits (witX 0) (batchMeanDirection witX witθ witY) v)
      (Finset.mem_univ 0))

theorem wit_dirLogitRange :
    dirLogitRange (witX 0) (batchMeanDirection witX witθ witY) = 1 / 2 := by
  unfold dirLogitRange
  rw [wit_sup_pos, wit_sup_neg]; norm_num

theorem wit_rangeSquare_sum :
    ∑ b, (dirLogitRange (witX b)
      (batchMeanDirection witX witθ witY)) ^ 2 = 1 / 4 := by
  rw [Finset.sum_eq_single 0
    (fun b _ hb => absurd (Subsingleton.elim b 0) hb)
    (by simp)]
  rw [wit_dirLogitRange]; norm_num

/-- The witness choice batch has positive range-square: `R' = 1/4`
(the AND atom discriminates the two candidate classes). -/
theorem wit_rangeSquare_pos : 0 < batchLogitRangeSquare witX witθ witY := by
  unfold batchLogitRangeSquare
  rw [wit_rangeSquare_sum]
  norm_num

/-! ## Canonical transition: the choice-CE under the certified guard -/

/-- Concrete system metrics for the choice-CE setting: the objective
is the true arithmetic-mean choice-CE (batch CE over the mask
classes); risk and budget are the concrete remaining levels supplied
by the caller (R1 polarity slice, as in
`Hagi.Contracts.BatchRangeBF16Cert.batchCEMetrics`); task tag `Unit`. -/
noncomputable def choiceCEMetrics {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (y : Fin B → V)
    (riskRem budgetRem : ℝ) :
    Hagi.Cert.SystemMetrics (EuclideanSpace ℝ (Fin d)) Unit where
  objective := fun θ => batchLoss X θ y
  risk := fun _ => riskRem
  budget := fun _ => budgetRem
  task := fun _ => ()

/-- Projection law: the concrete objective readout is the choice-CE. -/
theorem choiceCEMetrics_objective {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (y : Fin B → V)
    (riskRem budgetRem : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    (choiceCEMetrics X y riskRem budgetRem).objective θ = batchLoss X θ y :=
  rfl

/-- Projection law: the risk level is the constant remaining-risk
parameter at every state. -/
theorem choiceCEMetrics_risk {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (y : Fin B → V)
    (riskRem budgetRem : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    (choiceCEMetrics X y riskRem budgetRem).risk θ = riskRem := rfl

/-- Projection law: the budget level is the constant remaining-budget
parameter at every state. -/
theorem choiceCEMetrics_budget {V : Type} [Fintype V] {B d : ℕ}
    (X : Fin B → Matrix V (Fin d) ℝ) (y : Fin B → V)
    (riskRem budgetRem : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    (choiceCEMetrics X y riskRem budgetRem).budget θ = budgetRem := rfl

/-- The C223 certified safe step on the choice batch assembles into a
canonical progress `TransitionStep`: the `CertStep` objective is the
choice-CE descent with the certified drop
`2 * batchAlignment^2 / batchLogitRangeSquare`, budget/risk preserved
(zero spend, nonnegative remainders), floors kept trivially by
nonnegativity of the CE. This certifies DESCENT OF THE CHOICE-CE, not
that the chosen function is the right one (see the module boundary
statement). -/
noncomputable def choiceCE_transitionStep_progress {V : Type} [Fintype V]
    [Nonempty V] {B d : ℕ} (X : Fin B → Matrix V (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (y : Fin B → V)
    (riskRem budgetRem : ℝ)
    (hR : 0 < batchLogitRangeSquare X θ y)
    (hbudgetnn : 0 ≤ budgetRem) (hrisknn : 0 ≤ riskRem) :
    Hagi.Cert.TransitionStep (choiceCEMetrics X y riskRem budgetRem)
      (zeroFloorObligations Unit) θ (batchLogitNextParameters X θ y) := by
  have hdesc : (choiceCEMetrics X y riskRem budgetRem).objective
      (batchLogitNextParameters X θ y)
      ≤ (choiceCEMetrics X y riskRem budgetRem).objective θ
        - (2 * (batchAlignment X θ y) ^ 2 / batchLogitRangeSquare X θ y) := by
    rw [choiceCEMetrics_objective, choiceCEMetrics_objective]
    exact batchLoss_logitSafeStep_le_residual X θ y hR
  have hdrop : 0 < 2 * (batchAlignment X θ y) ^ 2
      / batchLogitRangeSquare X θ y := by
    exact div_pos (mul_pos (by norm_num)
      (sq_pos_of_pos
        (batchAlignment_pos_of_logitRangeSquare_pos X θ y hR))) hR
  have hfloors : Hagi.Cert.FloorsKept (choiceCEMetrics X y riskRem budgetRem)
      (zeroFloorObligations Unit) (batchLogitNextParameters X θ y) :=
    floorsKept_zeroFloor
      (Hagi.Contracts.BatchCETrajectory.batchLoss_nonneg X
        (batchLogitNextParameters X θ y) y)
  have hbudget : (choiceCEMetrics X y riskRem budgetRem).budget
      (batchLogitNextParameters X θ y)
      = (choiceCEMetrics X y riskRem budgetRem).budget θ :=
    (choiceCEMetrics_budget X y riskRem budgetRem
      (batchLogitNextParameters X θ y)).trans
      ((choiceCEMetrics_budget X y riskRem budgetRem θ).symm)
  have hrisk : (choiceCEMetrics X y riskRem budgetRem).risk
      (batchLogitNextParameters X θ y)
      = (choiceCEMetrics X y riskRem budgetRem).risk θ :=
    (choiceCEMetrics_risk X y riskRem budgetRem
      (batchLogitNextParameters X θ y)).trans
      ((choiceCEMetrics_risk X y riskRem budgetRem θ).symm)
  exact Hagi.Cert.TransitionStep.progress
    (descentCertStep _ hdrop hdesc hbudget hbudgetnn hrisk hrisknn hfloors)

/-! ## End-to-end witness: certified descent + exact execution -/

/-- END-TO-END WITNESS: on the concrete choice batch there is a
positive certified drop `Δ` such that the C223 safe step decreases the
choice-CE by at least `Δ`, AND the executed head of every candidate
mask is exact (the 64-case Venn bridge). Together: certified descent
of the choice-CE plus exact execution of the chosen function — the
hybrid neuro-symbolic certificate. The statement claims nothing about
the chosen mask being the right one for a task (honest boundary,
module docstring). -/
theorem choice_certified_behavior :
    ∃ Δ : ℝ, 0 < Δ ∧
      batchLoss witX (batchLogitNextParameters witX witθ witY) witY
        ≤ batchLoss witX witθ witY - Δ ∧
      ∀ (i : Fin 2) (a b : Bool),
        vennHead (maskReal (witCand i)) (s a) (s b)
          = (if vennBool (witCand i) a b then (1:ℝ) else 0) := by
  refine ⟨2 * (batchAlignment witX witθ witY) ^ 2
      / batchLogitRangeSquare witX witθ witY, ?_, ?_, fun i a b =>
        vennHead_exact (witCand i) a b⟩
  · exact div_pos (mul_pos (by norm_num)
      (sq_pos_of_pos
        (batchAlignment_pos_of_logitRangeSquare_pos witX witθ witY
          wit_rangeSquare_pos))) wit_rangeSquare_pos
  · exact batchLoss_logitSafeStep_le_residual witX witθ witY
      wit_rangeSquare_pos

end Hagi.Contracts.LogicChoiceCert
