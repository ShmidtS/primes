/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.InfoCore
import Hagi.Core.Concat
import Hagi.Energy.PairwiseCategorical

set_option linter.style.header false

/-!
# Pseudolikelihood as local conditional cross-entropy

Track E1 (addendum A9, CRAM / arXiv:2611.17309): the pseudolikelihood
objective of a categorical pairwise energy is EXACTLY the mean local
cross-entropy over the CRAM-sign conditional logits — reducing it to
the existing `Hagi.Prelude.ceDef` / `Hagi.Prelude.softDef` machinery
(the C235 Prelude spine), so the CEDescent toolchain applies to
pseudolikelihood training by construction, with no new CE theory.

* `conditionalLogit` — the local logits `z_ia = −H(y^{i←a})` (CRAM
  sign: LOW energy = HIGH logit).
* `conditionalDist` — the local Gibbs conditional
  `q_i(a) = softDef z_i ∝ exp(−H(y^{i←a}))`.
* `pseudolikelihoodObjective` — `J = (1/|ι|) Σ_i −log q_i(y_i)`,
  written with `Hagi.Core.ceOneHot` (the `-log q_i(y_i)` term IS
  `ceOneHot (y i) z_i`, since `-log q_i(y_i) = lse z_i − z_i(y i)`).
* `pseudolikelihood_eq_conditional_ce` — (E1 MAIN) `J` equals the mean
  of `Hagi.Prelude.ceDef (Pi.single (y i) 1) (Hagi.Prelude.softDef z_i)`
  over `i`: pseudolikelihood is local conditional cross-entropy on the
  Prelude CE spine (`Hagi.Core.ceOneHot_eq_ceDef_pi_single`, termwise).
* `pseudolikelihood_nonneg` — `0 ≤ J` (every local CE term is
  nonnegative; division by the positive variable count).

## Sign-adapter warning (CRAM vs classic Hopfield)

The logits follow the CRAM convention `z = −H`, conditionals
`q ∝ exp(−H)` (low energy = high probability). The classic Hopfield
file `Hagi/StatMech/Hopfield/Model.lean` uses `Z = Σ exp(β·E)` with
`H = −E` — the OPPOSITE sign. Any bridge to classic Hopfield MUST be
an explicit sign adapter; none is claimed here.

## Honest boundaries

Pseudolikelihood is NOT the full likelihood: it is the exact local
conditional objective only. Nothing here asserts descent in `θ`
(CertTrain) or free-energy descent in `p` (CertReason) — those are
separate certificates (A9), E2+ scope.
-/

namespace Hagi.Model.EnergyReasoning

open Hagi.Energy (pairwiseEnergy)
open Hagi.Core (ceOneHot)
open Hagi.Prelude (softDef ceDef)

section Conditional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Local conditional logits `z_ia = −H(y^{i←a})` where `y^{i←a}`
replaces coordinate `i` of the observed configuration by value `a`
(CRAM sign convention: low energy = high logit; see the module
docstring's sign-adapter warning). -/
noncomputable def conditionalLogit (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y : ι → α) (i : ι) : α → ℝ :=
  fun a => -pairwiseEnergy B K (Function.update y i a)

/-- Local Gibbs conditional `q_i(a) = softDef z_i(a) ∝ exp(−H(y^{i←a}))`
on the canonical Prelude softmax spine. -/
noncomputable def conditionalDist (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ)
    (y : ι → α) (i : ι) : α → ℝ :=
  softDef (conditionalLogit B K y i)

/-- Pseudolikelihood objective
`J = (1/|ι|) Σ_i −log q_i(y_i) = (1/|ι|) Σ_i ceOneHot (y i) z_i`
(each `-log q_i(y_i)` term is `ceOneHot (y i) z_i` because
`-log q_i(y_i) = lse z_i − z_i (y i)` on the `softDef`/`lse` spine). -/
noncomputable def pseudolikelihoodObjective (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (y : ι → α) : ℝ :=
  (∑ i, ceOneHot (y i) (conditionalLogit B K y i)) / (Fintype.card ι : ℝ)

end Conditional

section Identities

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- (E1 MAIN) The pseudolikelihood objective equals the MEAN of local
conditional cross-entropies on the canonical Prelude CE spine:
`J = (1/|ι|) Σ_i ceDef (δ_{y i}) (softDef z_i)` with one-hot targets
`δ_{y i} = Pi.single (y i) 1` and logits `z_i = conditionalLogit`.
Consequence: pseudolikelihood training is cross-entropy training
against the local Gibbs conditionals — the existing CEDescent /
CEGradient machinery applies by construction, no new CE theory. -/
theorem pseudolikelihood_eq_conditional_ce [Nonempty α]
    (B : ι → α → ℝ) (K : ι → ι → α → α → ℝ) (y : ι → α) :
    pseudolikelihoodObjective B K y
      = (∑ i, ceDef (Pi.single (y i) 1) (softDef (conditionalLogit B K y i)))
        / (Fintype.card ι : ℝ) := by
  unfold pseudolikelihoodObjective
  exact congrArg (· / (Fintype.card ι : ℝ))
    (Finset.sum_congr rfl fun i _ =>
      Hagi.Core.ceOneHot_eq_ceDef_pi_single (y i)
        (conditionalLogit B K y i))

omit [DecidableEq α] in
/-- (E1) Pseudolikelihood is nonnegative: every local term
`ceOneHot (y i) z_i = lse z_i − z_i (y i) ≥ 0` (the target exponential
is one term of the log-sum-exp normalizer), the variable count is
positive for nonempty `ι`. -/
theorem pseudolikelihood_nonneg [Nonempty ι] [Nonempty α] (B : ι → α → ℝ)
    (K : ι → ι → α → α → ℝ) (y : ι → α) :
    0 ≤ pseudolikelihoodObjective B K y := by
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  refine div_nonneg ?_ hcard.le
  refine Finset.sum_nonneg fun i _ => ?_
  have hpos : (0 : ℝ) < ∑ v, Real.exp (conditionalLogit B K y i v) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hterm : Real.exp (conditionalLogit B K y i (y i))
      ≤ ∑ v, Real.exp (conditionalLogit B K y i v) :=
    Finset.single_le_sum (fun v _ => (Real.exp_pos _).le)
      (Finset.mem_univ (y i))
  have hlog := Real.log_le_log (Real.exp_pos _) hterm
  rw [Real.log_exp] at hlog
  unfold ceOneHot Hagi.Core.lse
  unfold conditionalLogit at hlog ⊢
  linarith

end Identities

end Hagi.Model.EnergyReasoning
