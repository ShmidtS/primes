/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.MasterHAGI
import Hagi.Unified.MergeBridge
import Hagi.Runtime.TernaryExact

set_option linter.style.header false

/-!
# R263 (audit §2.1): a NONVACUITY WITNESS for `CorePremises`

The audit's central complaint: the capstone's premise set
`CorePremises` is never shown satisfiable — no `example`, no
`#guard`, nothing pins the 15 conjuncts to a real cycle.

This module exhibits ONE concrete cycle where every `h_emp_*`
stage law holds with equality (the degenerate-but-consistent
ledger instantiation), and — the substantive part — the
quantization-distortion conjunct `quantErr ≤ 1/2` (h_emp_dist)
is DERIVED from the entry-level ternary theory
(`Runtime.TernaryExact.qTern_error_in`, itself delegating to
`Energy.Ternary.roundTern_error_scaled` ← `roundTern_error`),
not assumed:

  quantErr := |w₀ − qTern 1 w₀| with w₀ = 1/4 (a real
  off-grid weight; the ternary quantizer rounds it to 0), and
  the half-step bound is the ternary rounding theorem.

This is audit stage 7, item 3 (witnesses of nonvacuity) and
the first `h_emp_*`-shaped conjunct fed by a Core-layer
theorem. The remaining stage laws are still chosen as
equalities (a ledger instantiation); deriving h_emp_grow /
h_emp_merge from the Hadamard/block-diag layer is the open
frontier.
-/

open Real Finset InnerProductSpace Hagi Hagi.Foundations

namespace Hagi.Unified

/-- The ternary-grounded distortion of the witness weight:
the compressed weight is `qTern 1 (1/4) = roundTern (1/4) = 0`,
and the half-step bound is `qTern_error_in` (delegating to
`roundTern_error_scaled` ← `roundTern_error`). -/
theorem witness_quantErr_bounded :
    |(1/4 : ℝ) - qTern 1 (1/4)| ≤ 1 / 2 := by
  have hin : ternInRange 1 (1/4) := by
    unfold ternInRange
    norm_num
  exact qTern_error_in 1 (1/4) one_pos hin

section Witness

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The witness cycle: one pre-state `S₀` at the origin with
zero gaps/gains/costs/risks and energies pinned at a common
`E`; the probe telemetry is the zero vector and the compressed
weight is `1/4` with its ternary distortion carried by
`witness_quantErr_bounded`. -/
noncomputable def S₀ (E : ℝ) [NormedAddCommGroup X] [InnerProductSpace ℝ X] :
    Hagi.GenState X where
  weightDim := 1
  weights := fun _ => 1/4
  params := 0
  experts := 0
  energy := E
  protectedRisk := 0
  budget := 0
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 0, L := 1, kappa := 0, s := 1 }
  effects := {
    growGain := 0
    growCost := 0
    growRisk := 0
    growEnergy := E
    mergeEnergy := E
    mergeRisk := 0
    jointEnergy := E
    jointRisk := 0
    jointCost := 0
    quantErr := |1/4 - qTern 1 (1/4)|
    compressEnergy := E
    compressRisk := 0
  }
  gen := ⟨0, 0, 0, 0, 0⟩

/-- The post-cycle state: the composite
`compress (joint (merge (grow S₀)))` on the three carriers the
account and potential laws read, with the (unconstrained)
remaining telemetry left at the pre-state values. -/
noncomputable def S₁ (E : ℝ) [NormedAddCommGroup X] [InnerProductSpace ℝ X] :
    Hagi.GenState X where
  weightDim := 1
  weights := fun _ => 1/4
  params := 0
  experts := 1
  energy := E
  protectedRisk := 0
  budget := 0
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 0, L := 1, kappa := 0, s := 1 }
  effects := {
    growGain := 0
    growCost := 0
    growRisk := 0
    growEnergy := E
    mergeEnergy := E
    mergeRisk := 0
    jointEnergy := E
    jointRisk := 0
    jointCost := 0
    quantErr := |1/4 - qTern 1 (1/4)|
    compressEnergy := E
    compressRisk := 0
  }
  gen := ⟨0, 0, 0, 0, 0⟩

/-!
## Non-idle witness (R357): positive gap and gain

`corePremises_nonvacuous` pins the 15 conjuncts at equality
with zero gap/gain — satisfiable but degenerate. The NON-idle
witness below feeds the merge conjunct with the STRICT Jensen
gap of two genuinely disagreeing experts (`jensenGap_pos_witness`,
R356): `gap := g > 0`, `growGain := g`, energies chained
`E → E−g → E−2g`, so the cycle strictly decreases the energy
ledger while every `h_emp_*` law holds. h_emp_merge is here
INSTANTIATED by the Core lse theory (MergeBridge), not chosen
freely.
-/

/-- The measured strict gap of the witness disagreement. -/
noncomputable def witnessGap : ℝ :=
  jensenGap (fun _ : Fin 2 => (0:ℝ))
    (fun i : Fin 2 => if i = 0 then (1:ℝ) else -1)

theorem witnessGap_pos : 0 < witnessGap :=
  jensenGap_pos_witness 1 one_ne_zero

/-- The non-idle pre-state: `gap := g > 0`, `growGain := g`,
energies chained `E → E−g → E−2g` (grow, then merge at the
strict gap); the joint and compress stages pass through at
`eta = 0`, `kappa = 0`. -/
noncomputable def Spos (E : ℝ) : Hagi.GenState X where
  weightDim := 1
  weights := fun _ => 1/4
  params := 0
  experts := 0
  energy := E
  protectedRisk := 0
  budget := 0
  gap := witnessGap
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 0, L := 1, kappa := 0, s := 1 }
  effects := {
    growGain := witnessGap
    growCost := 0
    growRisk := 0
    growEnergy := E - witnessGap
    mergeEnergy := E - 2 * witnessGap
    mergeRisk := 0
    jointEnergy := E - 2 * witnessGap
    jointRisk := 0
    jointCost := 0
    quantErr := |1/4 - qTern 1 (1/4)|
    compressEnergy := E - 2 * witnessGap
    compressRisk := 0
  }
  gen := ⟨0, 0, 0, 0, 0⟩

/-- The non-idle post-state: the composite successor's
ledger fields (energy = the compress stage's output `E − 2g`)
with the expert count advanced. -/
noncomputable def Spos' (E : ℝ) : Hagi.GenState X :=
  { Spos E with experts := 1, energy := E - 2 * witnessGap }

/-- The productive TRAJECTORY witness state at step t:
energy strictly decreases `E − 2t·g` per step-pair, gap and
gain stay at the strict Jensen level `g`, capability grows
`t·g`. -/
noncomputable def Straj (E g : ℝ) (t : ℕ) : Hagi.GenState X where
  weightDim := 1
  weights := fun _ => 1/4
  params := 0
  experts := t
  energy := E - 2 * t * g
  protectedRisk := 0
  budget := 1
  gap := g
  dataField := 0
  capability := t * g
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 0, L := 1, kappa := 0, s := 1 }
  effects := {
    growGain := g
    growCost := 0
    growRisk := 0
    growEnergy := E - (2 * t + 1) * g
    mergeEnergy := E - (2 * t + 2) * g
    mergeRisk := 0
    jointEnergy := E - (2 * t + 2) * g
    jointRisk := 0
    jointCost := 0
    quantErr := |1/4 - qTern 1 (1/4)|
    compressEnergy := E - (2 * t + 2) * g
    compressRisk := 0
  }
  gen := ⟨0, 0, 0, 0, 0⟩

/-- **The productive trajectory witness** (R369, audit v7
§5.3): for EVERY horizon T there is a state trajectory on
which `CorePremises` holds at EVERY step with strictly
positive gap and gain and strictly decreasing energy —
E − 2t·g → E − 2(t+1)·g — while capability grows linearly
`t·g`. This is the trajectory-level (category-2) witness:
not one pair of states, but the full contract along the
whole horizon. -/
theorem corePremises_trajectory_productive (E g : ℝ)
    (hg : 0 < g) (T : ℕ) :
    ∃ S : ℕ → Hagi.GenState X, ∀ t < T,
      CorePremises (S t) (S (t + 1)) 0 (fun _ => 0)
        ∧ (S (t + 1)).toGrowthState.energy
          < (S t).toGrowthState.energy
        ∧ 0 < (S t).toGrowthState.gap
        ∧ 0 < (S (t + 1)).toGrowthState.capability
            - (S t).toGrowthState.capability := by
  refine ⟨fun t => Straj E g t, fun t ht => ?_⟩
  unfold CorePremises Straj
  norm_num [Qgen, Qvec, grow, merge, joint, compress]
  have hq := witness_quantErr_bounded
  have hT : (0:ℝ) ≤ (t:ℝ) := by positivity
  refine ⟨⟨hg.le, by linarith [hT], by linarith [hT], hq,
    by left; ring⟩, by linarith [hg, hT], hg,
    by nlinarith [hg, hT]⟩
/-- **The non-idle nonvacuity witness**: `CorePremises` is
satisfiable with a STRICTLY positive Jensen gap and gain —
the cycle's energy ledger strictly decreases (`S'.energy =
E − 2g < E`), h_emp_merge carried by the Core lse theory. -/
theorem corePremises_nonvacuous_strict (E : ℝ) :
    ∃ S S' : Hagi.GenState X, ∃ epsQ : ℝ, ∃ w : Fin 5 → ℝ,
      CorePremises S S' epsQ w ∧ 0 < S.toGrowthState.gap
        ∧ 0 < S.toGrowthState.effects.growGain := by
  refine ⟨Spos E, Spos' E, 0, fun _ => 0, ?_, ?_, ?_⟩
  · unfold CorePremises Spos Spos'
    norm_num [Qgen, Qvec, grow, merge, joint, compress]
    refine ⟨le_of_lt witnessGap_pos, by linarith, witness_quantErr_bounded, rfl, rfl⟩
  · exact witnessGap_pos
  · exact witnessGap_pos

/-- **The nonvacuity witness**: `CorePremises` is satisfiable —
`S₀ E` and its composite successor `S₁ E` satisfy all 15
conjuncts, with h_emp_dist carried by the ternary rounding
theorem and every other stage law instantiated at equality. -/
theorem corePremises_nonvacuous (E : ℝ) :
    ∃ S S' : Hagi.GenState X, ∃ epsQ : ℝ, ∃ w : Fin 5 → ℝ,
      CorePremises S S' epsQ w := by
  refine ⟨S₀ E, S₁ E, 0, fun _ => 0, ?_⟩
  unfold CorePremises S₀ S₁ grow merge joint compress
  norm_num [Qgen, Qvec]
  exact witness_quantErr_bounded

end Witness

end Hagi.Unified
