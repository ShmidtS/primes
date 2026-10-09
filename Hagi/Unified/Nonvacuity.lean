/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.MasterHAGI
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

namespace Hagi.Nonvacuity

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
  gen := ⟨0, 0, 0, 0, 0⟩

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

end Hagi.Nonvacuity
