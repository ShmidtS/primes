/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Theory.CertifyThenCommit
import Hagi.Runtime.CertChecker
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# Trunk training — certified joint trunk+head steps (C481, beat C478)

The C478 roadmap gap (item 4): every bench mode trained a LINEAR
head on a frozen carrier; the C475 joint theory
(`Hagi.Training.JointTrunkHead`) had no executable Python face.
C481 adds the trunk-training bench (`scripts/bench_bridge.py`,
`--mode trunk-train`): a NON-LINEAR trunk — an L1-denominator
rational RMSNorm surrogate (true RMSNorm divides by an irrational
√; the surrogate x/(|x|+ε) is Fraction-exact, docstring-pinned in
the bench), a linear W1, ReLU, a linear W2 — trained JOINTLY with
the linear head by certified steps.

## Coordination only — the mathematics lives in the components

This module is composition GLUE in the C479 `FullPipeline` pattern;
every substantive leg is an EXISTING theorem, cited as the
construction route:

- **JOINT step** → `headStep` route: the C475 joint majorizer
  `Hagi.Training.JointTrunkHead.joint_head_trunk_step_le`
  (CE ≤ CE − 2A²/R² + 2·HL·dd) with the parametric lip atoms
  (`rms_gain_param_disp`, `mlp_param_lip`) and the strict-commit
  criterion `joint_step_commit_strict` (2·HL·dd < 2A²/R²).
- **HEAD finetune** → `headStep` route: the C462 adaptive-majorizer
  drop (`Hagi.Theory.AdaptiveMajorizer.adaptive_descent`), as in
  C479 TRAIN.

## Honesty pins

- The bench step is a finite-difference-direction grid-snapped
  trial; NO 2A²/R² descent is claimed for it. The LIVE guarantee
  is per-step MEASURED descent (drop = obj − obj' > 0 computed
  exactly in `Fraction`s on the actual parameters) with guarded
  rollback (drop ≤ 0 ⇒ HOLD, parameters restored) — the C443/C474
  hold semantics. A, R, dd are telemetry; the C475 strict-commit
  criterion is advisory. The commit criterion consumed by the C463
  cycle is the realized drop > 0, exactly as in
  `Hagi.Theory.CertifyThenCommit.commit_drop_checked`.
- `trunkPhaseRoute` is a TAG, not a claim of component
  re-derivation; the route map only checks that a two-phase trunk
  cycle IS a C463 certify-then-commit cycle.
- `trunk_traj_drop_pos` is the list-level bridge from the
  executable checker (`checkTrajectory`, C430) to per-step drop
  positivity — the same pattern as `full_traj_drop_pos` (C479);
  it does not re-derive the probability premises of C463.

Layer decision: Theory (7), like FullPipeline — the module must
see the C463 cycle (7) and the Runtime checker (3).
-/

open MeasureTheory
open Hagi.Theory.CertifyThenCommit
open Hagi.Cert (SystemMetrics StepObligations FloorsKept)
open Hagi.Runtime

namespace Hagi.Theory.TrunkTrain

/-! ## The trunk phases and their gate routes -/

/-- The two phases of the trunk-training bench (C481
`--mode trunk-train`): the certified JOINT trunk+head step and the
certified head finetune on the frozen trunk. -/
inductive TrunkTrainPhase where
  /-- Joint trunk+head step (C475 `joint_head_trunk_step_le`
  route; the bench admits it by the measured drop with guarded
  rollback). -/
  | jointStep
  /-- Head finetune step on the frozen trunk (C462
  adaptive-majorizer headStep route, as in C479 TRAIN). -/
  | headFinetune
deriving Inhabited

/-- The construction-route map from the trunk phases to the C463
gate owners. Both routes are owned by the head gate: the joint
step IS a certified head safe-step plus the measured trunk
displacement damage (the C475 additive majorizer), and the head
finetune is the plain C462 head step. The map is a TAG — the
cycle theorem below consumes only the `CertStep` interface. -/
def trunkPhaseRoute : TrunkTrainPhase → CTCRound
  | .jointStep => .headStep
  | .headFinetune => .headStep

/-- The canonical phase order of the trunk-training cycle: a joint
step followed by a head finetune over a T = 2 horizon (the bench
trace realizes each phase with committed measured-descent steps;
holds are honest no-ops). -/
def trunkPhaseList : List TrunkTrainPhase := [.jointStep, .headFinetune]

def trunkPipelinePhases : Fin 2 → TrunkTrainPhase :=
  fun i => trunkPhaseList.getD i.val default

/-! ## The compositional soundness theorem -/

variable {S TaskId : Type}

/-- **trunk_cycle_sound (C481)**: a two-round certify-then-commit
cycle whose rounds follow the canonical trunk-training phase order
(each round owned by the routed C463 gate) inherits the complete
C463 end-to-end guarantee at the trunk-cycle horizon: the objective
telescopes against the committed drops, with probability ≥ 1 −
δtotal no commit is false, the holdout risk grows by at most ε,
the budget ledger balances, the budget stays nonnegative, the
floors are kept — AND both rounds are owned by the head gate, the
route through which the C475 joint step and the C462 finetune
discharge their certified drops. The whole content is the cited
`certify_then_commit_sound` specialization; NEW is only the
two-phase glue (`hkind` routing). -/
theorem trunk_cycle_sound {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId}
    (cyc : CertifyThenCommitCycle M obl 2)
    (hkind : ∀ i : Fin 2,
      cyc.kind i = trunkPhaseRoute (trunkPipelinePhases i))
    {Ω : Type} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (falseCommit : Fin 2 → Ω → Prop) (δ : Fin 2 → ℝ)
    (hFalse : ∀ i : Fin 2, μ.real {ω | falseCommit i ω} ≤ δ i)
    {δtotal : ℝ} (hsumd : ∑ i : Fin 2, δ i ≤ δtotal)
    {ε : ℝ} (hε : ∑ i : Fin 2, cyc.e i ≤ ε) :
    -- (b) objective telescope against the committed drops
    M.objective (cyc.t 2) ≤ M.objective (cyc.t 0)
      - ∑ i : Fin 2, cyc.dropV i
    -- (c) with high probability no commit is false
    ∧ μ.real {ω | ∃ i : Fin 2,
        cyc.commit i = true ∧ falseCommit i ω} ≤ δtotal
    -- (d) holdout risk grows by at most ε
    ∧ M.risk (cyc.t 2) ≤ M.risk (cyc.t 0) + ε
    -- (e) budget balance + nonnegativity + floors
    ∧ M.budget (cyc.t 2) + ∑ i : Fin 2, cyc.spendV i
        = M.budget (cyc.t 0)
    ∧ 0 ≤ M.budget (cyc.t 2) ∧ FloorsKept M obl (cyc.t 2)
    -- (f) both rounds are owned by the head gate
    ∧ ∀ i : Fin 2, cyc.kind i = CTCRound.headStep := by
  obtain ⟨hb, hc, hd, he, hnn, hfl⟩ :=
    certify_then_commit_sound cyc falseCommit δ hFalse hsumd hε
  refine ⟨hb, hc, hd, he, hnn, hfl, ?_⟩
  intro i
  rw [hkind i]
  cases h : trunkPipelinePhases i <;> rfl

/-! ## The witness bridge (checkTrajectory → drop positivity) -/

/-- **trunk_traj_drop_pos**: if the executable list-level checker
accepts a trunk-training trajectory witness (the C481 bench emits
ONE `CertStepData` trace for the joint cycle), then EVERY step of
the trace has a positive declared drop — the machine-checked
reason a non-certified trunk step (an inflated or non-positive
drop) can never ride the trunk trajectory. This is the bridge from
`checkTrajectory` (C430) to the per-round positivity the C463
ledger consumes; the same pattern as `full_traj_drop_pos` (C479). -/
theorem trunk_traj_drop_pos (start : ℚ)
    (ds : List Hagi.Runtime.CertStepData)
    (h : Hagi.Runtime.checkTrajectory start ds = true)
    (j : ℕ) (hj : j < ds.length) :
    0 < (ds.getD j default).drop :=
  (Hagi.Runtime.checkStep_spec
    (Hagi.Runtime.checkStep_of_checkTrajectory start ds h j hj)).1

end Hagi.Theory.TrunkTrain
