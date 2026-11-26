/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Runtime.CertChecker
import Hagi.Theory.CertifyThenCommit
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# Full pipeline — the unified six-phase cycle

The bench modes exercised the phases
SEPARATELY (cert-ce, ef21-step, hadamard-tern, grow, grow-stop);
no single certified trajectory ran the WHOLE lifecycle on one
objective chain. This module adds the unified composition: ONE task
passes six phases back to back — TRAIN, EF21 (in-step quantized
compression), HADAMARD-TERN (measured-coherence gated ternary
jump), GROW (block admission), MERGE (measured-δ branch merge),
STOP (Ville anytime holdout stop) — as ONE `CertStepData` trace.

## Coordination only — the mathematics lives in the components

This module is the composition GLUE; every substantive leg is an
EXISTING theorem, cited as the construction route:

- **TRAIN** → `headStep` route: the adaptive-majorizer drop
  `Hagi.Theory.AdaptiveMajorizer.adaptive_descent` (the bench face:
  certified GD steps with η = 1/L, BlockSmooth).
- **EF21** → `compress` route: the in-step identities
  `Hagi.Theory.EF21InStep` (telescope, energy split; reject-hold
  semantics `ef21_reject_hold`) on the fixed-scale quantizer.
- **HADAMARD-TERN** → `compress` route: the measured gate
  `Hagi.Theory.HadamardIncoherence.hadamardRotateBenefits`
  (rotate-if-measured-better) with the ternary jump criterion
  (`Hagi.Theory.CertTernaryJump.ternary_hold_rejected` for holds).
- **GROW** → `growBlock` route: the admission margin
  `Hagi.Theory.BlockAdmission.block_admission_sound` /
  `noBlockAdmissionWithoutMargin`.
- **MERGE** → `compress` route: the measured-δ gate
  `Hagi.Theory.NonlinearMerge.nonlinear_merge_bound` /
  `merge_gate_meas` (`merge_unsafe_without_measurement` shows why
  the measured residual is required).
- **STOP** → `growBlock` route: the Ville stop
  `Hagi.Theory.AnytimeHoldoutStop.grow_stop_sound` /
  `stop_blocks_admission` — the stop lives INSIDE the growth gate.

The cycle theorem consumed below is `certify_then_commit_sound`:
rounds owned by gate kinds, commits carry certified ledger
steps, holds are no-ops, the stop blocks commits.

## Limits

- **NEW here is only the glue**: the six-phase tag type, the route
  map into the four gate owners, the T = 6 specialization of
  `certify_then_commit_sound`, and the witness bridge
  (`full_traj_drop_pos`) from the executable list-level checker
  (`checkTrajectory`) to per-step drop positivity. No
  component mathematics is restated.
- **The route map is a TAG**, not a claim of component
  re-derivation: the bench pipeline (`scripts/bench_bridge.py`,
  `--mode full-pipeline`) discharges each phase's gate through its
  cited component; the theory here only checks that a six-phase
  cycle IS a certify-then-commit cycle.
- **The bridge is list-level**: `checkTrajectory` checks the
  reported readouts (positive drop, real descent, chained
  objectives); it does not re-derive the probability premises of
the stop — those remain premise-form.

Layer: Theory (7), like CertifyThenCommit — the module must see
the cycle (7) and the Runtime checker (3).
-/

open MeasureTheory
open Hagi.Theory.CertifyThenCommit
open Hagi.Cert (SystemMetrics StepObligations FloorsKept)
open Hagi.Runtime

namespace Hagi.Theory.FullPipeline

/-! ## The six phases and their gate routes -/

/-- The six phases of the unified full pipeline (bench
`--mode full-pipeline`): certified training, EF21 in-step
quantized compression, the coherence-gated ternary jump, growth
block admission, the measured-δ branch merge, and the Ville
anytime stop. -/
inductive FullPipelinePhase where
  /-- Certified training steps (headStep route). -/
  | train
  /-- EF21 in-step quantized steps with error feedback. -/
  | ef21Step
  /-- Coherence-gated ternary quantization jump. -/
  | hadamardTern
  /-- Growth block admission by the LCB margin. -/
  | grow
  /-- Branch merge under the measured-δ gate. -/
  | merge
  /-- Ville anytime holdout stop. -/
  | stop
deriving Inhabited
/-- The construction-route map from the six pipeline phases to the
four gate owners. Each route names the component theorem
family that discharges the phase's gate (see the module docstring
for the citations); the map is a TAG — the cycle theorem below
consumes only the `CertStep` interface. -/
def fullPhaseRoute : FullPipelinePhase → CTCRound
  | .train => .headStep
  | .ef21Step => .compress
  | .hadamardTern => .compress
  | .grow => .growBlock
  | .merge => .compress
  | .stop => .growBlock

/-- The canonical phase order of the unified pipeline: train,
ef21, hadamard-tern, grow, merge, stop — one round per phase over
a T = 6 horizon (the bench trace realizes each phase with at
least one committed step or an honest hold). Realized as list
lookup so no equation-compiler match lemmas are generated. -/
def fullPhaseList : List FullPipelinePhase :=
  [.train, .ef21Step, .hadamardTern, .grow, .merge, .stop]

def fullPipelinePhases : Fin 6 → FullPipelinePhase :=
  fun i => fullPhaseList.getD i.val default

theorem fullPipelinePhases_stop : fullPipelinePhases ⟨5, by omega⟩ = .stop := by
  simp [fullPipelinePhases, fullPhaseList]

theorem fullPipelinePhases_eq_stop {i : Fin 6}
    (h : fullPipelinePhases i = .stop) : i = ⟨5, by omega⟩ := by
  fin_cases i <;> simp [fullPipelinePhases, fullPhaseList] at h ⊢

/-! ## The compositional soundness theorem -/

variable {S TaskId : Type}

/-- **full_pipeline_sound**: a six-round certify-then-commit
cycle whose rounds follow the canonical full-pipeline phase order
(each round owned by the routed gate) inherits the complete
 end-to-end guarantee at the pipeline horizon: the objective
telescopes against the committed drops, with probability ≥ 1 −
δtotal no commit is false, the holdout risk grows by at most ε,
the budget ledger balances, the budget stays nonnegative, the
floors are kept — AND the terminal (stop) round is owned by the
growth gate, the route through which the stop blocks every
later commit. The whole content is the cited
`certify_then_commit_sound` specialization; NEW is only the
six-phase glue (`hkind` routing and the terminal-round
consequence). -/
theorem full_pipeline_sound {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId}
    (cyc : CertifyThenCommitCycle M obl 6)
    (hkind : ∀ i : Fin 6,
      cyc.kind i = fullPhaseRoute (fullPipelinePhases i))
    {Ω : Type} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (falseCommit : Fin 6 → Ω → Prop) (δ : Fin 6 → ℝ)
    (hFalse : ∀ i : Fin 6, μ.real {ω | falseCommit i ω} ≤ δ i)
    {δtotal : ℝ} (hsumd : ∑ i : Fin 6, δ i ≤ δtotal)
    {ε : ℝ} (hε : ∑ i : Fin 6, cyc.e i ≤ ε) :
    -- (b) objective telescope against the committed drops
    M.objective (cyc.t 6) ≤ M.objective (cyc.t 0)
      - ∑ i : Fin 6, cyc.dropV i
    -- (c) with high probability no commit is false
    ∧ μ.real {ω | ∃ i : Fin 6,
        cyc.commit i = true ∧ falseCommit i ω} ≤ δtotal
    -- (d) holdout risk grows by at most ε
    ∧ M.risk (cyc.t 6) ≤ M.risk (cyc.t 0) + ε
    -- (e) budget balance + nonnegativity + floors
    ∧ M.budget (cyc.t 6) + ∑ i : Fin 6, cyc.spendV i
        = M.budget (cyc.t 0)
    ∧ 0 ≤ M.budget (cyc.t 6) ∧ FloorsKept M obl (cyc.t 6)
    -- (f) the terminal stop round is owned by the growth gate
    ∧ cyc.kind ⟨5, by omega⟩ = CTCRound.growBlock := by
  obtain ⟨hb, hc, hd, he, hnn, hfl⟩ :=
    certify_then_commit_sound cyc falseCommit δ hFalse hsumd hε
  refine ⟨hb, hc, hd, he, hnn, hfl, ?_⟩
  rw [hkind ⟨5, by omega⟩]
  rfl

/-- **Stop rounds of the full pipeline never commit** (
coordination law specialized to the six-phase order): when the
pipeline's stop-phase round fires its anytime holdout stop, that
round HOLDS — no growth block, no ledger entry, no drop claim
(`stop_never_commits`). -/
theorem full_pipeline_stop_never_commits {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId}
    (cyc : CertifyThenCommitCycle M obl 6)
    (i : Fin 6) (_hphase : fullPipelinePhases i = .stop)
    (hstop : cyc.stop i = true) : cyc.commit i = false :=
  stop_never_commits cyc i hstop

/-! ## The witness bridge (checkTrajectory → drop positivity) -/

/-- **full_traj_drop_pos**: if the executable list-level checker
accepts a trajectory witness (the bench emits ONE
`CertStepData` trace for the whole six-phase cycle), then EVERY
step of the trace has a positive declared drop — the machine-
checked reason a broken phase (an inflated or non-positive drop)
can never ride the unified trajectory. This is the bridge from
`checkTrajectory` to the per-round positivity
ledger consumes. -/
theorem full_traj_drop_pos (start : ℚ)
    (ds : List Hagi.Runtime.CertStepData)
    (h : Hagi.Runtime.checkTrajectory start ds = true)
    (j : ℕ) (hj : j < ds.length) :
    0 < (ds.getD j default).drop :=
  (Hagi.Runtime.checkStep_spec
    (Hagi.Runtime.checkStep_of_checkTrajectory start ds h j hj)).1

end Hagi.Theory.FullPipeline

/-! ## TrunkTrain — trunk-loop certification glue (ns Hagi.Theory.TrunkTrain preserved) -/

set_option relaxedAutoImplicit false

/-!
# Trunk training — certified joint trunk+head steps

Every bench mode trained a LINEAR
head on a frozen carrier; the joint theory
(`Hagi.Training.JointTrunkHead`) had no executable Python face.
This module adds the trunk-training bench (`scripts/bench_bridge.py`,
`--mode trunk-train`): a NON-LINEAR trunk — an L1-denominator
rational RMSNorm surrogate (true RMSNorm divides by an irrational
√; the surrogate x/(|x|+ε) is Fraction-exact, stated in the docstring in
the bench), a linear W1, ReLU, a linear W2 — trained JOINTLY with
the linear head by certified steps.

## Coordination only — the mathematics lives in the components

This module is composition GLUE (the `FullPipeline` pattern);
every substantive leg is an EXISTING theorem, cited as the
construction route:

- **JOINT step** → `headStep` route: the joint majorizer
  `Hagi.Training.JointTrunkHead.joint_head_trunk_step_le`
  (CE ≤ CE − 2A²/R² + 2·HL·dd) with the parametric lip atoms
  (`rms_gain_param_disp`, `mlp_param_lip`) and the strict-commit
  criterion `joint_step_commit_strict` (2·HL·dd < 2A²/R²).
- **HEAD finetune** → `headStep` route: the adaptive-majorizer
  drop (`Hagi.Theory.AdaptiveMajorizer.adaptive_descent`), as in
 TRAIN.

## Limits

- The bench step is a finite-difference-direction grid-snapped
  trial; NO 2A²/R² descent is claimed for it. The LIVE guarantee
  is per-step MEASURED descent (drop = obj − obj' > 0 computed
  exactly in `Fraction`s on the actual parameters) with guarded
  rollback (drop ≤ 0 ⇒ HOLD, parameters restored)
  hold semantics. A, R, dd are telemetry; the strict-commit
  criterion is advisory. The commit criterion consumed by the
  cycle is the realized drop > 0, exactly as in
  `Hagi.Theory.CertifyThenCommit.commit_drop_checked`.
- `trunkPhaseRoute` is a TAG, not a claim of component
  re-derivation; the route map only checks that a two-phase trunk
  cycle IS a certify-then-commit cycle.
- `trunk_traj_drop_pos` is the list-level bridge from the
  executable checker (`checkTrajectory`) to per-step drop
  positivity — the same pattern as `full_traj_drop_pos`;
  it does not re-derive the probability premises of the stop.

Layer: Theory (7), like FullPipeline — the module must see
the cycle (7) and the Runtime checker (3).
-/

open MeasureTheory
open Hagi.Theory.CertifyThenCommit
open Hagi.Cert (SystemMetrics StepObligations FloorsKept)
open Hagi.Runtime

namespace Hagi.Theory.TrunkTrain

/-! ## The trunk phases and their gate routes -/

/-- The two phases of the trunk-training bench
(`--mode trunk-train`): the certified JOINT trunk+head step and the
certified head finetune on the frozen trunk. -/
inductive TrunkTrainPhase where
  /-- Joint trunk+head step (`joint_head_trunk_step_le`
  route; the bench admits it by the measured drop with guarded
  rollback). -/
  | jointStep
  /-- Head finetune step on the frozen trunk
  (adaptive-majorizer headStep route, as TRAIN). -/
  | headFinetune
deriving Inhabited

/-- The construction-route map from the trunk phases to the
gate owners. Both routes are owned by the head gate: the joint
step IS a certified head safe-step plus the measured trunk
displacement damage (the additive majorizer), and the head
finetune is the plain head step. The map is a TAG — the
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

/-- **trunk_cycle_sound**: a two-round certify-then-commit
cycle whose rounds follow the canonical trunk-training phase order
(each round owned by the routed gate) inherits the complete
 end-to-end guarantee at the trunk-cycle horizon: the objective
telescopes against the committed drops, with probability ≥ 1 −
δtotal no commit is false, the holdout risk grows by at most ε,
the budget ledger balances, the budget stays nonnegative, the
floors are kept — AND both rounds are owned by the head gate, the
route through which the joint step and the finetune
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
accepts a trunk-training trajectory witness (the bench emits
ONE `CertStepData` trace for the joint cycle), then EVERY step of
the trace has a positive declared drop — the machine-checked
reason a non-certified trunk step (an inflated or non-positive
drop) can never ride the trunk trajectory. This is the bridge from
`checkTrajectory` to the per-round positivity
ledger consumes; the same pattern as `full_traj_drop_pos`. -/
theorem trunk_traj_drop_pos (start : ℚ)
    (ds : List Hagi.Runtime.CertStepData)
    (h : Hagi.Runtime.checkTrajectory start ds = true)
    (j : ℕ) (hj : j < ds.length) :
    0 < (ds.getD j default).drop :=
  (Hagi.Runtime.checkStep_spec
    (Hagi.Runtime.checkStep_of_checkTrajectory start ds h j hj)).1

end Hagi.Theory.TrunkTrain

