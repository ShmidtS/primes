import Mathlib.Tactic
import Hagi.Cert.StepGen

/-!
# EvalBinding — certificates bound to real evaluation (A16, C378)

A16 directive, top-priority item: every certificate must bind to REAL
evaluation `Eval(θ, A, B)` — the actual loss for parameters θ,
architecture A, batch B — and the risk channel must be split into
THREE type-distinct concepts instead of one conflated `ℝ` risk.

* `RiskExposure` / `RiskRemaining` / `ConfidenceRadius` — three
  DISTINCT structures (single field + proof).  Different types mean
  accidental conflation (passing a confidence radius where the
  remaining-risk readout is expected) is a TYPE error, not a silent
  `ℝ` coercion.  The frozen kernel `CertStepGen.riskRem : ℝ` is NOT
  changed (Freeze); the adapter `CertStepGen.toRiskRemaining` maps it
  into the typed world.
* `EvalFn` / `MachineEvalBridge` / `EvalBinding` — the evaluation
  binding: certificate numbers `L_before`/`L_after` carry PROOFS
  `hbefore : L_before = evalFn θ_t A_t B`,
  `hafter : L_after = evalFn θ_{t+1} A_{t+1} B`.  This closes the
  "detached counters" defect (GrowthState/TrainState): the numbers a
  certificate reports are forced to be the evaluation of the recorded
  parameters/architecture/batch, not free-floating counters.
* The machine-vs-abstract gap is HONEST: a `MachineEvalBridge` is a
  premise `|machineEval − evalFn| ≤ ε_eval`, instantiated by consumers
  from the Runtime rounding lemmas (TernaryExact / BF16Delta) —
  Runtime is not imported here (layering; the C375 `coord_err_bound`
  premise pattern).

Honest pins (A16): `evalFn (θ, A, B) → ℝ` stays an abstract PARAMETER —
real network evaluation is out of Lean scope.  What the binding
guarantees is CONSISTENCY of the numbers used across certificates.
The demo theorem living on the canonical carrier is in
`Hagi/State/EvalBindingCert.lean` (State layer; Cert may not import
State).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Cert

/-! ## Словарь перегрузок: `EvalBinding`
Канон-носитель связывания сертификата с реальной оценкой — этот
файл. Одноимённые записи в нём отличаются ролей (binding/unwrap);
определения `CertStepGen` искать в `Hagi.Cert.StepGen`.
Полное переименование — вне v5.
-/

/-! ## Three type-distinct risk concepts (A16: not one `risk`) -/

/-- Risk EXPOSED at a state: the pre-step risk level, as a typed
value pinned to the state readout. -/
structure RiskExposure (S : Type*) (risk : S → ℝ) (s : S) where
  /-- The exposure value. -/
  val : ℝ
  /-- It is exactly the state's risk level. -/
  hval : val = risk s

/-- Risk REMAINING at a state: the post-step risk readout, a type
DISTINCT from `RiskExposure` so the two cannot be silently mixed. -/
structure RiskRemaining (S : Type*) (risk : S → ℝ) (s : S) where
  /-- The remaining-risk value. -/
  val : ℝ
  /-- It is exactly the state's risk level. -/
  hval : val = risk s

/-- Confidence radius: a NONNEGATIVE statistical uncertainty of an
estimate (e.g. an LCB slack).  Distinct type: a radius is not a risk
level and must never be stored in one. -/
structure ConfidenceRadius where
  /-- The radius value. -/
  val : ℝ
  /-- Radii are nonnegative. -/
  nonneg : 0 ≤ val

/-- Exposure readout at a state (typed constructor from the level
function). -/
def riskExposure (S : Type*) (risk : S → ℝ) (s : S) : RiskExposure S risk s where
  val := risk s
  hval := rfl

/-- Remaining readout at a state (typed constructor). -/
def riskRemaining (S : Type*) (risk : S → ℝ) (s : S) : RiskRemaining S risk s where
  val := risk s
  hval := rfl

/-- ADAPTER (C378): the frozen kernel's ℝ field `CertStepGen.riskRem`
maps explicitly into the typed `RiskRemaining` of the post-state —
no frozen statement changes, and new consumers get the type
protection. -/
def CertStepGen.toRiskRemaining {S TaskId : Type*}
    {M : SystemMetrics S TaskId} {obl : StepObligations TaskId}
    {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepGen M obl deltaLevel s s') :
    RiskRemaining S M.risk s' where
  val := h.riskRem
  hval := h.risk_next.symm

/-- The kernel's spend, wrapped as the pre-state EXPOSURE minus the
typed remainder (consistency of the typed readouts with the kernel's
split law). -/
theorem CertStepGen.riskExposure_split {S TaskId : Type*}
    {M : SystemMetrics S TaskId} {obl : StepObligations TaskId}
    {deltaLevel : S → ℝ} {s s' : S}
    (h : CertStepGen M obl deltaLevel s s')
    (e : RiskExposure S M.risk s) :
    e.val = h.riskSpend + (h.toRiskRemaining).val := by
  change e.val = h.riskSpend + h.riskRem
  rw [← h.risk_split, ← e.hval]

/-! ## Evaluation binding (A16 "самое важное") -/

variable {Θ A B : Type*}

/-- Abstract evaluation function `Eval(θ, A, B)` — parameters,
architecture, batch → loss.  Honest pin: a PARAMETER; real network
evaluation is out of Lean scope. -/
abbrev EvalFn (Θ A B : Type*) : Type _ := Θ → A → B → ℝ

/-- Machine-vs-abstract rounding bridge (C375 premise pattern): the
machine evaluation is within `eps` of the abstract evaluation
everywhere.  Consumers instantiate `bound` from Runtime rounding
lemmas (TernaryExact / BF16Delta); no `machine = real` pretense. -/
structure MachineEvalBridge (Θ A B : Type*) (evalFn : EvalFn Θ A B) where
  /-- The machine (rounded-backend) evaluation. -/
  machineEval : Θ → A → B → ℝ
  /-- The rounding-error bound. -/
  eps : ℝ
  /-- The bound is nonnegative. -/
  eps_nonneg : 0 ≤ eps
  /-- Proven rounding-error bound, uniform over θ, A, B. -/
  bound : ∀ θ : Θ, ∀ a : A, ∀ b : B, |machineEval θ a b - evalFn θ a b| ≤ eps

/-- The evaluation binding: certificate loss numbers bound to REAL
evaluation of the recorded parameters, architecture and batch.
`hbefore`/`hafter` are the detachment fix — the certificate's
`L_before`/`L_after` are PROVEN equal to the evaluation of `θ_t`/`θ_{t+1}`
on the SAME batch `B`, so they cannot be detached counters. -/
structure EvalBinding (Θ A B : Type*) (evalFn : EvalFn Θ A B) where
  /-- Parameters before the step. -/
  thetaBefore : Θ
  /-- Parameters after the step. -/
  thetaAfter : Θ
  /-- Architecture before the step. -/
  archBefore : A
  /-- Architecture after the step. -/
  archAfter : A
  /-- The evaluation batch (shared by before/after). -/
  batch : B
  /-- Reported loss before the step. -/
  Lbefore : ℝ
  /-- Reported loss after the step. -/
  Lafter : ℝ
  /-- PROOF: the reported before-loss IS the evaluation of the
  recorded before-parameters/architecture on the batch. -/
  hbefore : Lbefore = evalFn thetaBefore archBefore batch
  /-- PROOF: the reported after-loss IS the evaluation of the
  recorded after-parameters/architecture on the same batch. -/
  hafter : Lafter = evalFn thetaAfter archAfter batch

/-- The certified drop of the binding: `L_before − L_after` is
exactly the evaluation gap of the recorded transition. -/
theorem EvalBinding.drop_eq {evalFn : EvalFn Θ A B}
    (evb : EvalBinding Θ A B evalFn) :
    evb.Lbefore - evb.Lafter
      = evalFn evb.thetaBefore evb.archBefore evb.batch
        - evalFn evb.thetaAfter evb.archAfter evb.batch := by
  rw [evb.hbefore, evb.hafter]

/-- Machine readout of the before-loss sits within the PROVEN
rounding bound `eps` of the certificate's `L_before` (numeric bridge:
certificate numbers ↔ machine numbers). -/
theorem EvalBinding.machine_before {evalFn : EvalFn Θ A B}
    (br : MachineEvalBridge Θ A B evalFn)
    (evb : EvalBinding Θ A B evalFn) :
    |br.machineEval evb.thetaBefore evb.archBefore evb.batch - evb.Lbefore|
      ≤ br.eps := by
  rw [evb.hbefore]
  exact br.bound _ _ _

/-- Machine readout of the after-loss sits within `eps` of the
certificate's `L_after`. -/
theorem EvalBinding.machine_after {evalFn : EvalFn Θ A B}
    (br : MachineEvalBridge Θ A B evalFn)
    (evb : EvalBinding Θ A B evalFn) :
    |br.machineEval evb.thetaAfter evb.archAfter evb.batch - evb.Lafter|
      ≤ br.eps := by
  rw [evb.hafter]
  exact br.bound _ _ _

/-- The machine-side certified drop differs from the abstract one by
at most `2·eps` (both readouts carry the rounding bound) — honest
accumulation form for consumers. -/
theorem EvalBinding.machine_drop_gap {evalFn : EvalFn Θ A B}
    (br : MachineEvalBridge Θ A B evalFn)
    (evb : EvalBinding Θ A B evalFn) :
    |(br.machineEval evb.thetaBefore evb.archBefore evb.batch
        - br.machineEval evb.thetaAfter evb.archAfter evb.batch)
      - (evb.Lbefore - evb.Lafter)| ≤ 2 * br.eps := by
  have h1 := evb.machine_before br
  have h2 := evb.machine_after br
  have b1 := abs_le.mp h1
  have b2 := abs_le.mp h2
  apply abs_le.mpr
  constructor <;> linarith

end Hagi.Cert
