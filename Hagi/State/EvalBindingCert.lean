import Mathlib.Tactic
import Hagi.State.CanonicalTrainState
import Hagi.Cert.EvalBinding

/-!
# EvalBindingCert — demo theorem on the canonical carrier 

The demo: a full certificate on `CanonicalTrainState` carrying
`Hagi.Cert.EvalBinding`, where the certificate's `L_before`/`L_after`
are the SAME values the descent theorem talks about:

* `FullEvalCert` — a `FullStepCert` PLUS an `EvalBinding` at
  `evalFn := fun st _ _ => fullObjective st` on the recorded
  before/after states (θ carried BY the canonical state itself);
* `fullEvalCert_descent` — the descent restated on the BOUND
  numbers: `L_after ≤ L_before − drop`.  The descent theorem's
  objective values and the certificate's reported losses coincide BY
  PROOF (`hbefore`/`hafter` of the binding, definitionally equal to
  `fullObjective s`/`fullObjective s'`), not by convention;
* `fullEvalCert_machine_drop` — the machine-side drop differs from
  the bound `L_before − L_after` by at most `2·eps_eval` (the
  `MachineEvalBridge` rounding premise, instantiated by consumers
  from Runtime rounding lemmas).

Honest pin: `evalFn` abstracts the real evaluation; here it is
INSTANTIATED at `fullObjective` (weights + optimizer buffers), the
objective the canonical carrier's certificates already carry.
-/

set_option relaxedAutoImplicit false

namespace Hagi.State

variable {n a e q r c k : ℕ}
variable {Arch Batch : Type*}

/-- The evaluation function of the canonical carrier: parameters ARE
the canonical state, evaluated by the FULL objective (weights plus
optimizer buffers — buffer drift cannot hide behind weight descent,
).  Architecture and batch are abstract parameters. -/
noncomputable def canonicalEval (st : CanonicalTrainState n a e q r c k)
    (_a : Arch) (_b : Batch) : ℝ := fullObjective st

/-- Full certificate on the canonical carrier WITH the evaluation
binding: the step certificate plus the binding of the
reported numbers to the evaluation of the recorded states. -/
structure FullEvalCert (s s' : CanonicalTrainState n a e q r c k) where
  /-- The certified progress step (full objective, budget/risk
  ledger laws). -/
  cert : FullStepCert s s'
  /-- The evaluation binding on the same states. -/
  binding : Hagi.Cert.EvalBinding
    (CanonicalTrainState n a e q r c k) Arch Batch canonicalEval
  /-- The binding's before-parameters ARE the certificate's
  pre-state. -/
  thetaBefore_eq : binding.thetaBefore = s
  /-- The binding's after-parameters ARE the certificate's
  post-state. -/
  thetaAfter_eq : binding.thetaAfter = s'

/-- The reported after-loss IS the full objective of the post-state
(unfolds the binding through the state identification). -/
theorem FullEvalCert.lafter_eq
    (fc : FullEvalCert (Arch := Arch) (Batch := Batch) s s') :
    fc.binding.Lafter = fullObjective s' := by
  have h := fc.binding.hafter
  rw [fc.thetaAfter_eq] at h
  exact h

/-- The reported before-loss IS the full objective of the
pre-state. -/
theorem FullEvalCert.lbefore_eq
    (fc : FullEvalCert (Arch := Arch) (Batch := Batch) s s') :
    fc.binding.Lbefore = fullObjective s := by
  have h := fc.binding.hbefore
  rw [fc.thetaBefore_eq] at h
  exact h

/-- DEMO THEOREM (detachment closed): the descent law
certificate, stated ENTIRELY on the bound certificate numbers —
`L_after ≤ L_before − drop`.  The values the descent theorem talks
about and the numbers the certificate reports are the SAME values,
by the binding proofs above. -/
theorem fullEvalCert_descent (s s' : CanonicalTrainState n a e q r c k)
    (fc : FullEvalCert (Arch := Arch) (Batch := Batch) s s') :
    fc.binding.Lafter ≤ fc.binding.Lbefore - fc.cert.drop := by
  have hd := fc.cert.descent
  rw [← fc.lbefore_eq, ← fc.lafter_eq] at hd
  exact hd

/-- Machine-side drop honesty: with a rounding bridge over the
canonical evaluation, the machine-reported drop differs from the
certified bound `L_before − L_after` by at most `2·eps_eval` (no
`machine = real` pretense). -/
theorem fullEvalCert_machine_drop (s s' : CanonicalTrainState n a e q r c k)
    (fc : FullEvalCert (Arch := Arch) (Batch := Batch) s s')
    (br : Hagi.Cert.MachineEvalBridge
      (CanonicalTrainState n a e q r c k) Arch Batch canonicalEval) :
    |(br.machineEval fc.binding.thetaBefore fc.binding.archBefore
        fc.binding.batch
      - br.machineEval fc.binding.thetaAfter fc.binding.archAfter
        fc.binding.batch)
      - (fc.binding.Lbefore - fc.binding.Lafter)| ≤ 2 * br.eps :=
  fc.binding.machine_drop_gap br

end Hagi.State
