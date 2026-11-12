/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Cert.Core

/-!
# Generic certification-kernel adapters

Layer-legal adapters between concrete descent certificates and the
canonical `Hagi.Cert` kernel.  This file deliberately imports ONLY
`Hagi.Cert.Core`: it is generic over any `SystemMetrics` carrier.
Concrete instantiations (e.g. the batch cross-entropy setting) live at
the Contracts layer, which may import the model layer.

`zeroFloorObligations` is the trivial obligation family, kept by any
state with nonnegative objective.  `descentCertStep` assembles a
positive certified drop, a real descent inequality and preserved
budget/risk levels into a canonical `CertStep` with zero budget/risk
spend.  `holdTransition` is the identity `TransitionStep` at a
floor-keeping state.  `protectedRisk_le_of_riskRem` is the R1
risk-polarity slice: when the kernel risk level is the remaining-risk
`riskTotalLimit - protectedRisk`, the kernel's nonnegative risk
remainder converts into the protected-risk-under-limit bound.  The
GrowthState carrier for `protectedRisk` lives in quarantined
`Hagi/Legacy`, so the polarity adapter is stated against the canonical
kernel with explicit premises only.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Cert.Adapters

/-- Zero floor obligations: every task tag carries the trivial floor 0. -/
def zeroFloorObligations (T : Type*) : StepObligations T where
  floor := fun _ => 0

/-- The zero-floor contract holds exactly where the objective is
nonnegative. -/
theorem floorsKept_zeroFloor {S : Type*} {TaskId : Type*}
    {M : SystemMetrics S TaskId} {s : S} (h : 0 ≤ M.objective s) :
    FloorsKept M (zeroFloorObligations TaskId) s := fun _ => h

/-- Generic progress adapter: a positive certified drop, a real
descent inequality from execution, preserved budget/risk levels (zero
spend) with nonnegative remainders, and kept floors assemble into a
canonical `CertStep`. -/
def descentCertStep {S : Type*} {TaskId : Type*} {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId} {s s' : S} (drop : ℝ) (hdrop : 0 < drop)
    (hdescent : M.objective s' ≤ M.objective s - drop)
    (hbudget : M.budget s' = M.budget s) (hbudgetnn : 0 ≤ M.budget s')
    (hrisk : M.risk s' = M.risk s) (hrisknn : 0 ≤ M.risk s')
    (hfloors : FloorsKept M obl s') : CertStep M obl s s' where
  drop := drop
  drop_pos := hdrop
  descent := hdescent
  budgetSpend := 0
  budget_next := by rw [hbudget]; ring
  budget_nonneg := hbudgetnn
  riskSpend := 0
  risk_next := by rw [hrisk]; ring
  risk_nonneg := hrisknn
  floorsKept := hfloors

/-- Hold adapter: a floor-keeping state always admits the identity
`TransitionStep` via `HoldStep.id`, with no progress claim. -/
def holdTransition {S : Type*} {TaskId : Type*} {M : SystemMetrics S TaskId}
    {obl : StepObligations TaskId} {s : S}
    (hfloors : FloorsKept M obl s) : TransitionStep M obl s s :=
  TransitionStep.hold (HoldStep.id M obl s hfloors)

/-- R1 risk-polarity slice: if the canonical risk level at the
pre-state is the remaining risk `riskTotalLimit - protectedRisk`, then
a certified step's nonnegative risk remainder converts into the
protected-risk-under-limit bound after spending. -/
theorem protectedRisk_le_of_riskRem {S : Type*} {TaskId : Type*}
    {M : SystemMetrics S TaskId} {obl : StepObligations TaskId} {s s' : S}
    {c : CertStep M obl s s'} {riskTotalLimit protectedRisk : ℝ}
    (hpolarity : M.risk s = riskTotalLimit - protectedRisk) :
    protectedRisk + c.riskSpend ≤ riskTotalLimit := by
  have h1 := c.risk_nonneg
  rw [c.risk_next, hpolarity] at h1
  linarith

end Hagi.Cert.Adapters
