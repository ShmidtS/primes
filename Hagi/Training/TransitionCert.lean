import Mathlib.Tactic
import Hagi.State.EvalBindingCert
import Hagi.Training.MacroStatCert

/-!
# FourCertTransition — four-certificate composition on one versioned
transition (A16, C383)

The A16 composition record: FOUR certificates — micro-optimization
(C363 `FullStepCert`), resource ledger, quality growth, macro-statistics
(C380 `MacroStatCert`) — all referencing the SAME versioned state
transition `S_t → S_{t+1}` on the canonical carrier
`Hagi.State.CanonicalTrainState`. Version coherence is by construction:
the record carries `macro_before`/`macro_after` hversion proofs that the
macro certificate's states ARE the states the micro/resource/growth
certificates are indexed by — no cross-transition mixing.

* `ResourceCert` — the thin resource book: the exact budget/risk ledger
  laws of the transition (the per-step form of the C330/C334 budget
  account `data_compute_budget`; adapter `fullStepCert_resource`
  extracts it from any C363 certificate);
* `GrowthCert` — the missing fourth certificate (premise-form): the
  quality channels of the canonical state change EXACTLY by the recorded
  per-channel deltas `growth` (telemetry tie — TrainState §4.1: quality
  change is bound to a transition only by a Transition-level
  certificate), and no protected channel degrades;
* `FourCertTransition` — the versioned composition record;
* `fourCert_commit_descent` — composition soundness (positive
  consistency): a COMMIT decision executes the micro-certified post-state
  `s'` AND the full objective descends by the micro drop — the macro
  decision and the micro descent provably act on the SAME transition;
* `fourCert_hold_sound` — a HOLD decision keeps the pre-state exactly.

Honest exposure (rollback): a ROLLBACK decision restores
`macro.sCheckpoint`, which is OUTSIDE the certified pair `s, s'` by
construction — NO micro/growth coherence is claimed for the rollback
target (`rollback_sound` of C380 applies unchanged).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Training

open Hagi.State Hagi.Training

variable {n a e q r c k : ℕ}

/-! ## ResourceCert — the per-transition resource ledger -/

/-- The resource certificate of ONE transition: the exact budget and
risk ledger laws (C363 `FullStepCert` fields, in the per-step form of
the C330/C334 `data_compute_budget` account). -/
structure ResourceCert (s s' : CanonicalTrainState n a e q r c k) where
  /-- Budget spent by the transition (compute channel). -/
  budgetSpend : ℝ
  /-- Exact budget ledger law. -/
  budget_next : s'.core.res.budget = s.core.res.budget - budgetSpend
  /-- Residual budget is nonnegative. -/
  budget_nonneg : 0 ≤ s'.core.res.budget
  /-- Risk spent by the transition (independent channel). -/
  riskSpend : ℝ
  /-- Residual risk (free remainder, not 0-pinned). -/
  riskRem : ℝ
  /-- Risk ledger law of the next state. -/
  risk_next : s'.core.saf.risk = riskRem
  /-- Exact risk split in the ledger. -/
  risk_split : s.core.saf.risk = riskSpend + riskRem
  /-- Residual risk is nonnegative. -/
  risk_nonneg : 0 ≤ riskRem

/-- Adapter: every C363 `FullStepCert` already carries the resource
ledger laws — extract the resource book of the SAME transition. -/
def fullStepCert_resource (h : FullStepCert s s') : ResourceCert s s' where
  budgetSpend := h.budgetSpend
  budget_next := h.budget_next
  budget_nonneg := h.budget_nonneg
  riskSpend := h.riskSpend
  riskRem := h.riskRem
  risk_next := h.risk_next
  risk_split := h.risk_split
  risk_nonneg := h.risk_nonneg

/-! ## GrowthCert — the quality growth certificate (premise-form) -/

/-- The growth certificate of ONE transition (the fourth A16 book,
premise-form): the quality channels of the canonical state change
EXACTLY by the recorded per-channel deltas (`qual_tie` — the §4.1
telemetry tie: a transition cannot set quality arbitrarily), and no
protected channel degrades (`protected_ok` — the safety interlock on
`SafetyState.protectedChannels`). No claim is made that quality grows:
the deltas are recorded telemetry, their signs are the consumer's to
discharge outside protected channels. -/
structure GrowthCert (s s' : CanonicalTrainState n a e q r c k) where
  /-- Per-channel quality deltas (recorded telemetry). -/
  growth : Fin 5 → ℝ
  /-- Telemetry tie: quality changes exactly by the recorded deltas. -/
  qual_tie : ∀ i, s'.core.qual i = s.core.qual i + growth i
  /-- Safety interlock: no protected channel degrades. -/
  protected_ok : ∀ i ∈ s.core.saf.protectedChannels, 0 ≤ growth i

/-! ## The versioned composition record -/

/-- The four-certificate composition on ONE versioned transition
`S_t → S_{t+1}` (states `s`, `s'` of the canonical carrier): micro
(C363), resource, growth, macro (C380). Version coherence is by
construction: `macro_before`/`macro_after` are the hversion proofs that
the macro certificate's recorded states ARE `s` and `s'` — all four
certificates bind the identical pair, cross-transition mixing is not
expressible in this type. -/
structure FourCertTransition (s s' : CanonicalTrainState n a e q r c k) where
  /-- Micro-optimization certificate (C363 full step). -/
  micro : FullStepCert s s'
  /-- Resource ledger book of the same transition. -/
  resource : ResourceCert s s'
  /-- Quality growth book of the same transition. -/
  growth : GrowthCert s s'
  /-- Macro statistical certificate (C380), on the full objective. -/
  macroStat : MacroStatCert (CanonicalTrainState n a e q r c k) fullObjective
  /-- hversion: the macro pre-state IS the micro/resource/growth
  pre-state `s`. -/
  macro_before : macroStat.sBefore = s
  /-- hversion: the macro post-state IS the micro/resource/growth
  post-state `s'`. -/
  macro_after : macroStat.sAfter = s'

/-- Assembly lemma (the canonical-carrier demo): the existing pieces —
a C363 micro certificate, a growth book, and a C380 macro certificate
whose recorded states are `s`/`s'` — compose into the versioned
transition record, with the resource book extracted from the micro
certificate by `fullStepCert_resource`. -/
def fourCert_of_parts (micro : FullStepCert s s') (growth : GrowthCert s s')
    (mcert : MacroStatCert (CanonicalTrainState n a e q r c k) fullObjective)
    (hb : mcert.sBefore = s) (ha : mcert.sAfter = s') :
    FourCertTransition s s' where
  micro := micro
  resource := fullStepCert_resource micro
  growth := growth
  macroStat := mcert
  macro_before := hb
  macro_after := ha

/-! ## Composition soundness (no cross-transition mixing) -/

/-- COMPOSITION SOUNDNESS, commit case: if the macro decision is
`commit`, the executed state IS the micro-certified post-state `s'`
(through the hversion proof `FourCertTransition.macro_after`), and the
full objective descends by the micro drop — the macro-level decision
and the micro-level descent provably act on the SAME transition, not on
two separately-versioned copies of the states. -/
theorem fourCert_commit_descent (s s' : CanonicalTrainState n a e q r c k)
    (tc : FourCertTransition s s')
    (h : tc.macroStat.decision = MacroDecision.commit) :
    applyDecision tc.macroStat = s'
      ∧ fullObjective s' ≤ fullObjective s - tc.micro.drop := by
  have hexe : applyDecision tc.macroStat
      = applyStep tc.macroStat.sBefore (Outcome.progress tc.macroStat.sAfter) := by
    simp only [applyDecision, h]
  rw [tc.macro_before, tc.macro_after] at hexe
  simp only [applyStep] at hexe
  exact ⟨hexe, tc.micro.descent⟩

/-- COMPOSITION SOUNDNESS, hold case: if the macro decision is `hold`,
the executed state IS the pre-state `s` (through `macro_before` and the
C363 total-rollback invariant behind C380 `hold_safe`) — a hold executes
no transition at all, so no book of the record is bypassed. -/
theorem fourCert_hold_sound (s s' : CanonicalTrainState n a e q r c k)
    (tc : FourCertTransition s s')
    (h : tc.macroStat.decision = MacroDecision.hold) :
    applyDecision tc.macroStat = s := by
  rw [hold_safe tc.macroStat h, tc.macro_before]

end Hagi.Training
