import Mathlib.Tactic
import Hagi.Contracts.VilleMonitor
import Hagi.State.CanonicalTrainState
import Hagi.Cert.EvalBinding
import Hagi.Probability.Concentration

/-!
# MacroStatCert — statistically valid macro-cycle certificate (A16 TT-CAT)

The macro-loop certificate of the A16 TT-CAT two-level training design:
every `K` micro-steps the controller forms a quality estimate `ΔQ̂_K`
with a typed confidence radius, and takes ONE of three decisions —
`commit` (LCB `ΔQ̂_K − r_conf` above threshold), `hold` (statistical
uncertainty zone — no state change), `rollback` (UCB confirms
degradation OR a hard limit is breached — restore the last committed
checkpoint).

Composition, no new probability (thin-adapter convention):

* the anytime-validity premise is carried by `Hagi.Contracts.VilleMonitor.EProcMonitor`
 — the decision consumes the monitor's α and firing predicate;
* `commit_sound` is a direct descent from
  `Hagi.Contracts.VilleMonitor.monitor_ville_valid` (
  Ville engine) `gate_anytime_valid` embedding premise
  shape: the false-commit event embeds in the e-process crossing;
* `rollback_sound` / `hold_safe` run on
  `Hagi.State.applyStep` / `hold_rollback_total` machinery (total-state
  rollback, partial rollback not expressible);
* `r_conf` is `Hagi.Cert.ConfidenceRadius` type — a radius is
  never silently mixed with a risk level.

Honest pins (A16 acceptance bar — "plain Freedman on reused data is
insufficient"):

1. **Data freshness / independence binder (premise-form)**: the
   e-process factors must have conditional mean ≤ 1 on data the macro
   loop did NOT adaptively choose (pre-split fresh samples). The
   demo below instantiates exactly this pre-split route. NO bound is
   claimed on adaptively reused data.
2. **E-process validity binder (premise-form)**: the supermartingale
   premises `hL`/`hLnn`/`hL0` of `commit_sound` — the consumer's to
   discharge .
3. **Adaptive-data route**: pointer only — future instantiation via
   the `EProcMonitor` stitched masters (
   `stitching_eprocess_anytime` `stitching_countable_ville`).
-/

set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open Hagi.Contracts.VilleMonitor Hagi.Cert Hagi.State

namespace Hagi.Training

/-! ## The three-way decision -/

/-- The macro-cycle decision (A16 TT-CAT): commit the new state, hold
(no state change), or roll back to the last committed checkpoint. -/
inductive MacroDecision where
  /-- LCB above threshold — commit the new state. -/
  | commit : MacroDecision
  /-- Statistically uncertain — hold the current state. -/
  | hold : MacroDecision
  /-- Degradation confirmed (UCB) or hard limit breached — roll back. -/
  | rollback : MacroDecision

/-- The pure three-way decision function: from the quality estimate
`dQ` (= `ΔQ̂_K`), the confidence radius `r`, the commit `threshold`,
and the hard-limit breach flag `breach`:
`breach` dominates (rollback); then `commit` iff the LCB
`dQ − r.val` is strictly above `threshold`; then `rollback` iff the
UCB `dQ + r.val` is strictly below `-threshold` (degradation
confirmed); otherwise `hold` (uncertainty zone).

Decidability is `Real.decidableLT` (the decision is a specification,
not a computable runtime — hence `noncomputable`). -/
noncomputable def macroDecide (dQ : ℝ) (r : ConfidenceRadius) (threshold : ℝ)
    (breach : Bool) : MacroDecision :=
  if breach then MacroDecision.rollback
  else if threshold < dQ - r.val then MacroDecision.commit
  else if dQ + r.val < -threshold then MacroDecision.rollback
  else MacroDecision.hold

/-- Exhaustive match, commit case: without a hard-limit breach the
decision is `commit` EXACTLY when the LCB `dQ − r` is above the
threshold. -/
@[simp] theorem macroDecide_eq_commit_iff (dQ : ℝ) (r : ConfidenceRadius)
    (threshold : ℝ) (breach : Bool) :
    macroDecide dQ r threshold breach = MacroDecision.commit ↔
      ¬breach ∧ threshold < dQ - r.val := by
  cases breach with
  | false =>
      unfold macroDecide
      rw [if_neg (by simp)]
      split
      · next h1 => simp [h1]
      · next h1 =>
        split
        · next h2 => simp [h1, h2]
        · next h2 => simp [h1, h2]
  | true => simp [macroDecide]

/-- Exhaustive match, hold case: the decision is `hold` EXACTLY in
the statistical uncertainty zone — no breach, LCB not above
threshold, UCB not below `-threshold`. -/
@[simp] theorem macroDecide_eq_hold_iff (dQ : ℝ) (r : ConfidenceRadius)
    (threshold : ℝ) (breach : Bool) :
    macroDecide dQ r threshold breach = MacroDecision.hold ↔
      ¬breach ∧ ¬(threshold < dQ - r.val) ∧ ¬(dQ + r.val < -threshold) := by
  cases breach with
  | false =>
      unfold macroDecide
      rw [if_neg (by simp)]
      split
      · next h1 => simp [h1]
      · next h1 =>
        split
        · next h2 => simp [h1, h2]
        · next h2 => simp [h1, h2]
  | true => simp [macroDecide]

/-- Exhaustive match, rollback case: the decision is `rollback`
EXACTLY when the hard limit is breached OR the UCB confirms
degradation. -/
@[simp] theorem macroDecide_eq_rollback_iff (dQ : ℝ) (r : ConfidenceRadius)
    (threshold : ℝ) (breach : Bool) :
    macroDecide dQ r threshold breach = MacroDecision.rollback ↔
      breach ∨ (¬breach ∧ ¬(threshold < dQ - r.val)
        ∧ dQ + r.val < -threshold) := by
  cases breach with
  | false =>
      unfold macroDecide
      rw [if_neg (by simp)]
      split
      · next h1 => simp [h1]
      · next h1 =>
        split
        · next h2 => simp [h1, h2]
        · next h2 => simp [h1, h2]
  | true => simp [macroDecide]

/-! ## The macro-cycle certificate -/

/-- The macro statistical certificate (A16 four-certificate rule):
the versioned state transition `sBefore → sAfter` (the `S_t → S_{t+1}`
binding shared by all four certificates), the last committed
checkpoint `sCheckpoint` (the rollback target), the quality estimate
`deltaQ` (`ΔQ̂_K`), the TYPED confidence radius `r_conf` (— a
radius is not a risk level), the commit `threshold`, the hard-limit
`breach` flag, the anytime-validity premise carrier `mon`
(`EProcMonitor`), and the `decision` — pinned by `decide_ok` to
be exactly the output of `macroDecide` (no free-floating decision). -/
structure MacroStatCert (S : Type*) (objective : S → ℝ) where
  /-- State BEFORE this macro-cycle (S_t). -/
  sBefore : S
  /-- State AFTER this macro-cycle (S_{t+1}). -/
  sAfter : S
  /-- Last committed checkpoint — the rollback target. -/
  sCheckpoint : S
  /-- The quality estimate ΔQ̂_K on the macro window. -/
  deltaQ : ℝ
  /-- The typed confidence radius r_conf. -/
  r_conf : ConfidenceRadius
  /-- The commit threshold. -/
  threshold : ℝ
  /-- Hard limit violated flag. -/
  breach : Bool
  /-- The anytime-validity premise carrier (monitor). -/
  mon : EProcMonitor
  /-- The decision actually taken. -/
  decision : MacroDecision
  /-- The decision is exactly `macroDecide`'s output — no drift. -/
  decide_ok :
    decision = macroDecide deltaQ r_conf threshold breach

/-- Execute the certificate's decision on the pre-state, through the
 total-state step semantics: `commit` installs `sAfter`,
`hold` keeps `sBefore` (total rollback), `rollback` restores
the last committed checkpoint `sCheckpoint`. -/
def applyDecision {S : Type*} {objective : S → ℝ}
    (cert : MacroStatCert S objective) : S :=
  match cert.decision with
  | MacroDecision.commit => applyStep cert.sBefore (Outcome.progress cert.sAfter)
  | MacroDecision.hold => applyStep cert.sBefore Outcome.hold
  | MacroDecision.rollback =>
      applyStep cert.sBefore (Outcome.progress cert.sCheckpoint)

/-! ## Decision soundness -/

/-- **hold_safe**: a Hold decision changes NOTHING — `applyDecision`
returns the pre-state exactly, by the total-rollback invariant
`Hagi.State.hold_rollback_total` (partial state change not
expressible). -/
theorem hold_safe {S : Type*} {objective : S → ℝ}
    (cert : MacroStatCert S objective)
    (h : cert.decision = MacroDecision.hold) :
    applyDecision cert = cert.sBefore := by
  simp only [applyDecision, h]
  exact hold_rollback_total cert.sBefore

/-- **rollback_sound**: a Rollback decision restores the LAST
COMMITTED CHECKPOINT — total-state restore through
`applyStep` semantics (the full carrier, weights and optimizer
buffers alike, is replaced by the checkpoint state; a partial
rollback is not expressible). -/
theorem rollback_sound {S : Type*} {objective : S → ℝ}
    (cert : MacroStatCert S objective)
    (h : cert.decision = MacroDecision.rollback) :
    applyDecision cert = cert.sCheckpoint := by
  simp only [applyDecision, h]
  rfl

/-- **commit_sound (anytime-valid, embedding shape)**: under the
e-process premises — the trajectory `L` fed to the monitor is a
nonnegative supermartingale with `μ[L 0] ≤ 1` (premise-form e-process
validity; on ADAPTIVELY reused data this premise is NOT derivable —
see the module pins) — and the two policy premises:
`hembed` (`gate_anytime_valid` embedding shape): if the
committed gain is FALSE (`¬goodGain`), the e-process has crossed the
threshold `mon.α⁻¹` by horizon `n` — the e-process DETECTS the false
commit;
`hguard`: a monitor that has fired by horizon `n` never issued a
`commit` decision —
then the probability of a FALSE COMMIT is at most `α`, i.e.
`μ.real {ω | committed ∧ ¬goodGain ω} ≤ mon.α`. Proof: direct descent
from `Hagi.Contracts.VilleMonitor.monitor_ville_valid` (
Ville engine) by measure monotonicity — exactly the
`audit_monitor_fires` proof shape; no new concentration. -/
theorem commit_sound {S : Type*} {objective : S → ℝ}
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}
    (cert : MacroStatCert S objective)
    {L : ℕ → Ω → ℝ} (hL : Supermartingale L 𝒢 μ) (hLnn : 0 ≤ L)
    (hL0 : μ[L 0] ≤ 1) (n : ℕ) {goodGain : Ω → Prop}
    (hembed : ∀ ω, ¬ goodGain ω →
      ∃ t ∈ Finset.range (n + 1), cert.mon.α⁻¹ ≤ L t ω)
    (hguard : ∀ ω, cert.decision = MacroDecision.commit →
      ¬ ∃ t ∈ Finset.range (n + 1), cert.mon.α⁻¹ ≤ L t ω) :
    μ.real {ω | cert.decision = MacroDecision.commit ∧ ¬ goodGain ω}
      ≤ cert.mon.α := by
  -- the radius now flows through the unified premise record
  -- (`ConcVilleChannel`) instead of the raw monitor form.
  have hmain := Hagi.Contracts.VilleMonitor.concVilleAnytime
    (C := ⟨cert.mon.α, cert.mon.α_pos, 𝒢, L, hL, hLnn, hL0⟩) n

  refine le_trans ?_ hmain
  refine measureReal_mono ?_ (by finiteness)
  rintro ω ⟨hcom, hbad⟩
  exact absurd (hembed ω hbad) (hguard ω hcom)

/-! ## Demo: the pre-split fresh-sample instantiation -/

/-- The monitor over a PRE-SPLIT fresh factor batch (the honest first
instantiation of the A16 acceptance bar): level `α`, e-value exactly
the product of the factor list. FACTOR VALIDITY (each factor has
conditional mean ≤ 1 on the pre-split data) is PREMISE-FORM — pin #1
of the module; nothing here claims a bound on adaptively reused data. -/
def freshBatchMonitor (α : ℝ) (hα : 0 < α) (facs : List ℝ) :
    EProcMonitor where
  α := α
  α_pos := hα
  M := facs.foldr (· * ·) 1
  updates := facs
  hM := rfl

/-- The anchor commit certificate (S := ℝ, objective := id): estimate
`ΔQ̂_K = 1`, radius `1/4`, threshold `1/2`, no breach — LCB
`1 − 1/4 = 3/4 > 1/2`: the pure decision function says COMMIT. -/
theorem macroDecide_anchor_commit :
    macroDecide 1 ⟨1 / 4, by norm_num⟩ (1 / 2) false
      = MacroDecision.commit := by
  simp only [macroDecide, Bool.false_eq_true, if_false]
  norm_num

/-- The anchor hold certificate: estimate `ΔQ̂_K = 0`, radius `1/2`,
threshold `1` — LCB `−1/2 ≤ 1` and UCB `1/2 > −1`: the statistical
uncertainty zone, the decision is HOLD. -/
theorem macroDecide_anchor_hold :
    macroDecide 0 ⟨1 / 2, by norm_num⟩ 1 false = MacroDecision.hold := by
  simp only [macroDecide, Bool.false_eq_true, if_false]
  norm_num

/-- The anchor rollback certificate: estimate `ΔQ̂_K = −2`, radius
`1/2`, threshold `1/2` — UCB `−3/2 < −1/2` confirms degradation (no
breach needed; the breach flag alone also forces rollback). -/
theorem macroDecide_anchor_rollback :
    macroDecide (-2) ⟨1 / 2, by norm_num⟩ (1 / 2) false
      = MacroDecision.rollback := by
  simp only [macroDecide, Bool.false_eq_true, if_false]
  norm_num

/-- The hard-limit anchor: a breached hard limit forces rollback
regardless of the estimate. -/
theorem macroDecide_anchor_breach :
    macroDecide 1 ⟨1 / 4, by norm_num⟩ (1 / 2) true
      = MacroDecision.rollback := by
  simp only [macroDecide]
  rfl

/-- The full anchor certificate (S := ℝ, objective := id) carrying a
COMMIT decision over the fresh-batch monitor at `α = 1/4` with
factors `[2, 2]` (the firing anchor batch). -/
noncomputable def macroCertAnchor : MacroStatCert ℝ id where
  sBefore := 0
  sAfter := 1
  sCheckpoint := 0
  deltaQ := 1
  r_conf := ⟨1 / 4, by norm_num⟩
  threshold := 1 / 2
  breach := false
  mon := freshBatchMonitor (1 / 4) (by norm_num) [2, 2]
  decision := MacroDecision.commit
  decide_ok := by
    simp only [macroDecide]
    norm_num

/-- The anchor certificate's executed decision installs the new state
(`sAfter = 1`). -/
theorem applyDecision_anchor_commit :
    applyDecision macroCertAnchor = 1 := rfl

/-- The anchor certificate's monitor is exactly the firing
anchor batch: factors `[2, 2]` at `α = 1/4` reach the e-value `4`
and the monitor FIRES (a false commit under this monitor is caught
by `commit_sound` at level `α = 1/4`). -/
theorem freshBatchMonitor_anchor_fires :
    monitorFires (freshBatchMonitor (1 / 4) (by norm_num) [2, 2]) := by
  simp only [monitorFires, freshBatchMonitor]
  norm_num

end Hagi.Training
