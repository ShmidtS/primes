import Mathlib.Tactic
import Hagi.Contracts.VilleMonitor
import Hagi.Cert.EvalBinding
import Hagi.State.CanonicalTrainState
import Hagi.Training.MacroStatCert
import Hagi.Training.TransitionCert

/-!
# Admission — confidence-gated admission of memory blocks and experts (A17 §5.4)

The A17 §5.4 admission rule: a new block of memory (or a new expert)
is added ONLY when

  `estimatedGain − r_conf − λ_M · memoryCost − λ_R · risk > 0`,

i.e. a new block is NOT added just because a heuristic predicted
benefit — the confidence-penalized, cost- and risk-weighted margin
must be strictly positive. `admitRule` is THE gate: the admission
certificate pins its recorded decision to the exact output of the
rule (no free-floating decision), and `noAdmitWithoutPositiveMargin`
proves the gate refuses every non-positive margin.

Composition, no new probability (C341/C380 thin-adapter convention):

* the anytime-validity premise is carried by `Hagi.Contracts.VilleMonitor.EProcMonitor`
  (C341) — `admit_sound` consumes the monitor's α and firing
  predicate;
* `admit_sound` is a direct descent from
  `Hagi.Contracts.VilleMonitor.monitor_ville_valid` with the C380
  `commit_sound` premise shape (the C264 `gate_anytime_valid`
  embedding): the false-admission event embeds in the e-process
  crossing, so `P[admitted ∧ ¬goodGain] ≤ α` — real Ville-engine
  statistics, not a vacuous bound;
* `refuse_safe` runs on the C363 `applyStep` / `hold_rollback_total`
  total-state machinery: a refused block changes NOTHING;
* the tie to the four-cert composition (C383):
  `growthCert_of_admission` shows an ADMITTED transition makes the
  `GrowthCert` (hence `fourCert_of_parts`) constructible — admission
  pins the DECISION, the growth book pins the CHANNELS.

Honest pins (A17 §5.4 acceptance bar):

1. **estimatedGain is a MEASURED quantity (premise), never a proven
   lower bound**: the estimate is produced through the C386
   `measuredQuality` semantic chain (the same measurement route as
   the C380 macro `ΔQ̂_K`). Only the radius-penalized LCB enters the
   rule; `admitRule_lcb_meaning` pins that `r_conf` is subtracted
   in full.
2. **E-process validity binder (premise-form)**: the
   supermartingale premises of `admit_sound` are the consumer's to
   discharge, exactly as C380 (C232/C341). NO bound is claimed on
   adaptively reused data — the honest instantiation is the
   pre-split fresh-sample route (`freshBatchMonitor`, C380).
3. **λ_M, λ_R are explicit parameters**, not hidden constants: the
   memory/risk exchange rates are recorded in the proposal,
   nonnegative-pinned.
4. **memoryCost** is the memory-side cost of the C330/C334
   `data_compute_budget` account (ledgered by the resource book,
   C383 `ResourceCert`); **risk** is a proposal-level estimate to be
   C378 `RiskExposure`-typed at state instantiation (a proposal is
   abstract over the live state; a radius is never a risk level).
-/

set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open Hagi.Contracts.VilleMonitor Hagi.Cert Hagi.State

namespace Hagi.Training

/-! ## The proposal and the rule -/

/-- The admission proposal of a candidate block/expert (A17 §5.4):
the MEASURED quality estimate `estimatedGain` (ΔQ̂ — premise, through
the C386 `measuredQuality` semantic chain; never a proven lower
bound), the typed confidence radius `r_conf` (C378), the memory cost
`memoryCost` with its nonnegativity (the memory side of the
C330/C334 `data_compute_budget` account), the risk estimate `risk`
with its nonnegativity (C378 `RiskExposure`-typed at state
instantiation), and the explicit exchange weights `lamM`, `lamR`. -/
structure AdmissionProposal where
  /-- Measured quality estimate ΔQ̂ (premise, C386 chain). -/
  estimatedGain : ℝ
  /-- Typed confidence radius of the estimate (C378). -/
  r_conf : ConfidenceRadius
  /-- Memory cost of the candidate block (C330/C334 account side). -/
  memoryCost : ℝ
  /-- Memory costs are nonnegative. -/
  memoryCost_nonneg : 0 ≤ memoryCost
  /-- Risk estimate of the candidate (C378 RiskExposure at
  instantiation). -/
  risk : ℝ
  /-- Risk estimates are nonnegative. -/
  risk_nonneg : 0 ≤ risk
  /-- Memory exchange weight λ_M (explicit parameter). -/
  lamM : ℝ
  /-- λ_M is nonnegative. -/
  lamM_nonneg : 0 ≤ lamM
  /-- Risk exchange weight λ_R (explicit parameter). -/
  lamR : ℝ
  /-- λ_R is nonnegative. -/
  lamR_nonneg : 0 ≤ lamR

/-- The confidence-penalized, cost- and risk-weighted admission
margin: `estimatedGain − r_conf − λ_M·memoryCost − λ_R·risk`. The
admission decision is exactly strict positivity of this margin. -/
noncomputable def admissionMargin (p : AdmissionProposal) : ℝ :=
  p.estimatedGain - p.r_conf.val - p.lamM * p.memoryCost
    - p.lamR * p.risk

/-- **THE admission rule (A17 §5.4)**: admit a candidate block/expert
iff the margin `estimatedGain − r_conf − λ_M·memoryCost − λ_R·risk`
is strictly positive. A new block is NOT added just because a
heuristic predicted benefit — this predicate is the only gate.
Decidability is `Real.decidableGT` (a specification, not a
computable runtime — hence `noncomputable`). -/
noncomputable def admitRule (p : AdmissionProposal) : Bool :=
  0 < admissionMargin p

/-- The decision is admission EXACTLY when the margin is strictly
positive — no drift between the rule and its unfolding. -/
@[simp] theorem admitRule_iff (p : AdmissionProposal) :
    admitRule p = true ↔ 0 < admissionMargin p := by
  simp only [admitRule, decide_eq_true_iff]

/-- **LCB meaning**: an admitted proposal has a strictly positive
confidence-penalized margin — the radius `r_conf` is subtracted in
full (the estimated gain is never consumed raw). -/
theorem admitRule_lcb_meaning (p : AdmissionProposal)
    (h : admitRule p = true) :
    0 < p.estimatedGain - p.r_conf.val - p.lamM * p.memoryCost
      - p.lamR * p.risk := by
  rw [admitRule, decide_eq_true_iff] at h
  simpa only [admissionMargin] using h

/-- **No heuristic bypass (gate closure)**: a non-positive margin
forces REFUSAL — whatever heuristic produced `estimatedGain`, the
rule admits nothing on a non-positive confidence-penalized margin. -/
theorem noAdmitWithoutPositiveMargin (p : AdmissionProposal)
    (h : admissionMargin p ≤ 0) : admitRule p = false := by
  unfold admitRule admissionMargin at *
  refine decide_eq_false ?_
  by_cases hn : 0 < p.estimatedGain - p.r_conf.val
    - p.lamM * p.memoryCost - p.lamR * p.risk
  · exact absurd hn (by linarith)
  · exact hn

/-! ## The admission certificate -/

/-- The admission certificate: a proposal `p`, the base state
`sBase` the candidate would be installed into, the candidate state
`sCand`, the anytime-validity premise carrier `mon` (`EProcMonitor`,
C341), and the `decision` — pinned by `admit_ok` to be exactly the
output of `admitRule p` (no free-floating decision). -/
structure AdmissionCert (S : Type*) (objective : S → ℝ) where
  /-- The candidate proposal. -/
  proposal : AdmissionProposal
  /-- The base state. -/
  sBase : S
  /-- The candidate state (block/expert installed). -/
  sCand : S
  /-- The anytime-validity premise carrier (C341 monitor). -/
  mon : EProcMonitor
  /-- The decision actually taken. -/
  decision : Bool
  /-- The decision is exactly `admitRule`'s output — no drift. -/
  admit_ok : decision = admitRule proposal

/-- Execute the certificate's decision on the base state, through
the C363 total-state step semantics: admission installs `sCand`,
refusal HOLDS (no state change at all). -/
def applyAdmission {S : Type*} {objective : S → ℝ}
    (cert : AdmissionCert S objective) : S :=
  match cert.decision with
  | true => applyStep cert.sBase (Outcome.progress cert.sCand)
  | false => applyStep cert.sBase Outcome.hold

/-! ## Soundness -/

/-- **refuse_safe**: a REFUSED block changes NOTHING —
`applyAdmission` returns the base state exactly, by the C363
total-rollback invariant `hold_rollback_total` (partial state change
not expressible; no block, no budget, no risk is spent). -/
theorem refuse_safe {S : Type*} {objective : S → ℝ}
    (cert : AdmissionCert S objective)
    (h : cert.decision = false) :
    applyAdmission cert = cert.sBase := by
  simp only [applyAdmission, h]
  exact hold_rollback_total cert.sBase

/-- **admit_sound (anytime-valid, C380 commit_sound shape)**: under
the e-process premises — the trajectory `L` fed to the monitor is a
nonnegative supermartingale with `μ[L 0] ≤ 1` (premise-form e-process
validity; on ADAPTIVELY reused data this premise is NOT derivable —
see the module pins) — and the two policy premises:
`hembed` (the C264 `gate_anytime_valid` embedding shape): if the
admitted gain is FALSE (`¬goodGain`), the e-process has crossed the
threshold `mon.α⁻¹` by horizon `n` — the e-process DETECTS the false
admission;
`hguard`: a monitor that has fired by horizon `n` never issued an
admission —
then the probability of a FALSE ADMISSION is at most `α`, i.e.
`μ.real {ω | admitted ∧ ¬goodGain ω} ≤ mon.α`. Proof: direct descent
from `Hagi.Contracts.VilleMonitor.monitor_ville_valid` (the C232/C295
Ville engine) by measure monotonicity — the C380 `commit_sound` proof
shape; no new concentration. -/
theorem admit_sound {S : Type*} {objective : S → ℝ}
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ m0}
    (cert : AdmissionCert S objective)
    {L : ℕ → Ω → ℝ} (hL : Supermartingale L 𝒢 μ) (hLnn : 0 ≤ L)
    (hL0 : μ[L 0] ≤ 1) (n : ℕ) {goodGain : Ω → Prop}
    (hembed : ∀ ω, ¬ goodGain ω →
      ∃ t ∈ Finset.range (n + 1), cert.mon.α⁻¹ ≤ L t ω)
    (hguard : ∀ ω, cert.decision = true →
      ¬ ∃ t ∈ Finset.range (n + 1), cert.mon.α⁻¹ ≤ L t ω) :
    μ.real {ω | cert.decision = true ∧ ¬ goodGain ω}
      ≤ cert.mon.α := by
  have hmain := monitor_ville_valid cert.mon hL hLnn hL0 n
  refine le_trans ?_ hmain
  refine measureReal_mono ?_ (by finiteness)
  rintro ω ⟨hcom, hbad⟩
  exact absurd (hembed ω hbad) (hguard ω hcom)

/-! ## Tie to the four-cert composition (C383) -/

variable {n a e q r c k : ℕ}

/-- **GrowthCert tie**: an ADMITTED proposal whose executed decision
installs the candidate state `s'` (through `applyAdmission` and the
C363 step semantics) together with the growth telemetry premises of
C383 (the `qual_tie` channel deltas and the `protected_ok`
interlock — premise-form, as in C383 itself) yields the
`GrowthCert s s'` of the transition — so the four-cert composition
`fourCert_of_parts` (given the micro certificate and the C380 macro
certificate on the same pair) is completable. Division of labor:
ADMISSION pins the DECISION, the growth book pins the CHANNELS. -/
def growthCert_of_admission (s s' : CanonicalTrainState n a e q r c k)
    (cert : AdmissionCert (CanonicalTrainState n a e q r c k) fullObjective)
    (_h : cert.decision = true) (_hexec : applyAdmission cert = s')
    (_hs : cert.sBase = s) (g : Fin 5 → ℝ)
    (ht : ∀ i, s'.core.qual i = s.core.qual i + g i)
    (hp : ∀ i ∈ s.core.saf.protectedChannels, 0 ≤ g i) :
    GrowthCert s s' where
  growth := g
  qual_tie := ht
  protected_ok := hp

/-- Refused admissions produce NO growth book: the executed state IS
the base state (by `refuse_safe`), so no transition — and hence no
growth certificate — exists for a refused candidate. -/
theorem refused_no_transition (s s' : CanonicalTrainState n a e q r c k)
    (cert : AdmissionCert (CanonicalTrainState n a e q r c k) fullObjective)
    (h : cert.decision = false) (hexec : applyAdmission cert = s')
    (hs : cert.sBase = s) (hne : s ≠ s') : False := by
  rw [refuse_safe cert h, hs] at hexec
  exact hne (hexec.symm ▸ rfl)

/-! ## Anchor demos -/

/-- The anchor ADMIT certificate: measured gain `1`, radius `1/4`,
zero costs and risks — margin `3/4 > 0`: the rule admits. -/
theorem admitRule_anchor_admit :
    admitRule ⟨1, ⟨1 / 4, by norm_num⟩, 0, by norm_num, 0, by norm_num,
      0, by norm_num, 0, by norm_num⟩ = true := by
  simp only [admitRule, admissionMargin]
  norm_num

/-- The anchor REFUSE-by-costs: measured gain `1`, radius `1/4`, but
memory cost `1` at `λ_M = 1` — margin `−1/4 ≤ 0`: COSTS CAN VETO a
heuristically promising block. -/
theorem admitRule_anchor_refuse_costs :
    admitRule ⟨1, ⟨1 / 4, by norm_num⟩, 1, by norm_num, 0, by norm_num,
      1, by norm_num, 0, by norm_num⟩ = false := by
  simp only [admitRule, admissionMargin]
  norm_num

/-- The anchor REFUSE-by-uncertainty: measured gain `1` but radius
`2` — LCB `−1 ≤ 0`: UNCERTAINTY CAN VETO a heuristically promising
block (the estimate is never consumed raw). -/
theorem admitRule_anchor_refuse_uncertainty :
    admitRule ⟨1, ⟨2, by norm_num⟩, 0, by norm_num, 0, by norm_num,
      0, by norm_num, 0, by norm_num⟩ = false := by
  simp only [admitRule, admissionMargin]
  norm_num

end Hagi.Training
