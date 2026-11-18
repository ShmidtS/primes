/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Training.CRMSM
import Hagi.Theory.MasterTheorem
import Hagi.State.TrainTrajectory

/-!
# Alternating joint update — piecewise-certified trajectory with phase guards

C402, research beat of the C397 queue (ranked item 5, "joint
update — research goal"): LOOSEN the C396 `crmsm_joint_separation`
pin through an ALTERNATING schedule. The extractor updates RARELY
(at phase boundaries, every `K` steps, C380-style period) and is
admitted only through a re-certification gate; between boundaries
the extractor is FROZEN, so the head-descent theorems (C387 via
the C396 wiring, C392 master steps) apply VERBATIM — the
separation lemma's precondition holds by FREEZING, not by equality
of a joint update. Precedent: C293 R1 alternating rounds
(one-sided dependency z* → visible: each round's guarantee is
conditional on the frozen other side).

## What this module proves (the honest comparison vs the pin)

- WITHIN a phase (`HeadPhase`, `head_phase_certified`,
  `head_phase_bound`): at a frozen extractor every head step
  carries `HeadControl` (the C396 bridge applies unchanged) and
  the phase telescopes the C387 universal drops.
- AT a boundary (`ExtractorBoundary`, `extractor_phase_admitted`,
  `boundary_refusal_freezes`): the extractor may move ONLY through
  the C390 admission rule (no free-floating decision; non-positive
  margin ⇒ refuse), ONLY at multiples of the schedule period `K`,
  and the loss change across the boundary is bounded by an
  explicit premise `delta ≥ 0`. Refusal freezes the extractor —
  the next phase proceeds at the SAME extractor, so the head
  theorems apply again (safe degradation, NOT a deadlock).
- OVER the whole trajectory (`AlternatingTrajectory`,
  `alternating_trajectory_bound`): the full objective is bounded
  by start − Σ certified drops + Σ penalties + Σ boundary damages
  (telescope over the kind discipline).

## What this module does NOT prove (the pin stays)

`crmsm_joint_separation` (C396) is INTENTIONALLY untouched: a
SIMULTANEOUS single-step joint extractor+head update remains
uncovered. What alternating achieves is the PIECEWISE-CERTIFIED
trajectory above; it is a partial result next to the pin, not a
replacement of it.

## Honesty pins

- **Damage bound is a PREMISE (C402), with a DERIVED counterpart
  (C408).** `delta` is a per-boundary binder `fullObjective s' ≤
  fullObjective s + delta`, `delta ≥ 0`. C408 derives the
  CE-channel damage: the CE head is 2-Lipschitz in the logits
  (sup norm, `ce_head_lipschitz_in_logits`), the head logit map
  is `headLip`-Lipschitz in the FEATURES (premise), and the
  MEASURED extractor displacement `D` is a fresh non-circular
  binder (`ExtractorSpec.lip` bounds ONE extractor on TWO
  inputs — it cannot bound two extractors). Composed:
  `boundary_damage_bound` / `derived_boundary_damage` give
  `|ΔCE| ≤ 2 * headLip * D`, and the C408 variant trajectory
  `alternating_trajectory_bound_derived` replaces every `delta`
  by the derived `2 * headLip * D`. The feature → fullObjective
  bridge remains OPEN: in the derived variant the fullObjective
  channel keeps premise-form with the DERIVED constant.
- **Re-certification is an EXISTENCE premise.** On admission, a
  fresh certified head carrier `U'` (fresh alignment/curvature
  constants A', C' from `UniversalSafeStep` fields) must EXIST at
  the new extractor. It is the consumer's channel for starting the
  next `HeadPhase`; the trajectory bound does not depend on it,
  and its values are not constructed here.
- The bound's content is the DECOMPOSITION (drops, penalties,
  boundary damages separated) plus the discipline theorems (only
  admitted boundaries move the extractor, only at multiples of
  `K`); a consumer instantiating huge `delta`s gets a weak bound —
  that is the honest price of premise-form.

Layer decision: Training (8), same as CRMSM (C396) — the module
must see the CR-MSM skeleton (8), the C392 master theorem (7) and
the C387 carrier; only layer 8 can.
-/

set_option relaxedAutoImplicit false

open Hagi.Semantics Hagi.Training Hagi.Theory Hagi.State
open Hagi.Training.CRMSM

namespace Hagi.Training.AlternatingJoint

/-! ## The alternating schedule -/

/-- The alternating schedule: the extractor may update only every
`K` steps (C380-style rare-update period). The period discipline
itself is carried by `AlternatingTrajectory.periodic`; this record
pins the period and its positivity. -/
structure AlternatingSchedule where
  /-- The rarity period: extractor steps only at multiples of K. -/
  K : ℕ
  /-- The period is positive (a degenerate K = 0 schedule would
  make every step a boundary and is excluded). -/
  K_pos : 0 < K

/-! ## Head phases: the extractor is frozen -/

variable {Θ X V F : Type} [NormedAddCommGroup X] [NormedAddCommGroup F]
variable {mE rE dE : ℕ}

/-- A head phase of length `K` at a FROZEN extractor: a sequence
of CR-MSM blocks whose extractors are all equal to the phase-start
extractor, and a head-parameter trajectory following the C387
universal steps. The freezing premise is exactly what makes the
C396 head wiring apply — the separation lemma's precondition holds
by freezing, not by a joint-update argument. -/
structure HeadPhase (K : ℕ) (U : Hagi.Theory.CEChain.UniversalSafeStep Θ)
    where
  /-- The CR-MSM blocks across the phase. -/
  blocks : ℕ → CRMSMBlock Θ X V F mE rE dE
  /-- The head parameters after each step. -/
  θs : ℕ → Θ
  /-- The extractor is FROZEN within the phase: every block's
  extractor equals the phase-start one. -/
  frozen : ∀ j ≤ K, (blocks j).extractor = (blocks 0).extractor
  /-- The head follows the C387 universal step at the universal
  step size. -/
  headSteps : ∀ j < K, θs (j + 1) =
    U.step (θs j) (Hagi.Theory.CEChain.universalStepSize U (θs j))
  /-- The curvature premise holds at every visited head point. -/
  curvaturePos : ∀ j ≤ K, 0 < U.curvature (θs j)

/-- Phase certification: within a head phase EVERY step carries
`HeadControl` — the C396 fixed-extractor bridge applies verbatim,
the extractor-equality channel supplied by freezing. This is the
phase-level restatement of `crmsm_head_step_safe` over a frozen
sequence; no new mathematics. -/
theorem head_phase_certified (K : ℕ)
    (U : Hagi.Theory.CEChain.UniversalSafeStep Θ)
    (hp : HeadPhase (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) K U) (j : ℕ) (hj : j < K) :
    HeadControl (hp.blocks j) (hp.blocks (j + 1)) U (hp.θs j) :=
  crmsm_head_step_safe _ _
    ((hp.frozen j (by omega)).trans (hp.frozen (j + 1) (by omega)).symm)
    U _ (hp.curvaturePos j (by omega))

/-- Phase bound: at a frozen extractor the head loss telescopes
the C387 universal drops over the whole phase — the phase-level
counterpart of the per-step `universal_descent`. -/
theorem head_phase_bound (K : ℕ)
    (U : Hagi.Theory.CEChain.UniversalSafeStep Θ)
    (hp : HeadPhase (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) K U) :
    U.loss (hp.θs K) ≤ U.loss (hp.θs 0)
      - ∑ j ∈ Finset.range K, Hagi.Theory.CEChain.universalDrop U (hp.θs j) := by
  have key : ∀ j < K, U.loss (hp.θs (j + 1))
      ≤ U.loss (hp.θs j)
        - Hagi.Theory.CEChain.universalDrop U (hp.θs j) := by
    intro j hj
    rw [hp.headSteps j hj]
    exact Hagi.Theory.CEChain.universal_descent U (hp.θs j)
      (hp.curvaturePos j (by omega))
  have h := obj_telescope_err K (fun j => U.loss (hp.θs j))
    (fun j => Hagi.Theory.CEChain.universalDrop U (hp.θs j))
    (fun _ => (0 : ℝ)) (fun j hj => by linarith [key j hj])
  simpa using h

/-! ## Extractor boundaries: gated by admission + damage premise -/

variable {n a e q r c k : ℕ}

/-- A phase boundary: the extractor update event between two
canonical states, GATED by the C390 admission rule (no
free-floating decision — the recorded decision is EXACTLY
`admitRule proposal`), with the honest damage bookkeeping:
- the extractor moves ONLY on an admitted decision (iff);
- the full-objective change across the boundary is bounded by the
  PREMISE `delta ≥ 0` (see module pins: no descent guarantee for a
  nonconvex extractor update, and no cheap `ExtractorSpec.lip` →
  `fullObjective` bridge exists);
- on admission, a fresh certified head carrier must EXIST at the
  new extractor (re-certification, existence premise). -/
structure ExtractorBoundary (s s' : Hagi.State.CanonicalTrainState n a e q r c k)
    where
  /-- The block before the boundary. -/
  block : CRMSMBlock Θ X V F mE rE dE
  /-- The block after the boundary. -/
  block' : CRMSMBlock Θ X V F mE rE dE
  /-- The admission proposal of the extractor update. -/
  proposal : AdmissionProposal
  /-- The recorded decision. -/
  decision : Bool
  /-- No drift: the decision is exactly the C390 rule output. -/
  admit_ok : decision = admitRule proposal
  /-- The extractor moves IFF the boundary was admitted. -/
  extractor_moves_iff :
    decision = true ↔ block'.extractor ≠ block.extractor
  /-- The damage bound of the boundary (PREMISE-form). -/
  delta : ℝ
  /-- The damage bound is nonnegative. -/
  delta_nonneg : 0 ≤ delta
  /-- The full objective changes by at most `delta` across the
  boundary (PREMISE: the only bound on extractor-update damage). -/
  damage : Hagi.State.fullObjective s' ≤ Hagi.State.fullObjective s + delta
  /-- Re-certification (existence premise): on admission, a fresh
  certified C387 head carrier exists at the new extractor — the
  fresh alignment/curvature constants A', C' of the next phase. -/
  recertified : decision = true →
    ∃ U' : Hagi.Theory.CEChain.UniversalSafeStep Θ,
      ∀ θ : Θ, 0 < U'.curvature θ

/-- The boundary gate, admission direction: an admitted extractor
update forces a strictly positive admission margin AND the
re-certification premise to hold. The extractor cannot move
against the C390 gate (refusal direction:
`boundary_refusal_freezes` below). -/
theorem extractor_phase_admitted
    {s s' : Hagi.State.CanonicalTrainState n a e q r c k}
    (hb : ExtractorBoundary (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) s s')
    (hd : hb.decision = true) :
    0 < admissionMargin hb.proposal ∧
      ∃ U' : Hagi.Theory.CEChain.UniversalSafeStep Θ,
        ∀ θ : Θ, 0 < U'.curvature θ := by
  refine ⟨?_, hb.recertified hd⟩
  have hrule : admitRule hb.proposal = true := by
    rw [← hb.admit_ok]; exact hd
  exact admitRule_iff hb.proposal |>.mp hrule

/-- The boundary gate, refusal direction (safe degradation): a
refused boundary leaves the extractor UNCHANGED — the next phase
proceeds at the SAME extractor, so `head_phase_certified` applies
verbatim to the continuation (not a deadlock) — and the damage
bound still holds. -/
theorem boundary_refusal_freezes
    {s s' : Hagi.State.CanonicalTrainState n a e q r c k}
    (hb : ExtractorBoundary (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) s s')
    (hd : hb.decision = false) :
    hb.block'.extractor = hb.block.extractor ∧
      Hagi.State.fullObjective s' ≤ Hagi.State.fullObjective s + hb.delta := by
  refine ⟨?_, hb.damage⟩
  by_contra hne
  have := hb.extractor_moves_iff.mpr hne
  exact absurd this (by rw [hd]; simp)

/-! ## The alternating trajectory -/

/-- The kind of an alternating-trajectory step: a certified head
step (extractor frozen), an extractor boundary step (admission-
gated, damage-bounded), or a hold (identity, C363 semantics). -/
inductive AltStepKind where
  /-- A head step at a frozen extractor (carries a CRMSMStep). -/
  | headStep : AltStepKind
  /-- An extractor boundary (carries an ExtractorBoundary). -/
  | extractorStep : AltStepKind
  /-- A hold: the state does not move. -/
  | holdStep : AltStepKind
deriving DecidableEq

/-- The alternating trajectory: `T` canonical-state steps, each a
certified head step (a C396 `CRMSMStep` — hence a C392
`MasterStepCert`), an admission-gated extractor boundary, or a
hold. The C380-style rare-update discipline is explicit: extractor
boundaries occur ONLY at indices `j` with `(j + 1) % K = 0`. -/
structure AlternatingTrajectory (T : ℕ) where
  /-- The alternating schedule (the rarity period K). -/
  sch : AlternatingSchedule
  /-- The states: `states j` after j steps. -/
  states : ℕ → Hagi.State.CanonicalTrainState n a e q r c k
  /-- The kind of each step. -/
  kinds : ℕ → AltStepKind
  /-- Head steps carry the C396 CR-MSM step certificate (at a
  frozen extractor, with the C392 master certificate inside). -/
  headCerts : ∀ j < T, kinds j = AltStepKind.headStep →
    CRMSMStep (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (states j) (states (j + 1))
  /-- Extractor steps carry the gated boundary record. -/
  boundaries : ∀ j < T, kinds j = AltStepKind.extractorStep →
    ExtractorBoundary (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (states j) (states (j + 1))
  /-- Holds are identities (safe refusal, C363). -/
  holdIds : ∀ j < T, kinds j = AltStepKind.holdStep →
    states (j + 1) = states j
  /-- Rare-update discipline: extractor boundaries only at
  multiples of the schedule period (C380 pattern). -/
  periodic : ∀ j < T, kinds j = AltStepKind.extractorStep →
    (j + 1) % sch.K = 0

/-- The certified drop of step `j` as a total function: the
master-certificate drop on head steps, 0 otherwise. -/
noncomputable def AlternatingTrajectory.stepDrop (T : ℕ)
    (tr : AlternatingTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) T) (j : ℕ) : ℝ :=
  if h : j < T ∧ tr.kinds j = AltStepKind.headStep then
    (tr.headCerts j h.1 h.2).master.drop else 0

/-- The compression penalty of step `j` as a total function: the
master-certificate penalty on head steps, 0 otherwise. -/
noncomputable def AlternatingTrajectory.stepPenalty (T : ℕ)
    (tr : AlternatingTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) T) (j : ℕ) : ℝ :=
  if h : j < T ∧ tr.kinds j = AltStepKind.headStep then
    (tr.headCerts j h.1 h.2).master.penalty else 0

/-- The boundary damage of step `j` as a total function: the
premise `delta` on extractor boundaries, 0 otherwise. -/
noncomputable def AlternatingTrajectory.stepDamage (T : ℕ)
    (tr : AlternatingTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) T) (j : ℕ) : ℝ :=
  if h : j < T ∧ tr.kinds j = AltStepKind.extractorStep then
    (tr.boundaries j h.1 h.2).delta else 0

/-- The alternating trajectory bound: over `T` steps the full
objective is bounded by its start MINUS the sum of certified head
drops PLUS the sum of compression penalties PLUS the sum of
boundary damages. Head phases descend (C392 via C396, extractor
frozen); extractor boundaries pay their premise damage; holds are
free. The decomposition IS the result — the simultaneous joint
update remains pinned (C396 `crmsm_joint_separation`, untouched).
Proof: per-step key by kind discipline, then the generic
telescope `obj_telescope_err`. -/
theorem alternating_trajectory_bound (T : ℕ)
    (tr : AlternatingTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) T) :
    Hagi.State.fullObjective (tr.states T) ≤ Hagi.State.fullObjective (tr.states 0)
      - ∑ j ∈ Finset.range T, tr.stepDrop T j
      + ∑ j ∈ Finset.range T, tr.stepPenalty T j
      + ∑ j ∈ Finset.range T, tr.stepDamage T j := by
  have key : ∀ j < T, Hagi.State.fullObjective (tr.states (j + 1))
      ≤ Hagi.State.fullObjective (tr.states j) - tr.stepDrop T j
        + tr.stepPenalty T j + tr.stepDamage T j := by
    intro j hj
    cases hkind : tr.kinds j with
    | headStep =>
      have hd : tr.stepDrop T j =
          (tr.headCerts j hj hkind).master.drop := by
        simp [AlternatingTrajectory.stepDrop, hkind, hj]
      have hp : tr.stepPenalty T j =
          (tr.headCerts j hj hkind).master.penalty := by
        simp [AlternatingTrajectory.stepPenalty, hkind, hj]
      have hdm : tr.stepDamage T j = 0 := by
        simp [AlternatingTrajectory.stepDamage, hkind]
      rw [hd, hp, hdm]
      have := (tr.headCerts j hj hkind).master.descent
      linarith
    | extractorStep =>
      have hd : tr.stepDrop T j = 0 := by
        simp [AlternatingTrajectory.stepDrop, hkind]
      have hp : tr.stepPenalty T j = 0 := by
        simp [AlternatingTrajectory.stepPenalty, hkind]
      have hdm : tr.stepDamage T j =
          (tr.boundaries j hj hkind).delta := by
        simp [AlternatingTrajectory.stepDamage, hkind, hj]
      rw [hd, hp, hdm]
      have := (tr.boundaries j hj hkind).damage
      linarith
    | holdStep =>
      rw [tr.holdIds j hj hkind]
      have hd : tr.stepDrop T j = 0 := by
        simp [AlternatingTrajectory.stepDrop, hkind]
      have hp : tr.stepPenalty T j = 0 := by
        simp [AlternatingTrajectory.stepPenalty, hkind]
      have hdm : tr.stepDamage T j = 0 := by
        simp [AlternatingTrajectory.stepDamage, hkind]
      rw [hd, hp, hdm]
      linarith
  have h := obj_telescope_err T (fun j => Hagi.State.fullObjective (tr.states j))
    (tr.stepDrop T) (fun j => tr.stepPenalty T j + tr.stepDamage T j)
    (fun j hj => by linarith [key j hj])
  rw [Finset.sum_add_distrib] at h
  linarith

/-! ## C408: the extractor-damage bridge (derived boundary damage)

The C402 boundary damage was PREMISE-form (`delta`). This section
DERIVES the damage on the CE-head channel from two honest inputs:
the CE head is 2-Lipschitz in the logits (sup norm), and the head
logit map is Lipschitz in the FEATURES with the consumer's binder
`headLip`; composing with the MEASURED extractor displacement
binder `D` at the boundary gives the derived damage `2 * headLip * D`.
The C402 declarations above are FROZEN and untouched. -/

/-- One-sided shift bound for `lse`: if every coordinate of `a`
is at most `b + d`, then `lse a ≤ lse b + d`. Elementary:
exp-monotonicity, sum bound, then log of the product. -/
theorem lse_shift_le {κ : Type} [Fintype κ] [Nonempty κ] (d : ℝ)
    (a b : κ → ℝ) (h : ∀ v, a v ≤ b v + d) :
    Hagi.Core.lse a ≤ Hagi.Core.lse b + d := by
  have hsum : ∑ v, Real.exp (a v) ≤ Real.exp d * ∑ v, Real.exp (b v) := by
    have hexp : ∀ v : κ, Real.exp (a v) ≤ Real.exp d * Real.exp (b v) := by
      intro v
      calc Real.exp (a v) ≤ Real.exp (b v + d) := Real.exp_le_exp.mpr (h v)
        _ = Real.exp d * Real.exp (b v) := by rw [Real.exp_add]; ring
    calc ∑ v, Real.exp (a v)
        ≤ ∑ v, Real.exp d * Real.exp (b v) :=
          Finset.sum_le_sum fun v _ => hexp v
      _ = Real.exp d * ∑ v, Real.exp (b v) := by rw [Finset.mul_sum]
  have hlog := Real.log_le_log (by positivity) hsum
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] at hlog
  simp only [Hagi.Core.lse]
  linarith

/-- `lse` is 1-Lipschitz in the pi sup norm of the logit space. -/
theorem lse_lipschitz {κ : Type} [Fintype κ] [Nonempty κ] (a b : κ → ℝ) :
    |Hagi.Core.lse a - Hagi.Core.lse b| ≤ ‖a - b‖ := by
  have hpt : ∀ i : κ, |(a - b) i| ≤ ‖a - b‖ := by
    have hx : ∀ i : κ, ‖(a - b) i‖ ≤ ‖a - b‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg (a - b))).mp le_rfl
    exact hx
  apply abs_le.mpr
  constructor
  · have e2 := lse_shift_le ‖a - b‖ b a
        (fun v => by
          have h1 := abs_le.mp (hpt v)
          simp only [Pi.sub_apply] at h1
          linarith)
    linarith
  · have e1 := lse_shift_le ‖a - b‖ a b
        (fun v => by
          have h1 := abs_le.mp (hpt v)
          simp only [Pi.sub_apply] at h1
          linarith)
    linarith

/-- The CE head is 2-Lipschitz in the logits (pi sup norm on the
logit space): both summands of `ceOneHot t z = lse z − z t` are
individually 1-Lipschitz in the SAME norm, so L_x = 2 with no
norm smuggling. This is the head-side constant of the derived
damage bound below. -/
theorem ce_head_lipschitz_in_logits {κ : Type} [Fintype κ] [Nonempty κ]
    (t : κ) (z z' : κ → ℝ) :
    |Hagi.Core.ceOneHot t z - Hagi.Core.ceOneHot t z'| ≤ 2 * ‖z - z'‖ := by
  have hpt : ∀ i : κ, |(z - z') i| ≤ ‖z - z'‖ := by
    have hx : ∀ i : κ, ‖(z - z') i‖ ≤ ‖z - z'‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg (z - z'))).mp le_rfl
    exact hx
  have h1 := lse_lipschitz z z'
  have h2 := hpt t
  have hsplit : Hagi.Core.lse z - z t - (Hagi.Core.lse z' - z' t)
      = (Hagi.Core.lse z - Hagi.Core.lse z') - (z t - z' t) := by ring
  have htr : (Hagi.Core.lse z - Hagi.Core.lse z') - (z t - z' t)
      = (Hagi.Core.lse z - Hagi.Core.lse z') + (-(z t - z' t)) := by ring
  have habs : |z t - z' t| ≤ ‖z - z'‖ := by
    simpa [Pi.sub_apply, Real.norm_eq_abs] using h2
  unfold Hagi.Core.ceOneHot
  rw [hsplit, htr]
  calc |Hagi.Core.lse z - Hagi.Core.lse z' + -(z t - z' t)|
      ≤ |Hagi.Core.lse z - Hagi.Core.lse z'| + |-(z t - z' t)| :=
          abs_add_le _ _
    _ ≤ ‖z - z'‖ + |-(z t - z' t)| := add_le_add h1 (le_refl _)
    _ ≤ ‖z - z'‖ + ‖z - z'‖ := by
        rw [abs_neg]
        exact add_le_add (le_refl _) habs
    _ = 2 * ‖z - z'‖ := by ring

/-! ### The composed damage bound at a boundary

The DERIVED damage: the CE-head objective change across an
extractor boundary, evaluated at any head parameters, input and
target, is bounded by `2 * headLip * D` where
- `headLip` is the head logit map's Lipschitz constant in its
  FEATURE argument (consumer's premise; for a linear head this
  is the operator-norm bound), and
- `D` is the MEASURED extractor displacement at the boundary —
  the binder `‖spec'.extract x − spec.extract x‖ ≤ D`.

Honesty: `D` is NOT derivable from `ExtractorSpec.lip` — that
field bounds ONE extractor on TWO inputs, while a boundary
changes the extractor itself; deriving D from lip would be
circular (the update magnitude is the unknown being measured).
`D` is a fresh, non-circular binder over the measured change. -/

/-- The composed boundary damage bound: at a phase boundary the
extractor moves from `spec` to `spec'`; if the head logit map is
`headLip`-Lipschitz in the feature argument and the measured
extractor displacement at `x` is at most `D`, then the CE-head
objective changes by at most `2 * headLip * D` (CE head is
2-Lipschitz in the logits, sup norm — `ce_head_lipschitz_in_logits`). -/
theorem boundary_damage_bound {V : Type} [Fintype V] [Nonempty V]
    (head : Θ → F → (V → ℝ)) (headLip : ℝ) (headLip_nonneg : 0 ≤ headLip)
    (hlip : ∀ θ : Θ, ∀ f f' : F, ‖head θ f - head θ f'‖ ≤ headLip * ‖f - f'‖)
    (spec spec' : ExtractorSpec X F) (x : X) (D : ℝ)
    (disp : ‖spec'.extract x - spec.extract x‖ ≤ D)
    (θ : Θ) (t : V) :
    |Hagi.Core.ceOneHot t (head θ (spec'.extract x))
      - Hagi.Core.ceOneHot t (head θ (spec.extract x))|
      ≤ 2 * headLip * D := by
  have hhead := hlip θ (spec'.extract x) (spec.extract x)
  have hce := ce_head_lipschitz_in_logits t
    (head θ (spec'.extract x)) (head θ (spec.extract x))
  have h2 := hce.trans (by
    calc 2 * ‖head θ (spec'.extract x) - head θ (spec.extract x)‖
        ≤ 2 * (headLip * ‖spec'.extract x - spec.extract x‖) := by
          gcongr
      _ ≤ 2 * (headLip * D) := by
          gcongr
      _ = 2 * headLip * D := by ring)
  exact h2

/-! ### The derived boundary variant and trajectory corollary -/

/-- The DERIVED variant of `ExtractorBoundary`: the same
admission-gated boundary record WITHOUT the opaque `delta`
damage premise. Instead the boundary carries the head logit map,
its Lipschitz-in-features constant `headLip`, and the MEASURED
extractor displacement binder `D`; the CE-channel damage is then
a THEOREM (`derived_boundary_damage`), and the fullObjective
channel keeps a premise whose CONSTANT is the derived value
`2 * headLip * D` (the feature → fullObjective bridge remains
open — the C402 honesty pin). -/
structure DerivedExtractorBoundary [Fintype V] [Nonempty V]
    (s s' : Hagi.State.CanonicalTrainState n a e q r c k) where
  /-- The block before the boundary. -/
  block : CRMSMBlock Θ X V F mE rE dE
  /-- The block after the boundary. -/
  block' : CRMSMBlock Θ X V F mE rE dE
  /-- The admission proposal of the extractor update. -/
  proposal : AdmissionProposal
  /-- The recorded decision. -/
  decision : Bool
  /-- No drift: the decision is exactly the C390 rule output. -/
  admit_ok : decision = admitRule proposal
  /-- The extractor moves IFF the boundary was admitted. -/
  extractor_moves_iff :
    decision = true ↔ block'.extractor ≠ block.extractor
  /-- The head logit map: head parameters and FEATURES to logits
  (the `ModelSpec.head` shape with the feature space as input). -/
  head : Θ → F → (V → ℝ)
  /-- The head's Lipschitz constant in the FEATURE argument. -/
  headLip : ℝ
  /-- The head's Lipschitz constant is nonnegative. -/
  headLip_nonneg : 0 ≤ headLip
  /-- The head Lipschitz law in the feature argument (premise;
  for a linear head this is the operator-norm bound). -/
  head_lip : ∀ θ : Θ, ∀ f f' : F,
    ‖head θ f - head θ f'‖ ≤ headLip * ‖f - f'‖
  /-- The MEASURED extractor displacement at the boundary
  (non-circular binder: NOT derivable from `ExtractorSpec.lip`). -/
  D : ℝ
  /-- The displacement is nonnegative. -/
  D_nonneg : 0 ≤ D
  /-- Every input's feature displacement is at most `D`. -/
  disp : ∀ x : X, ‖block'.extractor.extract x - block.extractor.extract x‖ ≤ D
  /-- The fullObjective channel (premise-form, C402 pin) with the
  DERIVED constant `2 * headLip * D`. -/
  damage_derived : Hagi.State.fullObjective s'
    ≤ Hagi.State.fullObjective s + 2 * headLip * D

/-- The derived boundary damage (CE channel, fully DERIVED): at a
derived boundary the CE-head objective change across the boundary
is at most `2 * headLip * D` — for every head parameter point,
input and target. This is the bridge that replaces the opaque
`delta` premise on the CE-head channel. -/
theorem derived_boundary_damage [Fintype V] [Nonempty V]
    {s s' : Hagi.State.CanonicalTrainState n a e q r c k}
    (hb : DerivedExtractorBoundary (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) s s')
    (θ : Θ) (x : X) (t : V) :
    |Hagi.Core.ceOneHot t (hb.head θ (hb.block'.extractor.extract x))
      - Hagi.Core.ceOneHot t (hb.head θ (hb.block.extractor.extract x))|
      ≤ 2 * hb.headLip * hb.D :=
  boundary_damage_bound hb.head hb.headLip hb.headLip_nonneg hb.head_lip
    hb.block.extractor hb.block'.extractor x hb.D (hb.disp x) θ t

/-- The derived alternating trajectory: same discipline as
`AlternatingTrajectory`, but the extractor boundaries carry the
DERIVED damage structure (`DerivedExtractorBoundary`) instead of
the opaque `delta` premise. -/
structure DerivedAlternatingTrajectory [Fintype V] [Nonempty V] (T : ℕ) where
  /-- The alternating schedule (the rarity period K). -/
  sch : AlternatingSchedule
  /-- The states: `states j` after j steps. -/
  states : ℕ → Hagi.State.CanonicalTrainState n a e q r c k
  /-- The kind of each step. -/
  kinds : ℕ → AltStepKind
  /-- Head steps carry the C396 CR-MSM step certificate. -/
  headCerts : ∀ j < T, kinds j = AltStepKind.headStep →
    CRMSMStep (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (states j) (states (j + 1))
  /-- Extractor steps carry the DERIVED boundary record. -/
  boundaries : ∀ j < T, kinds j = AltStepKind.extractorStep →
    DerivedExtractorBoundary (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) (states j) (states (j + 1))
  /-- Holds are identities (safe refusal, C363). -/
  holdIds : ∀ j < T, kinds j = AltStepKind.holdStep →
    states (j + 1) = states j
  /-- Rare-update discipline: extractor boundaries only at
  multiples of the schedule period (C380 pattern). -/
  periodic : ∀ j < T, kinds j = AltStepKind.extractorStep →
    (j + 1) % sch.K = 0

/-- The certified drop of step `j` of a derived trajectory: the
master-certificate drop on head steps, 0 otherwise. -/
noncomputable def DerivedAlternatingTrajectory.stepDrop' [Fintype V] [Nonempty V] (T : ℕ)
    (tr : DerivedAlternatingTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) T) (j : ℕ) : ℝ :=
  if h : j < T ∧ tr.kinds j = AltStepKind.headStep then
    (tr.headCerts j h.1 h.2).master.drop else 0

/-- The compression penalty of step `j` of a derived trajectory:
the master-certificate penalty on head steps, 0 otherwise. -/
noncomputable def DerivedAlternatingTrajectory.stepPenalty' [Fintype V] [Nonempty V] (T : ℕ)
    (tr : DerivedAlternatingTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) T) (j : ℕ) : ℝ :=
  if h : j < T ∧ tr.kinds j = AltStepKind.headStep then
    (tr.headCerts j h.1 h.2).master.penalty else 0

/-- The derived boundary damage of step `j`: the DERIVED constant
`2 * headLip * D` on extractor steps, 0 otherwise. -/
noncomputable def DerivedAlternatingTrajectory.derivedStepDamage [Fintype V] [Nonempty V] (T : ℕ)
    (tr : DerivedAlternatingTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) T) (j : ℕ) : ℝ :=
  if h : j < T ∧ tr.kinds j = AltStepKind.extractorStep then
    2 * (tr.boundaries j h.1 h.2).headLip * (tr.boundaries j h.1 h.2).D
  else 0

/-- The DERIVED alternating trajectory bound (C408): over `T`
steps the full objective is bounded by its start MINUS the sum of
certified head drops PLUS the sum of compression penalties PLUS
the sum of DERIVED boundary damages `2 * headLip * D` — no opaque
`delta` binder anywhere. The CE-channel component of each
boundary's damage is fully derived
(`derived_boundary_damage`); the fullObjective channel keeps the
C402 premise with the derived constant. Proof mirrors
`alternating_trajectory_bound` (per-step key by kind discipline,
then the generic telescope). -/
theorem alternating_trajectory_bound_derived [Fintype V] [Nonempty V] (T : ℕ)
    (tr : DerivedAlternatingTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) (Θ := Θ) (X := X) (V := V) (F := F)
      (mE := mE) (rE := rE) (dE := dE) T) :
    Hagi.State.fullObjective (tr.states T) ≤ Hagi.State.fullObjective (tr.states 0)
      - ∑ j ∈ Finset.range T, tr.stepDrop' T j
      + ∑ j ∈ Finset.range T, tr.stepPenalty' T j
      + ∑ j ∈ Finset.range T, tr.derivedStepDamage T j := by
  have key : ∀ j < T, Hagi.State.fullObjective (tr.states (j + 1))
      ≤ Hagi.State.fullObjective (tr.states j) - tr.stepDrop' T j
        + tr.stepPenalty' T j + tr.derivedStepDamage T j := by
    intro j hj
    cases hkind : tr.kinds j with
    | headStep =>
      have hd : tr.stepDrop' T j =
          (tr.headCerts j hj hkind).master.drop := by
        simp [DerivedAlternatingTrajectory.stepDrop', hkind, hj]
      have hp : tr.stepPenalty' T j =
          (tr.headCerts j hj hkind).master.penalty := by
        simp [DerivedAlternatingTrajectory.stepPenalty', hkind, hj]
      have hdm : tr.derivedStepDamage T j = 0 := by
        simp [DerivedAlternatingTrajectory.derivedStepDamage, hkind]
      rw [hd, hp, hdm]
      have := (tr.headCerts j hj hkind).master.descent
      linarith
    | extractorStep =>
      have hd : tr.stepDrop' T j = 0 := by
        simp [DerivedAlternatingTrajectory.stepDrop', hkind]
      have hp : tr.stepPenalty' T j = 0 := by
        simp [DerivedAlternatingTrajectory.stepPenalty', hkind]
      have hdm : tr.derivedStepDamage T j =
          2 * (tr.boundaries j hj hkind).headLip
            * (tr.boundaries j hj hkind).D := by
        simp [DerivedAlternatingTrajectory.derivedStepDamage, hkind, hj]
      rw [hd, hp, hdm]
      have := (tr.boundaries j hj hkind).damage_derived
      linarith
    | holdStep =>
      rw [tr.holdIds j hj hkind]
      have hd : tr.stepDrop' T j = 0 := by
        simp [DerivedAlternatingTrajectory.stepDrop', hkind]
      have hp : tr.stepPenalty' T j = 0 := by
        simp [DerivedAlternatingTrajectory.stepPenalty', hkind]
      have hdm : tr.derivedStepDamage T j = 0 := by
        simp [DerivedAlternatingTrajectory.derivedStepDamage, hkind]
      rw [hd, hp, hdm]
      linarith
  have h := obj_telescope_err T (fun j => Hagi.State.fullObjective (tr.states j))
    (tr.stepDrop' T) (fun j => tr.stepPenalty' T j + tr.derivedStepDamage T j)
    (fun j hj => by linarith [key j hj])
  rw [Finset.sum_add_distrib] at h
  linarith

end Hagi.Training.AlternatingJoint
