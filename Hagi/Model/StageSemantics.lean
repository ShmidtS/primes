/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Hagi.System.GrowthState
set_option linter.style.header false

/-!
# StageSemantics — per-cycle stage inputs (audit P1 repair)

Repair of the two structural defects proven by the audit
regressions (`corePremises_two_step_decrease_nonpos`,
`full_cycle_two_step_growth_inconsistent`):

* the measured stage effects are an INPUT of each cycle
  (`StageInput`), not a stored fixed record; successive cycles
  may carry DIFFERENT measurements;
* spends are nonnegative and the SafeQP step is active
  (`0 < eta`) by construction — part of the input's type;
* the growth law is stated as a WINDOW
  `(1+α_min)·C_t ≤ C_{t+1} ≤ (1+α_cap)·C_t` with
  `α_min ≤ α_cap` — no squeezing into exact saturation
  (contrast `FrontierScaling.takeoff_edge_forced`).

Main items:

* `advance` — one composed cycle over fresh measurements;
* `Trajectory` — states linked by `advance` with per-cycle inputs;
* `advance_energy_drop` — one-cycle energy certificate;
* `cone_growth_window` — the un-squeezed growth law;
* `two_cycle_varying_gain_nonvacuous` — a concrete two-cycle
  witness with strictly positive, DISTINCT gains and strictly
  decreasing energy (impossible under the fixed-effects model
  by `full_cycle_two_step_growth_inconsistent`).
-/

namespace Hagi.Model

open Hagi.System InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The measured evidence of ONE growth cycle (time-indexed).
Nonnegativity of spends and activity of the SafeQP step are
PROOF FIELDS of the type (audit 5.3/5.4: spends cannot be
negative credits; a non-null direction must act). -/
structure StageInput (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] where
  /-- Measured stage constants of this cycle. -/
  sp : StageParams
  /-- Measured stage effects of this cycle. -/
  eff : StageEffects
  /-- Measured merge gap of this cycle. -/
  gap : ℝ
  /-- The SafeQP descent direction of this cycle. -/
  stepDir : X
  /-- The energy gradient of this cycle. -/
  grad : X
  /-- Compute spends are honest (nonnegative) — ALL four
  stages (P1.3: merge and compression are not free). -/
  h_costs_nn : 0 ≤ eff.growCost ∧ 0 ≤ eff.mergeCost
    ∧ 0 ≤ eff.jointCost ∧ 0 ≤ eff.compressCost
  /-- Protected-risk spends are honest (nonnegative). -/
  h_risks_nn : 0 ≤ eff.growRisk ∧ 0 ≤ eff.mergeRisk
    ∧ 0 ≤ eff.jointRisk ∧ 0 ≤ eff.compressRisk
  /-- The step is ACTIVE: a non-null direction really moves. -/
  h_eta_pos : 0 < sp.eta

/-- One composed growth cycle over FRESH per-cycle measurements:
the successor state of `S` under input `u`. Energy and the
ledger are taken from `u` (not stored), capability gains the
measured gain of THIS cycle. -/
def advance (S : GrowthState X) (u : StageInput X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params - u.sp.eta • u.stepDir
  experts := S.experts + 1
  energy := u.eff.compressEnergy
  protectedRisk := S.protectedRisk + u.eff.growRisk + u.eff.mergeRisk
    + u.eff.jointRisk + u.eff.compressRisk
  budget := S.budget - u.eff.growCost - u.eff.mergeCost
      - u.eff.jointCost - u.eff.compressCost
  gap := u.gap
  dataField := S.dataField
  capability := S.capability + u.eff.growGain
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := u.stepDir
  grad := u.grad
  sp := u.sp
  effects := u.eff

/-- A run of `T` cycles: states linked by `advance` with the
per-cycle inputs of the run. -/
structure Trajectory (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] where
  /-- Horizon (number of cycles). -/
  T : ℕ
  /-- States `0 .. T`. -/
  state : ℕ → GrowthState X
  /-- Per-cycle inputs `0 .. T-1`. -/
  input : ℕ → StageInput X
  /-- Every step is an advance over that cycle's input. -/
  h_step : ∀ t < T, state (t + 1) = advance (state t) (input t)

/-! ### State-dependent effects (audit 2 / P2 repair, paid growth)

The two-step inconsistency
(`Examples/Nonvacuity.full_cycle_two_step_growth_inconsistent`)
showed that a FIXED per-trajectory effect cannot sustain a
geometric growth law: the gain must be recomputed FROM THE
CURRENT STATE at every cycle. This layer makes that explicit —
and PAID: the budget cost is proportional to capability
(growth is not free), with the cost honesty carried
constructively along the sequence. -/

/-- **State-dependent cycle effects**: measured effects
computed FROM the current state, not carried over. Gain
`alpha * C_t` (geometric law), budget cost `mu * C_t` (growth
is paid for); remaining entries are neutral placeholders, so
the productive dynamic is studied in isolation. -/
def stateGrowthEffects (alpha mu : ℝ) (S : GrowthState X) : StageEffects where
  growGain := alpha * S.capability
  growCost := mu * S.capability
  growRisk := 0
  growEnergy := S.energy
  mergeEnergy := S.energy
  mergeRisk := 0
  mergeCost := 0
  jointEnergy := S.energy
  jointRisk := 0
  jointCost := 0
  quantErr := 0
  compressEnergy := S.energy
  compressRisk := 0
  compressCost := 0

/-- The per-cycle input for the paid productive-growth cycle:
effects recomputed from the CURRENT state `S`; the honesty of
the proportional budget spend is exactly `hcost`. -/
noncomputable def growInput (alpha mu : ℝ) (S : GrowthState X)
    (hcost : 0 ≤ mu * S.capability) : StageInput X where
  sp.eta := 1
  sp.L := 1
  sp.kappa := 0
  sp.s := 0
  eff := stateGrowthEffects alpha mu S
  gap := 0
  stepDir := 0
  grad := 0
  h_costs_nn := ⟨hcost, le_refl _, le_refl _, le_refl _⟩
  h_risks_nn := ⟨le_refl _, ⟨le_refl _, ⟨le_refl _, le_refl _⟩⟩⟩
  h_eta_pos := by norm_num

/-- One productive growth cycle through the state-dependent
semantics: capability gains exactly `alpha * C_t` — the gain is
recomputed from the CURRENT state at every cycle. -/
theorem growAdvance_capability (alpha mu : ℝ) (S : GrowthState X)
    (hcost : 0 ≤ mu * S.capability) :
    (advance S (growInput alpha mu S hcost)).capability
      = S.capability + alpha * S.capability := by
  simp [advance, growInput, stateGrowthEffects]

/-- One paid cycle consumes exactly `mu * C_t` of budget. -/
theorem growAdvance_budget (alpha mu : ℝ) (S : GrowthState X)
    (hcost : 0 ≤ mu * S.capability) :
    (advance S (growInput alpha mu S hcost)).budget
      = S.budget - mu * S.capability := by
  simp [advance, growInput, stateGrowthEffects]

/-- **Two-step consistency (the mirror of the two-step
inconsistency)**: under paid state-dependent effects the
geometric growth law is SATISFIABLE on two consecutive cycles
— the second cycle recomputes BOTH its gain and its cost from
the ALREADY GROWN state. -/
theorem grow_two_step_consistent (alpha mu : ℝ) (S : GrowthState X)
    (hcost : 0 ≤ mu * S.capability) (hα1 : 0 ≤ 1 + alpha) :
    (advance (advance S (growInput alpha mu S hcost))
      (growInput alpha mu (advance S (growInput alpha mu S hcost))
        (by
          have hcap := growAdvance_capability alpha mu S hcost
          rw [hcap]
          have hrid : mu * (S.capability + alpha * S.capability)
            = (1 + alpha) * (mu * S.capability) := by ring
          rw [hrid]
          exact mul_nonneg hα1 hcost))).capability
      = (1 + alpha) ^ 2 * S.capability := by
  have hcap' : 0 ≤ mu
      * (advance S (growInput alpha mu S hcost)).capability := by
    have h1 := growAdvance_capability alpha mu S hcost
    rw [h1]
    have hrid : mu * (S.capability + alpha * S.capability)
      = (1 + alpha) * (mu * S.capability) := by ring
    rw [hrid]
    exact mul_nonneg hα1 hcost
  have h1 := growAdvance_capability alpha mu S hcost
  have h2 := growAdvance_capability alpha mu
    (advance S (growInput alpha mu S hcost)) hcap'
  rw [h1] at h2
  rw [h2]
  ring

/-- Across the horizon the paid state-dependent cycle is
strictly productive (capability strictly increases whenever
`alpha > 0` and the start is positive). -/
theorem grow_strict_productive (alpha mu : ℝ) (S : GrowthState X)
    (hcost : 0 ≤ mu * S.capability) (hα : 0 < alpha)
    (hC : 0 < S.capability) :
    S.capability < (advance S (growInput alpha mu S hcost)).capability := by
  rw [growAdvance_capability]
  linarith [mul_pos hα hC]

/-! ### Sustained takeoff on the honest paid trajectory

The third clause of the audit's trichotomy: capability growth
sustained over the WHOLE horizon by genuine `advance`
transitions with paid state-dependent effects, on ONE
trajectory that carries capability, energy AND the budget
ledger (audit section 3: all metrics from one dynamics). The
cost honesty `0 <= mu * C_t` is carried CONSTRUCTIVELY at
every step, so the recursion needs no external invariant. -/

/-- The honest paid productive sequence: each state carries the
invariant `0 <= mu * capability`, making every cycle's cost
honest by construction (no external invariant needed in the
recursion). -/
noncomputable def growSeq (alpha mu : ℝ) (hmu : 0 ≤ mu)
    (hα1 : 0 ≤ 1 + alpha)
    (S0 : {s : GrowthState X // 0 ≤ mu * s.capability}) :
    ℕ → {s : GrowthState X // 0 ≤ mu * s.capability}
  | 0 => S0
  | t + 1 =>
    let S := growSeq alpha mu hmu hα1 S0 t
    ⟨advance S.val (growInput alpha mu S.val S.property),
      by
        have hcap := growAdvance_capability alpha mu S.val S.property
        have hrid : mu * (S.val.capability + alpha * S.val.capability)
          = (1 + alpha) * (mu * S.val.capability) := by ring
        rw [hcap, hrid]
        exact mul_nonneg hα1 S.property⟩

/-- **Sustained takeoff (the honest-trajectory growth law)**:
after `t` genuine paid cycles
`capability = (1 + alpha)^t * C0` — every factor contributed by
a real transition whose gain AND cost were recomputed from the
current state. -/
theorem growSeq_capability (alpha mu : ℝ) (hmu : 0 ≤ mu)
    (hα1 : 0 ≤ 1 + alpha)
    (S0 : {s : GrowthState X // 0 ≤ mu * s.capability}) (t : ℕ) :
    (growSeq alpha mu hmu hα1 S0 t).val.capability
      = (1 + alpha) ^ t * S0.val.capability := by
  induction t with
  | zero => simp [growSeq]
  | succ t ih =>
      have hcap := growAdvance_capability alpha mu (growSeq alpha mu hmu hα1 S0 t).val
        (growSeq alpha mu hmu hα1 S0 t).property
      simp only [growSeq]
      rw [hcap, ih, pow_succ]
      ring

/-- **The unified budget ledger on the same trajectory**
(audit section 3: capability and budget from ONE dynamics):
after `t` paid cycles the remaining budget plus the total spend
recorded cycle-by-cycle equals the initial budget exactly

  `budget(t) + mu * SUM_{i<t} C_i = budget(0)`,

with `C_i = (1 + alpha)^i * C0` the SAME capability sequence as
in `growSeq_capability`. -/
theorem growSeq_budget_ledger (alpha mu : ℝ) (hmu : 0 ≤ mu)
    (hα1 : 0 ≤ 1 + alpha)
    (S0 : {s : GrowthState X // 0 ≤ mu * s.capability}) (t : ℕ) :
    (growSeq alpha mu hmu hα1 S0 t).val.budget
      + mu * (∑ i ∈ Finset.range t,
        (growSeq alpha mu hmu hα1 S0 i).val.capability)
      = S0.val.budget := by
  induction t with
  | zero => simp [growSeq]
  | succ t ih =>
      have hcost := (growSeq alpha mu hmu hα1 S0 t).property
      have hbud := growAdvance_budget alpha mu (growSeq alpha mu hmu hα1 S0 t).val hcost
      have hsum : (∑ i ∈ Finset.range (t + 1),
          (growSeq alpha mu hmu hα1 S0 i).val.capability)
        = (∑ i ∈ Finset.range t,
            (growSeq alpha mu hmu hα1 S0 i).val.capability)
          + (growSeq alpha mu hmu hα1 S0 t).val.capability := by
        rw [Finset.sum_range_succ]
      simp only [growSeq]
      rw [hbud, hsum]
      have hsplit : mu * ((∑ i ∈ Finset.range t,
            (growSeq alpha mu hmu hα1 S0 i).val.capability)
          + (growSeq alpha mu hmu hα1 S0 t).val.capability)
        = mu * (∑ i ∈ Finset.range t,
            (growSeq alpha mu hmu hα1 S0 i).val.capability)
          + mu * (growSeq alpha mu hmu hα1 S0 t).val.capability := by ring
      rw [hsplit]
      linarith [ih]

/-- The paid honest trajectory on horizon `T` assembled from
the invariant-carrying sequence. -/
noncomputable def growTraj (alpha mu : ℝ) (hmu : 0 ≤ mu)
    (hα1 : 0 ≤ 1 + alpha)
    (S0 : {s : GrowthState X // 0 ≤ mu * s.capability}) (T : ℕ) :
    Trajectory X where
  T := T
  state := fun t => (growSeq alpha mu hmu hα1 S0 t).val
  input := fun t => growInput alpha mu (growSeq alpha mu hmu hα1 S0 t).val
    (growSeq alpha mu hmu hα1 S0 t).property
  h_step := fun t _ => rfl

/-! ### The one-cycle energy certificate -/

/-- **One-cycle energy drop over fresh measurements**: under the
per-cycle stage laws (grow / merge / joint-smoothness / honest
compression ledger), the post-cycle energy is bounded by the
pre-cycle energy minus the cycle's certified drop
`gain + gap + (⟨grad, d⟩ − L·η²‖d‖²/2) − κ·s·quantErr`.
Pure bookkeeping: no window saturation needed, and the drop may
be STRICTLY positive for many consecutive cycles because every
cycle re-measures. -/
theorem advance_energy_drop (S : GrowthState X) (u : StageInput X)
    (hgain : u.eff.growEnergy ≤ S.energy - u.eff.growGain)
    (hgap0 : 0 ≤ u.gap)
    (hmerge : u.eff.mergeEnergy
      ≤ u.eff.growEnergy - u.gap)
    (hL : 0 < u.sp.L)
    (heta : u.sp.eta ≤ 1 / u.sp.L)
    (hdesc : ‖u.stepDir‖ ^ 2 ≤ ⟪u.grad, u.stepDir⟫_ℝ)
    (hjoint : u.eff.jointEnergy
      ≤ u.eff.mergeEnergy - u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        + u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
    (hledger : u.eff.compressEnergy - u.eff.jointEnergy
      ≤ u.sp.kappa * u.sp.s * u.eff.quantErr) :
    u.eff.compressEnergy ≤ S.energy - (u.eff.growGain + u.gap
      + (u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
      - u.sp.kappa * u.sp.s * u.eff.quantErr) := by
  linarith [hgain, hmerge, hjoint, hledger]

/-! ### The un-squeezed growth window -/

/-- **Growth window (audit repair of the saturation squeeze)**:
under the cone with minimal rate `α_min` (via production
`γ·D ≤ G`) and an UPPER CAP at a DISTINCT rate `α_cap ≥ α_min`,
the capability stays in the window
`(1+α_min)·C_t ≤ C_{t+1} ≤ (1+α_cap)·C_t` — both bounds are
simultaneously satisfiable BECAUSE they differ (contrast the
exact saturation `C_{t+1} = (1+α)·C_t` forced when the same α
plays both roles, `FrontierScaling.takeoff_edge_forced`). -/
theorem cone_growth_window (C G D : ℕ → ℝ) (α_min α_cap γ : ℝ)
    (hγ : 0 < γ) (hmin : 0 ≤ α_min) (hsep : α_min ≤ α_cap)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain : ∀ t, γ * D t ≤ G t)
    (h_cone : ∀ t, α_min / γ * C t ≤ D t) :
    (1 + α_min) * C t ≤ C (t + 1) := by
  have hc := h_cone t
  have hg := h_gain t
  have he : γ * (α_min / γ * C t) = α_min * C t := by field_simp
  have hchain : α_min * C t ≤ G t := by
    have h1 : γ * (α_min / γ * C t) ≤ γ * D t :=
      mul_le_mul_of_nonneg_left hc hγ.le
    rw [he] at h1
    exact le_trans h1 hg
  have hr : (1 + α_min) * C t = C t + α_min * C t := by ring
  rw [h_step t, hr]
  linarith

/-! ### The repaired semantics is nonvacuous: two active cycles -/

/-- Cycle-2 measurement: gain `4`, gap `1`, chain `19 >= 18 >= 17`
- yet another, strictly larger gain. -/
noncomputable def wU2 : StageInput ℝ where
  sp := { eta := 1, L := 1, kappa := 0, s := 0 }
  eff :=
    { growGain := 4, growCost := 1, growRisk := 0, growEnergy := 19
      mergeEnergy := 18, mergeRisk := 0, mergeCost := 0
      jointEnergy := 17, jointRisk := 0, jointCost := 1
      quantErr := 0, compressEnergy := 17, compressRisk := 0, compressCost := 0 }
  gap := 1
  stepDir := 1
  grad := 1
  h_costs_nn := by norm_num
  h_risks_nn := by norm_num
  h_eta_pos := by norm_num


/-- Witness state (carrier `X = ℝ`): pre-cycle energy `10`,
capability `1`; direction and gradient `1` (so the SafeQP window
holds exactly at `η = 1, L = 1`). -/
noncomputable def wS0 : GrowthState ℝ where
  weightDim := 0
  weights := fun _ => 0
  params := 1
  experts := 0
  energy := 30
  protectedRisk := 0
  budget := 100
  gap := 0
  dataField := 0
  capability := 1
  verifier := 0
  runtimeError := 0
  stepDir := 1
  grad := 1
  sp := { eta := 1, L := 1, kappa := 0, s := 0 }
  effects :=
    { growGain := 0, growCost := 0, growRisk := 0, growEnergy := 0
      mergeEnergy := 0, mergeRisk := 0, mergeCost := 0
      jointEnergy := 0, jointRisk := 0, jointCost := 0
      quantErr := 0, compressEnergy := 0, compressRisk := 0, compressCost := 0 }

/-- Cycle-0 measurement: gain `1`, gap `1`, chain `29 >= 8 >= 7`. -/
noncomputable def wU0 : StageInput ℝ where
  sp := { eta := 1, L := 1, kappa := 0, s := 0 }
  eff :=
    { growGain := 1, growCost := 1, growRisk := 0, growEnergy := 29
      mergeEnergy := 28, mergeRisk := 0, mergeCost := 0
      jointEnergy := 27, jointRisk := 0, jointCost := 1
      quantErr := 0, compressEnergy := 27, compressRisk := 0, compressCost := 0 }
  gap := 1
  stepDir := 1
  grad := 1
  h_costs_nn := by norm_num
  h_risks_nn := by norm_num
  h_eta_pos := by norm_num

/-- Cycle-1 measurement: gain `2`, gap `1`, chain `26 >= 4 >= 3`
- a DIFFERENT, strictly larger gain. -/
noncomputable def wU1 : StageInput ℝ where
  sp := { eta := 1, L := 1, kappa := 0, s := 0 }
  eff :=
    { growGain := 2, growCost := 1, growRisk := 0, growEnergy := 25
      mergeEnergy := 24, mergeRisk := 0, mergeCost := 0
      jointEnergy := 23, jointRisk := 0, jointCost := 1
      quantErr := 0, compressEnergy := 23, compressRisk := 0, compressCost := 0 }
  gap := 1
  stepDir := 1
  grad := 1
  h_costs_nn := by norm_num
  h_risks_nn := by norm_num
  h_eta_pos := by norm_num

/-- The input's activity premise survives one advance: the
successor's step direction/energy ledger are the SAME cycle's
input, but the NEXT cycle re-measures; here we record the trivial
lemma that `advance` copies `sp` from the input. -/
theorem advance_sp (S : GrowthState X) (u : StageInput X) :
    (advance S u).sp = u.sp := rfl

theorem eta_pos_of_advance (S : GrowthState X) (u : StageInput X) :
    0 < (advance S u).sp.eta := u.h_eta_pos

/-- **Three-cycle witness (the repaired semantics is nonvacuous
on the audit bar T >= 3)**: three consecutive `advance` cycles
over fresh inputs with strictly positive DISTINCT measured gains
(`1`, `2`, `4`), strictly decreasing energy (`30 - 27 - 23 - 17`),
geometrically growing capability (`1 - 2 - 4 - 8`, the cone window
at `alpha = 1`), active steps and honest nonnegative spends. Under
the old fixed-effects model this is IMPOSSIBLE
(`Hagi.Examples.full_cycle_two_step_growth_inconsistent`). -/
theorem three_cycle_varying_gain_nonvacuous :
    (advance wS0 wU0).energy = 27
    ∧ (advance (advance wS0 wU0) wU1).energy = 23
    ∧ (advance (advance (advance wS0 wU0) wU1) wU2).energy = 17
    ∧ (advance wS0 wU0).capability = 2
    ∧ (advance (advance wS0 wU0) wU1).capability = 4
    ∧ (advance (advance (advance wS0 wU0) wU1) wU2).capability = 8
    ∧ 0 < wU0.eff.growGain
    ∧ 0 < wU1.eff.growGain
    ∧ 0 < wU2.eff.growGain
    ∧ wU0.eff.growGain ≠ wU1.eff.growGain
    ∧ wU1.eff.growGain ≠ wU2.eff.growGain
    ∧ 0 < (advance wS0 wU0).sp.eta
    ∧ 0 < (advance (advance wS0 wU0) wU1).sp.eta
    ∧ 0 < (advance (advance (advance wS0 wU0) wU1) wU2).sp.eta := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [advance, wS0, wU0]; all_goals norm_num
  · simp [advance, wS0, wU0, wU1]; all_goals norm_num
  · simp [advance, wS0, wU0, wU1, wU2]; all_goals norm_num
  · simp [advance, wS0, wU0]; all_goals norm_num
  · simp [advance, wS0, wU0, wU1]; all_goals norm_num
  · simp [advance, wS0, wU0, wU1, wU2]; all_goals norm_num
  · simp [wU0]; all_goals norm_num
  · simp [wU1]; all_goals norm_num
  · simp [wU2]; all_goals norm_num
  · exact ne_of_lt (by simp [wU0, wU1]; all_goals norm_num)
  · exact ne_of_lt (by simp [wU1, wU2]; all_goals norm_num)
  · exact eta_pos_of_advance wS0 wU0
  · exact eta_pos_of_advance (advance wS0 wU0) wU1
  · exact eta_pos_of_advance (advance (advance wS0 wU0) wU1) wU2

/-- Both witness cycles satisfy the one-cycle stage laws, so
`advance_energy_drop` certifies strictly positive drops. -/
theorem two_cycle_certified_descent :
    (advance wS0 wU0).energy
      <= wS0.energy - (wU0.eff.growGain + wU0.gap
        + (wU0.sp.eta * ⟪wU0.grad, wU0.stepDir⟫_ℝ
          - wU0.sp.L * wU0.sp.eta ^ 2 * ‖wU0.stepDir‖ ^ 2 / 2)
        - wU0.sp.kappa * wU0.sp.s * wU0.eff.quantErr)
    ∧ (advance (advance wS0 wU0) wU1).energy
      <= (advance wS0 wU0).energy - (wU1.eff.growGain + wU1.gap
        + (wU1.sp.eta * ⟪wU1.grad, wU1.stepDir⟫_ℝ
          - wU1.sp.L * wU1.sp.eta ^ 2 * ‖wU1.stepDir‖ ^ 2 / 2)
        - wU1.sp.kappa * wU1.sp.s * wU1.eff.quantErr)
    ∧ (advance (advance (advance wS0 wU0) wU1) wU2).energy
      <= (advance (advance wS0 wU0) wU1).energy - (wU2.eff.growGain
        + wU2.gap
        + (wU2.sp.eta * ⟪wU2.grad, wU2.stepDir⟫_ℝ
          - wU2.sp.L * wU2.sp.eta ^ 2 * ‖wU2.stepDir‖ ^ 2 / 2)
        - wU2.sp.kappa * wU2.sp.s * wU2.eff.quantErr) := by
  constructor
  · refine advance_energy_drop wS0 wU0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (simp [wS0, wU0]; all_goals norm_num)
  constructor
  · refine advance_energy_drop (advance wS0 wU0) wU1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (simp [advance, wS0, wU0, wU1]; all_goals norm_num)
  · show wU2.eff.compressEnergy
      <= (advance (advance wS0 wU0) wU1).energy
        - (wU2.eff.growGain + wU2.gap
          + (wU2.sp.eta * ⟪wU2.grad, wU2.stepDir⟫_ℝ
            - wU2.sp.L * wU2.sp.eta ^ 2 * ‖wU2.stepDir‖ ^ 2 / 2)
          - wU2.sp.kappa * wU2.sp.s * wU2.eff.quantErr)
    refine advance_energy_drop (advance (advance wS0 wU0) wU1) wU2
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (simp [advance, wS0, wU0, wU1, wU2]; all_goals norm_num)

/-! ### Strengthening: fields, telescope, state-linked takeoff -/

/-- The successor's energy ledger comes verbatim from the cycle
input. -/
theorem advance_energy (S : GrowthState X) (u : StageInput X) :
    (advance S u).energy = u.eff.compressEnergy := rfl

/-- The successor's capability adds THIS cycle's measured gain. -/
theorem advance_capability (S : GrowthState X) (u : StageInput X) :
    (advance S u).capability = S.capability + u.eff.growGain := rfl

/-- **State-linked geometric amplification** (the repaired takeoff):
if every cycle of a trajectory measures a gain of at least
`alpha * C_t` (the cone+production collapse of
`takeoff_edge_forced`, now with per-cycle gains FREE to vary), the
capability grows geometrically:
`(state T).capability >= (1+alpha)^T * (state 0).capability`.
Unlike `state_capability_takeoff`-style hypotheses (unsatisfiable
at `T >= 2` under the fixed-effects model,
`full_cycle_two_step_growth_inconsistent`), these hypotheses are
REALIZED by the witness below. -/
theorem capability_takeoff_amplified (tr : Trajectory X) (alpha : ℝ)
    (hα : 0 ≤ alpha)
    (hgain : ∀ t < tr.T,
      alpha * (tr.state t).capability ≤ (tr.input t).eff.growGain)
    (t : ℕ) (ht : t ≤ tr.T) :
    (1 + alpha) ^ t * (tr.state 0).capability
      ≤ (tr.state t).capability := by
  induction t with
  | zero => simp
  | succ n ih =>
    have hn : n ≤ tr.T := by omega
    have hstep := tr.h_step n (by omega)
    have hg := hgain n (by omega)
    have hcap : (tr.state (n + 1)).capability
        = (tr.state n).capability + (tr.input n).eff.growGain := by
      rw [hstep]; exact advance_capability _ _
    have h1p : 0 ≤ 1 + alpha := by linarith
    have hmul : (1 + alpha) ^ n * (1 + alpha) * (tr.state 0).capability
        ≤ (1 + alpha) * (tr.state n).capability := by
      have hih := ih (by omega)
      have hII : (1 + alpha) ^ n * (tr.state 0).capability * (1 + alpha)
          ≤ (tr.state n).capability * (1 + alpha) :=
        mul_le_mul_of_nonneg_right hih h1p
      have hI2 : (1 + alpha) ^ n * (1 + alpha) * (tr.state 0).capability
          = (1 + alpha) ^ n * (tr.state 0).capability * (1 + alpha) := by
        ring
      rw [hI2, mul_comm (1 + alpha) (tr.state n).capability]
      exact hII
    have hr2 : (1 + alpha) * (tr.state n).capability
        = (tr.state n).capability
          + alpha * (tr.state n).capability := by ring
    calc (1 + alpha) ^ (n + 1) * (tr.state 0).capability
        = (1 + alpha) ^ n * (1 + alpha) * (tr.state 0).capability := by ring
      _ ≤ (1 + alpha) * (tr.state n).capability := hmul
      _ ≤ (tr.state n).capability + (tr.input n).eff.growGain := by
          rw [hr2]; linarith [hg]
      _ = (tr.state (n + 1)).capability := by rw [hcap]

/-- **Telescope of certified per-cycle drops**: if every cycle of a
trajectory certifies an energy drop of at least `d0 >= 0` over the
FRESH measurement (`advance_energy_drop` saturated by `d0`), then
`(state t).energy <= (state 0).energy - t * d0` — a multi-cycle
progress certificate (impossible under the fixed-effects model,
where two cycles already force the certificate nonpositive,
`corePremises_two_step_decrease_nonpos`). -/
theorem trajectory_energy_telescope (tr : Trajectory X) (d0 : ℝ)
    (hd0 : 0 ≤ d0)
    (hdrop : ∀ t < tr.T,
      (tr.input t).eff.compressEnergy
        ≤ (tr.state t).energy - d0)
    (t : ℕ) (ht : t ≤ tr.T) :
    (tr.state t).energy ≤ (tr.state 0).energy - (t : ℝ) * d0 := by
  induction t with
  | zero => simp
  | succ n ih =>
    have hn : n ≤ tr.T := by omega
    have hstep := tr.h_step n (by omega)
    have hd := hdrop n (by omega)
    have hE : (tr.state (n + 1)).energy
        = (tr.input n).eff.compressEnergy := by
      rw [hstep]; exact advance_energy _ _
    have hprev := ih hn
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
    calc (tr.state (n + 1)).energy
        = (tr.input n).eff.compressEnergy := hE
      _ ≤ (tr.state n).energy - d0 := hd
      _ ≤ (tr.state 0).energy - (n : ℝ) * d0 - d0 := by
          linarith [hprev]
      _ = (tr.state 0).energy - ((n + 1 : ℕ) : ℝ) * d0 := by
          rw [hcast]; linarith [hd0]

/-! ### Unification: the old certificate is dominated by the cycle drop -/

/-- **Certificate domination (old → new bridge)**: one full
per-cycle drop (the `advance_energy_drop` bracket) dominates the
old `System.verify` certificate `growGain + gap + eta*||d||^2/2 -
kappa*s/2` whenever the SafeQP window holds (`eta <= 1/L`,
`||d||^2 <= <grad,d>`): the window saturates
`L*eta^2*||d||^2 <= eta*||d||^2` and the cone gives
`eta*||d||^2 <= eta*<grad,d>` — the same squeeze that forced the
two-cycle obstruction, now used constructively: the LEDGER of the
old model is a LOWER BOUND on the real per-cycle progress of the
repaired one. -/
theorem cycle_drop_ge_certificate (u : StageInput X)
    (hdesc : ‖u.stepDir‖ ^ 2 ≤ ⟪u.grad, u.stepDir⟫_ℝ)
    (heta : u.sp.eta ≤ 1 / u.sp.L)
    (hL : 0 < u.sp.L) :
    u.eff.growGain + u.gap
      + (u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
      ≥ u.eff.growGain + u.gap + u.sp.eta * ‖u.stepDir‖ ^ 2 / 2 := by
  set eta := u.sp.eta with hE
  set L := u.sp.L with hLE
  set N := ‖u.stepDir‖ ^ 2 with hN
  set I := ⟪u.grad, u.stepDir⟫_ℝ with hI
  have heta0 : 0 ≤ eta := le_trans (by linarith) (le_of_lt u.h_eta_pos)
  have hetaL : eta * L ≤ 1 := by
    calc eta * L ≤ (1 / L) * L := mul_le_mul_of_nonneg_right heta hL.le
      _ = 1 := by field_simp
  have hGN : 0 ≤ eta * N := mul_nonneg heta0 (sq_nonneg _)
  have h1a : eta * N ≤ eta * I := mul_le_mul_of_nonneg_left hdesc heta0
  have h1b : L * eta ^ 2 * N ≤ eta * N := by nlinarith [hetaL, hGN]
  linarith

/-! ### Unification: the witness realizes the amplification -/

/-- The three-cycle witness trajectory: states linked by
`advance` over the fresh inputs `wU0, wU1, wU2`. -/
noncomputable def wTraj : Trajectory ℝ where
  T := 3
  state := fun t =>
    if t = 0 then wS0
    else if t = 1 then advance wS0 wU0
    else if t = 2 then advance (advance wS0 wU0) wU1
    else advance (advance (advance wS0 wU0) wU1) wU2
  input := fun t =>
    if t = 0 then wU0 else if t = 1 then wU1 else wU2
  h_step := by
    intro t ht
    have ht3 : t < 3 := ht
    interval_cases t
    all_goals simp [advance]

/-- The amplification theorem instantiated on the witness: the
state-linked geometric takeoff `(1+1)^3 * 1 = 8` IS REALIZED —
the repaired semantics proves the capstone growth the OLD model
could only state vacuously (`MasterHAGI_linked` was inconsistent
at `T >= 2`). -/
theorem witness_takeoff_realized :
    (1 + (1:ℝ)) ^ 3 * (wTraj.state 0).capability
      ≤ (wTraj.state 3).capability := by
  have hα : 0 ≤ (1:ℝ) := by norm_num
  have hg : ∀ t < wTraj.T,
      (1:ℝ) * (wTraj.state t).capability
        ≤ (wTraj.input t).eff.growGain := by
    intro t ht
    have ht3 : t < 3 := ht
    interval_cases t
    all_goals simp [wTraj, advance, wS0, wU0, wU1, wU2]
    all_goals norm_num
  have hT : (3:ℕ) ≤ wTraj.T := by simp [wTraj]
  have hres := capability_takeoff_amplified wTraj (1:ℝ) hα hg 3 hT
  have hstate3 : wTraj.state 3
      = advance (advance (advance wS0 wU0) wU1) wU2 := by
    simp [wTraj]
  have hcap3 : (advance (advance (advance wS0 wU0) wU1) wU2).capability = 8 := by
    simp [advance, wS0, wU0, wU1, wU2]
    all_goals norm_num
  have hstate0 : wTraj.state 0 = wS0 := by simp [wTraj]
  rw [hstate0, hstate3, hcap3]
  have hcap0 : wS0.capability = 1 := by simp [wS0]
  rw [hcap0]
  norm_num

/-! ### Termination: the repaired model terminates on schedule -/

/-- **Termination bound for repaired trajectories** (unification
with the canonical Lyapunov machine): if every cycle certifies a
drop of at least `d0 > 0` and the energy never sinks below the
floor `Emin`, the whole horizon is budget-bounded:
`T <= (E_0 - Emin)/d0`. This is the multi-cycle generalization of
the one-cycle certificate arithmetic — under the OLD fixed-effects
model two consecutive cycles already forced the certified drop
nonpositive (`corePremises_two_step_decrease_nonpos`), so a
POSITIVE `d0` horizon was unsatisfiable; in the repaired semantics
it is realized (see `two_cycle_certified_descent`). Delegation
chain: `trajectory_energy_telescope` + energy floor +
`Hagi.Foundations.lyapunov_divides`-style arithmetic. -/
theorem trajectory_termination (tr : Trajectory X) (Emin d0 : ℝ)
    (hd0 : 0 < d0)
    (hdrop : ∀ t < tr.T,
      (tr.input t).eff.compressEnergy
        ≤ (tr.state t).energy - d0)
    (hfloor : ∀ t ≤ tr.T, Emin ≤ (tr.state t).energy) :
    (tr.T : ℝ) ≤ ((tr.state 0).energy - Emin) / d0 := by
  have htel := trajectory_energy_telescope tr d0 hd0.le hdrop tr.T
    (Nat.le_refl _)
  have hEk : Emin ≤ (tr.state tr.T).energy := hfloor tr.T (Nat.le_refl _)
  have hkey : (tr.state 0).energy - Emin ≥ (tr.T : ℝ) * d0 := by
    calc (tr.state 0).energy - Emin
        ≥ (tr.state 0).energy - (tr.state tr.T).energy := by
          linarith [hEk]
      _ ≥ (tr.T : ℝ) * d0 := by linarith [htel]
  exact (le_div_iff₀ hd0).mpr hkey

/-! ### Honest ledgers: typed nonnegativity drives bookkeeping -/

/-- **Budget never increases** (typed honesty): the compute spends
are nonnegative by the input's PROOF FIELDS
(`StageInput.h_costs_nn`), so the budget ledger strictly follows
the spends — an advance can only burn, never mint, budget. -/
theorem advance_budget_le (S : GrowthState X) (u : StageInput X) :
    (advance S u).budget ≤ S.budget := by
  have h1 : (0:ℝ) ≤ u.eff.growCost + u.eff.mergeCost
      + u.eff.jointCost + u.eff.compressCost := by
    obtain ⟨h1, h2, h3, h4⟩ := u.h_costs_nn
    linarith
  have hE : (advance S u).budget
      = S.budget - (u.eff.growCost + u.eff.mergeCost
          + u.eff.jointCost + u.eff.compressCost) := by
    simp only [advance]; ring
  linarith

/-- **Protected risk never decreases** (typed honesty): the risk
spends are nonnegative by `StageInput.h_risks_nn`, so the
protected-domain ledger only accrues. -/
theorem advance_risk_ge (S : GrowthState X) (u : StageInput X) :
    S.protectedRisk ≤ (advance S u).protectedRisk := by
  have h1 : (0:ℝ) ≤ u.eff.growRisk + u.eff.mergeRisk
      + u.eff.jointRisk + u.eff.compressRisk := by
    obtain ⟨h1, h2, h3, h4⟩ := u.h_risks_nn
    linarith
  have hE : (advance S u).protectedRisk
      = S.protectedRisk + (u.eff.growRisk + u.eff.mergeRisk
        + u.eff.jointRisk + u.eff.compressRisk) := by
    simp [advance]; ring
  linarith

/-- **Ledger monotonicity along a trajectory** (unification of the
typed nonnegativity with multi-cycle bookkeeping): over any run,
the budget never grows and the protected risk never shrinks. -/
theorem trajectory_ledgers_monotone (tr : Trajectory X) (t : ℕ)
    (ht : t ≤ tr.T) :
    (tr.state t).budget ≤ (tr.state 0).budget
    ∧ (tr.state 0).protectedRisk ≤ (tr.state t).protectedRisk := by
  induction t with
  | zero => simp
  | succ n ih =>
    have hn : n ≤ tr.T := by omega
    obtain ⟨hb, hr⟩ := ih hn
    have hstep := tr.h_step n (by omega)
    constructor
    · rw [hstep]
      exact le_trans (advance_budget_le _ _) hb
    · rw [hstep]
      exact le_trans hr (advance_risk_ge _ _)

/-- Привязка измерений цикла: копирует свежие поля `u`
(направление, градиент, параметры этапа, зазор, эффекты) в
состояние, не меняя накопленные величины. -/
def prepare (S : GrowthState X) (u : StageInput X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts
  energy := S.energy
  protectedRisk := S.protectedRisk
  budget := S.budget
  gap := u.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := u.stepDir
  grad := u.grad
  sp := u.sp
  effects := u.eff

/-- ЕДИНАЯ СЕМАНТИКА: `advance` — это в точности
последовательность четырёх операторов одного цикла
(grow → merge → joint → compress) после привязки измерений. -/
theorem advance_decompose (S : GrowthState X) (u : StageInput X) :
    advance S u = compress (joint (merge (grow (prepare S u)))) := by
  rfl

end Hagi.Model
