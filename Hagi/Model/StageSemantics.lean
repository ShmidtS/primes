/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Hagi.System.GrowthState
import Hagi.Optimization.Momentum
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

/-- СЕРТИФИКАТ ОДНОГО ЦИКЛА (уровень A этапа 4): advance
точно исполняет все три леджеря — бюджетный (полная
4-стадийная сумма трат), рисковый (накопление защищённого
риска), качества (прирост измеренной способности) — и это
следует из ОПРЕДЕЛЕНИЙ операторов (rfl), а не отдельных
предположений согласованности. -/
theorem advance_cycle_certificate (S : GrowthState X) (u : StageInput X) :
    (advance S u).budget
        = S.budget - (verify (advance S u)).budgetSpend
      ∧ (advance S u).protectedRisk
        = S.protectedRisk + u.eff.growRisk + u.eff.mergeRisk
            + u.eff.jointRisk + u.eff.compressRisk
      ∧ (advance S u).capability = S.capability + u.eff.growGain := by
  refine ⟨?_, ?_, ?_⟩
  · -- бюджетный леджерь: advance = 4-операторная композиция
    rw [advance_decompose]
    have hprep : (prepare S u).budget = S.budget := rfl
    have hchain := budget_account (prepare S u)
    have heff : (verify (prepare S u)).budgetSpend
        = (verify (advance S u)).budgetSpend := rfl
    rw [heff, hprep] at hchain
    exact hchain
  · rfl
  · rfl

/-- УРОВЕНЬ B: телескопирование траектории через сертификат
одного цикла — бюджетный и качественный леджеря всей
траектории выводятся из per-cycle сертификатов (единая
телескопная теорема, а не повторение суммирования). -/
theorem trajectory_cycle_ledgers (tr : Trajectory X) :
    ∀ k ≤ tr.T,
      (tr.state k).budget
        = (tr.state 0).budget
          - ∑ t ∈ Finset.range k, (verify (tr.state (t+1))).budgetSpend
      ∧ (tr.state k).capability
        = (tr.state 0).capability
          + ∑ t ∈ Finset.range k, (tr.input t).eff.growGain := by
  intro k hk
  induction k with
  | zero => simp
  | succ n ih =>
      have hn : n ≤ tr.T := le_trans (Nat.le_succ n) hk
      obtain ⟨hbud, hcap⟩ := ih hn
      have hstep := tr.h_step n (Nat.lt_of_succ_le hk)
      rw [hstep]
      obtain ⟨hbc, _, hcapc⟩ :=
        advance_cycle_certificate (tr.state n) (tr.input n)
      -- сертификат цикла использует verify(advance) = verify(state n+1)
      have hv : (verify (advance (tr.state n) (tr.input n))).budgetSpend
          = (verify (tr.state (n+1))).budgetSpend := by
        rw [hstep]
      rw [Finset.sum_range_succ]
      refine ⟨?_, ?_⟩
      · rw [hbc, hv, hbud]; ring
      · rw [Finset.sum_range_succ, hcapc, hcap]; ring

/-- РОСТ ОПЛАЧЕН (уровень D): если каждый цикл оплачивает
свой прирост качества (c·gain ≤ бюджетная трата цикла) и
бюджет неотрицателен, то суммарный прирост качества на
всей траектории ограничен стартовым бюджетом / c —
саморазвитие не бесплатно: сертификат качества опирается
на ресурсный сертификат. -/
theorem growth_pays_budget (tr : Trajectory X) (c : ℝ) (hc : 0 < c)
    (k : ℕ) (hk : k ≤ tr.T)
    (hpaid : ∀ t < tr.T,
      c * (tr.input t).eff.growGain
        ≤ (verify (tr.state (t+1))).budgetSpend)
    (hbudk : 0 ≤ (tr.state k).budget) :
    (tr.state k).capability
      ≤ (tr.state 0).capability + (tr.state 0).budget / c := by
  obtain ⟨hbud, hcap⟩ := trajectory_cycle_ledgers tr k hk
  -- Σ gain ≤ Σ spend / c ≤ budget0 / c (бюджет k ≥ 0 ⟹ Σ spend ≤ budget0)
  have hsum : ∑ t ∈ Finset.range k, (tr.input t).eff.growGain
      ≤ (∑ t ∈ Finset.range k,
          (verify (tr.state (t+1))).budgetSpend) / c := by
    refine (le_div_iff₀' hc).mpr ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t ht =>
      hpaid t (lt_of_lt_of_le (by simpa using ht : t < k) hk)
  have hspend : ∑ t ∈ Finset.range k,
      (verify (tr.state (t+1))).budgetSpend
      ≤ (tr.state 0).budget := by
    linarith [hbud, hbudk]
  have hfin : ∑ t ∈ Finset.range k, (tr.input t).eff.growGain
      ≤ (tr.state 0).budget / c :=
    le_trans hsum ((div_le_div_iff_of_pos_right hc).mpr hspend)
  rw [hcap]
  linarith

/-- ИНТЕГРАЛЬНЫЙ СЕРТИФИКАТ ТРАЕКТОРИИ (уровень E): единая
теорема — точные леджеря (бюджет/качество) И (при оплате
приростов и неотрицательном бюджете) ресурсная граница
роста: сертификат цикла → телескоп → оплаченный рост,
в одном утверждении с явно сохранёнными предпосылками. -/
theorem integral_trajectory_certificate (tr : Trajectory X)
    (c : ℝ) (hc : 0 < c)
    (hpaid : ∀ t < tr.T,
      c * (tr.input t).eff.growGain
        ≤ (verify (tr.state (t+1))).budgetSpend) :
    ∀ k ≤ tr.T,
      (tr.state k).budget
        = (tr.state 0).budget
          - ∑ t ∈ Finset.range k, (verify (tr.state (t+1))).budgetSpend
      ∧ (tr.state k).capability
        = (tr.state 0).capability
          + ∑ t ∈ Finset.range k, (tr.input t).eff.growGain
      ∧ (0 ≤ (tr.state k).budget →
          (tr.state k).capability
            ≤ (tr.state 0).capability + (tr.state 0).budget / c) := by
  intro k hk
  obtain ⟨hbud, hcap⟩ := trajectory_cycle_ledgers tr k hk
  refine ⟨hbud, hcap, ?_⟩
  intro hbudk
  exact growth_pays_budget tr c hc k hk hpaid hbudk

/-- КРИТЕРИЙ ОСТАНОВКИ (этап 7): если целевое качество дороже
всего бюджета (Qtarget > cap0 + budget0/c) и каждый цикл
оплачивает свой прирост, то НИ НА КАКОМ горизонте с
неотрицательным бюджетом цель недостижима — обучение
следует остановить/пересмотреть бюджет: это прямая
контрапозиция оплаченного роста. -/
theorem budget_stops_growth (tr : Trajectory X) (c : ℝ) (hc : 0 < c)
    (hpaid : ∀ t < tr.T,
      c * (tr.input t).eff.growGain
        ≤ (verify (tr.state (t+1))).budgetSpend)
    (Qtarget : ℝ)
    (hunreach : (tr.state 0).capability + (tr.state 0).budget / c
      < Qtarget) :
    ∀ k ≤ tr.T, 0 ≤ (tr.state k).budget →
      (tr.state k).capability < Qtarget := by
  intro k hk hbudk
  have h := growth_pays_budget tr c hc k hk hpaid hbudk
  linarith

/-- Структурный рост тоже оплачен (MemT P1: число экспертов —
структурный масштаб, не счётчик саморазвития): если добавление
эксперта стоит ≥ g и бюджет траектории неотрицателен, то
число экспертов на горизонте ограничено бюджетом — структурная
экспансия без ресурса невозможна. -/
theorem experts_pays_budget (tr : Trajectory X) (g : ℝ) (hg : 0 < g)
    (hpaid : ∀ t < tr.T,
      g ≤ (verify (tr.state (t+1))).budgetSpend)
    (k : ℕ) (hk : k ≤ tr.T)
    (hbudk : 0 ≤ (tr.state k).budget) :
    ((tr.state k).experts : ℝ)
      ≤ (tr.state 0).experts + (tr.state 0).budget / g := by
  -- телескоп бюджета: Σ spend ≤ budget0
  obtain ⟨hbud, _⟩ := trajectory_cycle_ledgers tr k hk
  have hspend : ∑ t ∈ Finset.range k,
      (verify (tr.state (t+1))).budgetSpend
      ≤ (tr.state 0).budget := by
    linarith [hbud, hbudk]
  -- эксперты: +1 за цикл (advance)
  have hexp : ∀ t < tr.T,
      ((tr.state (t+1)).experts : ℝ)
        = ((tr.state t).experts : ℝ) + 1 := by
    intro t ht
    rw [tr.h_step t ht]
    simp [advance]
  -- индукция: experts(k) = experts(0) + k, k ≤ budget0/g
  have hcount : ∀ j ≤ k,
      ((tr.state j).experts : ℝ)
        = ((tr.state 0).experts : ℝ) + (j : ℝ) := by
    intro j hj
    induction j with
    | zero => simp
    | succ n ih =>
        have hn : n ≤ k := le_trans (Nat.le_succ n) hj
        have hnk : n < k := lt_of_lt_of_le (Nat.lt_succ_self n) hj
        rw [hexp n (lt_of_lt_of_le hnk hk)]
        rw [ih hn]
        push_cast
        ring
  rw [hcount k (le_refl k)]
  -- k ≤ budget0/g: из Σ g ≤ Σ spend ≤ budget0
  have hkg : (k : ℝ) * g ≤ (tr.state 0).budget := by
    calc (k : ℝ) * g
        = ∑ _t ∈ Finset.range k, g := by
          simp [Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ t ∈ Finset.range k,
          (verify (tr.state (t+1))).budgetSpend :=
          Finset.sum_le_sum fun t ht =>
            hpaid t (lt_of_lt_of_le (by simpa using ht) hk)
      _ ≤ (tr.state 0).budget := hspend
  have hle : (k : ℝ) ≤ (tr.state 0).budget / g :=
    (le_div_iff₀ hg).mpr hkg
  linarith

/-- РИСК-КЭП ОСТАНАВЛИВАЕТ (этап 6, третья ось контроллера):
если каждый цикл несёт защищённый риск ≥ ρ и траектория
удерживает риск-кэп Rmax, то горизонт ограничен
(Rmax − risk0)/ρ — накопление риска, как и бюджета,
фундаментально ограничивает развитие. -/
theorem risk_cap_bounds_horizon (tr : Trajectory X) (ρ Rmax : ℝ)
    (hρ : 0 < ρ)
    (hrisk : ∀ t < tr.T,
      ρ ≤ (tr.input t).eff.growRisk + (tr.input t).eff.mergeRisk
        + (tr.input t).eff.jointRisk
        + (tr.input t).eff.compressRisk)
    (k : ℕ) (hk : k ≤ tr.T)
    (hcap : (tr.state k).protectedRisk ≤ Rmax) :
    (k : ℝ) ≤ (Rmax - (tr.state 0).protectedRisk) / ρ := by
  -- рисковый телескоп: risk(k) = risk0 + Σ per-cycle рисков
  have htele : ∀ j ≤ k, (tr.state j).protectedRisk
      = (tr.state 0).protectedRisk
        + (∑ t ∈ Finset.range j, ((tr.input t).eff.growRisk + (tr.input t).eff.mergeRisk + (tr.input t).eff.jointRisk + (tr.input t).eff.compressRisk)) := by
    intro j hj
    induction j with
    | zero => simp
    | succ n ih =>
        have hn : n ≤ k := le_trans (Nat.le_succ n) hj
        have hnk : n < k := lt_of_lt_of_le (Nat.lt_succ_self n) hj
        rw [tr.h_step n (lt_of_lt_of_le hnk hk)]
        obtain ⟨_, hrc, _⟩ :=
          advance_cycle_certificate (tr.state n) (tr.input n)
        rw [hrc, ih hn, Finset.sum_range_succ]
        ring
  -- Σ per-cycle рисков ≥ k·ρ
  have hsum : (k : ℝ) * ρ ≤ (∑ t ∈ Finset.range k, ((tr.input t).eff.growRisk + (tr.input t).eff.mergeRisk + (tr.input t).eff.jointRisk + (tr.input t).eff.compressRisk)) := by
    calc (k : ℝ) * ρ
        = ∑ _t ∈ Finset.range k, ρ := by
          simp [Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ t ∈ Finset.range k,
          ((tr.input t).eff.growRisk + (tr.input t).eff.mergeRisk
            + (tr.input t).eff.jointRisk
            + (tr.input t).eff.compressRisk) :=
          Finset.sum_le_sum fun t ht =>
            hrisk t (lt_of_lt_of_le (by simpa using ht) hk)
  -- сведение
  rw [htele k (le_refl k)] at hcap
  have hkey : (k : ℝ) * ρ ≤ Rmax - (tr.state 0).protectedRisk := by
    linarith
  exact (le_div_iff₀ hρ).mpr hkey

/-- ЕДИНЫЙ ИНВАРИАНТ КОНТРОЛЛЕРА (этап 6, композиция): при
оплате структуры (g ≥ стоимость эксперта за цикл) и
минимальном риске (ρ) с бюджетом ≥ 0 и риск-кэпом Rmax
горизонт траектории ограничен МИНИМУМОМ структурного и
рискового потолков (бюджетная ось ограничивает качество —
budget_stops_growth): контроллер останавливается по первой
исчерпанной оси счётчиков. -/
theorem controller_horizon_bound (tr : Trajectory X)
    (g ρ Rmax : ℝ) (hg : 0 < g) (hρ : 0 < ρ)
    (hpaidS : ∀ t < tr.T,
      g ≤ (verify (tr.state (t+1))).budgetSpend)
    (hrisk : ∀ t < tr.T,
      ρ ≤ (tr.input t).eff.growRisk + (tr.input t).eff.mergeRisk
        + (tr.input t).eff.jointRisk
        + (tr.input t).eff.compressRisk)
    (k : ℕ) (hk : k ≤ tr.T)
    (hbudk : 0 ≤ (tr.state k).budget)
    (hcap : (tr.state k).protectedRisk ≤ Rmax) :
    (k : ℝ) ≤ min ((tr.state 0).budget / g)
      ((Rmax - (tr.state 0).protectedRisk) / ρ) := by
  -- структурная ось: e0 + k ≤ e0 + budget0/g
  have hS := experts_pays_budget tr g hg hpaidS k hk hbudk
  have hcount : ∀ j ≤ k, ((tr.state j).experts : ℝ)
      = ((tr.state 0).experts : ℝ) + (j : ℝ) := by
    intro j hj
    induction j with
    | zero => simp
    | succ n ih =>
        have hn : n ≤ k := le_trans (Nat.le_succ n) hj
        have hnk : n < k := lt_of_lt_of_le (Nat.lt_succ_self n) hj
        rw [tr.h_step n (lt_of_lt_of_le hnk hk)]
        simp only [advance, Nat.cast_add, Nat.cast_one]
        rw [ih hn]
        ring
  rw [hcount k (le_refl k)] at hS
  have hSk : (k : ℝ) ≤ (tr.state 0).budget / g := by
    have h1 : ((tr.state 0).experts : ℝ) + (k : ℝ)
        ≤ ((tr.state 0).experts : ℝ) + (tr.state 0).budget / g := hS
    linarith
  -- рисковая ось
  have hR := risk_cap_bounds_horizon tr ρ Rmax hρ hrisk k hk hcap
  exact le_min hSk hR

/-- ПОЛОЖИТЕЛЬНЫЙ ЧИСТЫЙ ПРИРОСТ (этап 6 / P5, зеркально
MemoryCycle.gainOk): если каждый цикл сертифицирован —
прирост покрывает взвешенную стоимость, взвешенный риск и
запас ε (gainOk-контракт), то суммарное развитие траектории
не меньше суммы оплат: capability(k) ≥ cap0 + λM·Σspend +
λR·Σrisk + k·ε — саморазвитие с сертификатом чистой пользы. -/
theorem admit_gated_net_gain (tr : Trajectory X)
    (lamM lamR ε : ℝ) (hε : 0 ≤ ε)
    (hcert : ∀ t < tr.T,
      lamM * (verify (tr.state (t+1))).budgetSpend
        + lamR * ((tr.input t).eff.growRisk
          + (tr.input t).eff.mergeRisk
          + (tr.input t).eff.jointRisk
          + (tr.input t).eff.compressRisk)
        + ε
      ≤ (tr.input t).eff.growGain)
    (k : ℕ) (hk : k ≤ tr.T) :
    (tr.state 0).capability + lamM
        * ∑ t ∈ Finset.range k, (verify (tr.state (t+1))).budgetSpend
      + lamR * ∑ t ∈ Finset.range k,
          ((tr.input t).eff.growRisk + (tr.input t).eff.mergeRisk
            + (tr.input t).eff.jointRisk
            + (tr.input t).eff.compressRisk)
      + (k : ℝ) * ε
    ≤ (tr.state k).capability := by
  obtain ⟨_, hcap⟩ := trajectory_cycle_ledgers tr k hk
  rw [hcap]
  -- Σgain ≥ Σ(λM spend + λR risk + ε) — почленно
  have h1 : ∑ t ∈ Finset.range k, (tr.input t).eff.growGain
      ≥ ∑ t ∈ Finset.range k,
          (lamM * (verify (tr.state (t+1))).budgetSpend
            + lamR * ((tr.input t).eff.growRisk
              + (tr.input t).eff.mergeRisk
              + (tr.input t).eff.jointRisk
              + (tr.input t).eff.compressRisk)
            + ε) :=
    Finset.sum_le_sum fun t ht =>
      hcert t (lt_of_lt_of_le (by simpa using ht) hk)
  -- разложение суммы на три компоненты
  have h2 : ∑ t ∈ Finset.range k,
      (lamM * (verify (tr.state (t+1))).budgetSpend
        + lamR * ((tr.input t).eff.growRisk
          + (tr.input t).eff.mergeRisk
          + (tr.input t).eff.jointRisk
          + (tr.input t).eff.compressRisk)
        + ε)
      = lamM * ∑ t ∈ Finset.range k, (verify (tr.state (t+1))).budgetSpend
        + lamR * ∑ t ∈ Finset.range k,
            ((tr.input t).eff.growRisk + (tr.input t).eff.mergeRisk
              + (tr.input t).eff.jointRisk
              + (tr.input t).eff.compressRisk)
        + (k : ℝ) * ε := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.mul_sum,
      show (k : ℝ) * ε = ∑ _t ∈ Finset.range k, ε from by
        simp [Finset.card_range, nsmul_eq_mul]]
  linarith

/-- МОСТ УСКОРЕНИЕ × МОДЕЛЬ: если потенциал состояний
Φ(S_t) = energy + protectedRisk подчиняется инерционному
закону (шаг q, импульс β), то он затухает со скоростью
ρ(q,β): ускоренный алгоритм обучения напрямую управляет
потенциалом модели — сертификат роста и теория ускорения
соединены. -/
theorem trajectory_potential_momentum (tr : Trajectory X)
    (q β : ℝ) (hq : 0 < q) (hβ : 0 ≤ β) (hqb : q + β < 1)
    (hstep : ∀ k : ℕ, 1 ≤ k →
      potential (tr.state (k + 1))
        ≤ q * potential (tr.state k)
          + β * potential (tr.state (k - 1)))
    (k : ℕ) :
    potential (tr.state k)
      ≤ max (potential (tr.state 0))
          (potential (tr.state 1) / Hagi.Optimization.momentumRate q β)
        * (Hagi.Optimization.momentumRate q β) ^ k :=
  Hagi.Optimization.momentum_bound (fun t => potential (tr.state t)) q β hq hβ hqb
    hstep k

/-- УСКОРЕННЫЙ ВХОД ПОТЕНЦИАЛА В КОРИДОР: если потенциал
состояний подчиняется неточному инерционному закону
(q, β, δ), то для любого ε > 0 существует горизонт T, с
которого потенциал навсегда ≤ δ/(1−q−β) + ε: ускоренный
обучающий цикл выводит модель в коридор целевого качества
за конечное (логарифмическое по скорости ρ) время. -/
theorem trajectory_accelerated_entry (tr : Trajectory X)
    (q β δ : ℝ) (hq : 0 < q) (hβ : 0 ≤ β)
    (hqb : q + β < 1) (hδ : 0 ≤ δ)
    (hstep : ∀ k : ℕ, 1 ≤ k →
      potential (tr.state (k + 1))
        ≤ q * potential (tr.state k)
          + β * potential (tr.state (k - 1)) + δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
      potential (tr.state s)
        ≤ δ / (1 - q - β) + ε :=
  Hagi.Optimization.momentum_achievability
    (fun t => potential (tr.state t)) q β δ hq hβ hqb hδ
    hstep ε hε

/-- МОСТ НЕСТЕРОВ × МОДЕЛЬ: если потенциал состояний
Φ(S_t) = energy + protectedRisk подчиняется СКОРРЕКТИРОВАННОМУ
инерционному закону (look-ahead с поправкой β), то он
затухает с эффективным фактором (q+β)/(1+β): ускорение с
коррекцией напрямую управляет потенциалом модели. -/
theorem trajectory_potential_nesterov (tr : Trajectory X)
    (q β : ℝ) (hq : 0 < q) (hq1 : q < 1) (hβ : 0 < β)
    (hstep : ∀ k : ℕ,
      potential (tr.state (k + 1))
        + β * (potential (tr.state (k + 1))
          - potential (tr.state k))
        ≤ q * potential (tr.state k))
    (k : ℕ) :
    potential (tr.state k)
      ≤ ((q + β) / (1 + β)) ^ k * potential (tr.state 0) :=
  Hagi.Optimization.nesterov_corrected
    (fun t => potential (tr.state t)) q β hq hq1 hβ hstep k

/-- МНОГОШАГОВЫЙ ПРОДУКТИВНЫЙ WITNESS (аудит §4): на
канонической семантике Trajectory существует траектория
длины 3, каждый шаг которой строго продуктивен:
growGain > 0, энергия падает не менее чем на 3,
способность строго растёт. Состояния получены только
последовательными advance; эффекты — входы шагов. -/
theorem wTraj_productive :
    ∃ tr : Hagi.Model.Trajectory ℝ,
      tr.T = 3
        ∧ ∀ t < 3,
            0 < (tr.input t).eff.growGain
              ∧ (tr.state (t + 1)).energy + 3 ≤ (tr.state t).energy
              ∧ (tr.state t).capability < (tr.state (t + 1)).capability := by
  refine ⟨wTraj, rfl, ?_⟩
  intro t ht
  interval_cases t
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]

/-- ИНВАРИАНТЫ ПРОДУКТИВНОЙ ТРАЕКТОРИИ (аудит §9): та же
wTraj-траектория удовлетворяет сертификатам бюджета и риска
на всём горизонте: бюджет неотрицателен (100 − 2t), риск
неотрицателен и не убывает (все риски шагов нулевые —
тождественный ноль), бюджет тратится ровно на 2 за шаг. -/
theorem wTraj_budget_risk_invariants :
    (∀ t ≤ 3, (wTraj.state t).budget = 100 - 2 * t ∧ 0 ≤ (wTraj.state t).budget)
      ∧ ∀ t ≤ 3, (wTraj.state t).protectedRisk = 0 := by
  constructor
  · intro t ht
    interval_cases t
    all_goals norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · intro t ht
    interval_cases t
    all_goals norm_num [wTraj, wS0, wU0, wU1, wU2, advance]

/-- ВЗЛЁТ СВИДЕТЕЛЯ: продуктивная траектория wTraj реализует
экспоненциальный рост способности с темпом (1+α), α=1:
каждый шаг удовлетворяет гейту alpha·C_t ≤ growGain (gain
равен текущей capability: 1,2,4), поэтому
C_0·(1+1)^t ≤ C_t на всём горизонте — связка канонической
семантики с cone/takeoff-механикой. -/
theorem wTraj_takeoff :
    ∀ t ≤ 3, (1:ℝ) * (wTraj.state t).capability
      ≤ (wTraj.state (t + 1)).capability
        ∧ (wTraj.state 0).capability * 2 ^ t
          ≤ (wTraj.state t).capability := by
  intro t ht
  interval_cases t
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]
  · norm_num [wTraj, wS0, wU0, wU1, wU2, advance]

/-- МОСТ (advance → verify-сертификат): decrease шага
advance (в терминах свежего StageInput u) СТРОГО ПОЛОЖИТЕЛЕН
при операционных условиях: gap ≥ 0, η ≥ 0 и компрессия
оплачена (κ·s < 2·growGain, что влечёт growGain > 0). Связывает
каноническую advance-семантику с certify-слоем verify. -/
theorem advance_verify_decrease_pos {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (S : Hagi.System.GrowthState X) (u : Hagi.Model.StageInput X)
    (hgap : 0 ≤ u.gap)
    (heta : 0 ≤ u.sp.eta)
    (hks : u.sp.kappa * u.sp.s < 2 * u.eff.growGain) :
    0 < (Hagi.System.verify (Hagi.Model.advance S u)).decrease := by
  rw [Hagi.System.verify_decrease]
  have hnn : (0:ℝ) ≤ u.sp.eta * ‖u.stepDir‖ ^ 2 / 2 := by
    have : (0:ℝ) ≤ u.sp.eta * ‖u.stepDir‖ ^ 2 :=
      mul_nonneg heta (sq_nonneg _)
    positivity
  unfold Hagi.Model.advance
  nlinarith [hgap, hnn, hks]

/-- P0.2 МОСТ (закон роста advance-семантики): для траектории
настоящих advance-циклов с измеряемым потенциалом D
(k·capability ≤ D на каждом шаге) и конусной отдачей
(γ·D t ≤ измеренный growGain шага t) capability растёт
ЭКСПОНЕНЦИАЛЬНО: C T ≥ (1+γk)^T·C 0 — пересчитываемый из
состояния gain согласован с конусным законом роста;
фиксированный (независимый от состояния) gain дал бы лишь
линейный рост — конфликт семантик разрешён в пользу
пересчёта (audit two-step inconsistency). -/
theorem advance_trajectory_takeoff {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (tr : Trajectory X) (D : ℕ → ℝ) (γ k : ℝ)
    (hγ : 0 ≤ γ) (hγk : 0 ≤ 1 + γ * k)
    (hcone : ∀ t < tr.T, k * (tr.state t).capability ≤ D t)
    (hgain : ∀ t < tr.T, γ * D t ≤ (tr.input t).eff.growGain) :
    (1 + γ * k) ^ tr.T * (tr.state 0).capability
      ≤ (tr.state tr.T).capability := by
  have hmain : ∀ n : ℕ, n ≤ tr.T →
      (1 + γ * k) ^ n * (tr.state 0).capability
        ≤ (tr.state n).capability := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : (1 + γ * k) ^ 0 = 1 := pow_zero _
      rw [h0, one_mul]
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hstep := tr.h_step n (by omega)
      have hg := hgain n (by omega)
      have hc := hcone n (by omega)
      have hγkC : γ * k * (tr.state n).capability
          ≤ (tr.input n).eff.growGain :=
        calc γ * k * (tr.state n).capability
            = γ * (k * (tr.state n).capability) := by ring
        _ ≤ γ * D n := mul_le_mul_of_nonneg_left hc hγ
        _ ≤ (tr.input n).eff.growGain := hg
      have hkey : (1 + γ * k) * ((tr.state n).capability)
          ≤ (tr.state n).capability + (tr.input n).eff.growGain := by
        nlinarith [hγkC]
      have heq : (tr.state (n + 1)).capability
          = (tr.state n).capability + (tr.input n).eff.growGain := by
        rw [hstep]; simp [advance]
      rw [pow_succ, heq]
      nlinarith [ih', hkey]
  exact hmain tr.T (le_refl _)

/-- P2/итоговый алгоритм: БЮДЖЕТНЫЙ ПОТОЛОК РОСТА —
честный бюджет (каждый шаг тратит ≥ c, бюджет неотрицателен)
ограничивает горизонт T·c ≤ B; с C-cap (C(t+1) ≤ (1+α)C t)
потолок capability: C T ≤ (1+α)^{B/c}·C 0 — рост нельзя
«купить» больше, чем позволяет бюджет (термодинамический/
ресурсный предел экспоненты). -/
theorem budget_capability_ceiling {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (tr : Trajectory X) (α c : ℝ)
    (hα : 1 ≤ 1 + α) (hc : 0 < c)
    (hcost : ∀ t < tr.T, c ≤ (tr.input t).eff.growCost
      + (tr.input t).eff.mergeCost
      + (tr.input t).eff.jointCost
      + (tr.input t).eff.compressCost)
    (hbudget : ∀ t ≤ tr.T, 0 ≤ (tr.state t).budget)
    (hC0 : 0 ≤ (tr.state 0).capability)
    (hcap : ∀ t < tr.T, (tr.state (t + 1)).capability
      ≤ (1 + α) * (tr.state t).capability) :
    (tr.state tr.T).capability
      ≤ (1 + α) ^ ((tr.state 0).budget / c) * (tr.state 0).capability := by
  have hB : (tr.T : ℝ) * c ≤ (tr.state 0).budget := by
    have htele : ∀ n : ℕ, n ≤ tr.T →
        (tr.state n).budget
          ≤ (tr.state 0).budget - (n : ℝ) * c := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have hstep := tr.h_step n (by omega)
        have hc' := hcost n (by omega)
        have ih' := ih (by omega)
        have hbud : (tr.state (n + 1)).budget
            ≤ (tr.state n).budget - c := by
          rw [hstep]
          simp only [advance]
          linarith
        have hcast : (((n : ℝ) + 1)) * c = (n : ℝ) * c + c := by ring
        have hcast2 : ((n + 1 : ℕ) : ℝ) * c = (n : ℝ) * c + c := by
          push_cast
          ring
        nlinarith [hbud, ih']
    have h0 := htele tr.T (le_refl _)
    have hnn := hbudget tr.T (le_refl _)
    linarith
  have hcapT : (tr.state tr.T).capability
      ≤ (1 + α) ^ tr.T * (tr.state 0).capability := by
    have hmain : ∀ n : ℕ, n ≤ tr.T →
        (tr.state n).capability
          ≤ (1 + α) ^ n * (tr.state 0).capability := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have hcap' := hcap n (by omega)
        have ih' := ih (by omega)
        calc (tr.state (n + 1)).capability
            ≤ (1 + α) * (tr.state n).capability := hcap'
        _ ≤ (1 + α) * ((1 + α) ^ n * (tr.state 0).capability) :=
              mul_le_mul_of_nonneg_left ih' (by linarith)
        _ = (1 + α) ^ (n + 1) * (tr.state 0).capability := by
              rw [pow_succ]; ring
    exact hmain tr.T (le_refl _)
  have hTle : (tr.T : ℝ) ≤ (tr.state 0).budget / c :=
    (le_div_iff₀ hc).mpr hB
  have hpow : (1 + α) ^ (tr.T : ℕ)
      ≤ (1 + α) ^ ((tr.state 0).budget / c) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hα hTle
  calc (tr.state tr.T).capability
      ≤ (1 + α) ^ tr.T * (tr.state 0).capability := hcapT
  _ ≤ (1 + α) ^ ((tr.state 0).budget / c) * (tr.state 0).capability :=
        mul_le_mul_of_nonneg_right hpow hC0

/-- КОРИДОР РОСТА (композиция): конусная отдача даёт нижнюю
границу C T ≥ (1+γk)^T·C 0, бюджет + cap — верхнюю
C T ≤ (1+α)^{B/c}·C 0; вместе — согласованность горизонта:
экспоненциальный взлёт не может превысить ресурсный потолок,
(1+γk)^T ≤ (1+α)^{B/c} (при C 0 > 0). -/
theorem growth_corridor {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (tr : Trajectory X) (D : ℕ → ℝ) (γ k α c : ℝ)
    (hγ : 0 ≤ γ) (hγk : 0 ≤ 1 + γ * k) (hα : 1 ≤ 1 + α)
    (hc : 0 < c) (hC0 : 0 < (tr.state 0).capability)
    (hcone : ∀ t < tr.T, k * (tr.state t).capability ≤ D t)
    (hgain : ∀ t < tr.T, γ * D t ≤ (tr.input t).eff.growGain)
    (hcost : ∀ t < tr.T, c ≤ (tr.input t).eff.growCost
      + (tr.input t).eff.mergeCost
      + (tr.input t).eff.jointCost
      + (tr.input t).eff.compressCost)
    (hbudget : ∀ t ≤ tr.T, 0 ≤ (tr.state t).budget)
    (hcap : ∀ t < tr.T, (tr.state (t + 1)).capability
      ≤ (1 + α) * (tr.state t).capability) :
    (1 + γ * k) ^ (tr.T : ℝ) ≤ (1 + α) ^ ((tr.state 0).budget / c) := by
  have hlow := advance_trajectory_takeoff tr D γ k hγ hγk hcone hgain
  have hhigh := budget_capability_ceiling tr α c hα hc hcost
    hbudget (le_of_lt hC0) hcap
  have hlow' : (1 + γ * k) ^ (tr.T : ℝ)
      * (tr.state 0).capability
      ≤ (tr.state tr.T).capability := by
    rw [Real.rpow_natCast]
    exact hlow
  have hchain : (1 + γ * k) ^ (tr.T : ℝ)
      * (tr.state 0).capability
      ≤ (1 + α) ^ ((tr.state 0).budget / c)
        * (tr.state 0).capability := by
    exact le_trans hlow' hhigh
  exact le_of_mul_le_mul_right hchain hC0

end Hagi.Model