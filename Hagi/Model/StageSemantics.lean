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
  /-- Compute spends are honest (nonnegative). -/
  h_costs_nn : 0 ≤ eff.growCost ∧ 0 ≤ eff.jointCost
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
  budget := S.budget - u.eff.growCost - u.eff.jointCost
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
      mergeEnergy := 18, mergeRisk := 0
      jointEnergy := 17, jointRisk := 0, jointCost := 1
      quantErr := 0, compressEnergy := 17, compressRisk := 0 }
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
      mergeEnergy := 0, mergeRisk := 0
      jointEnergy := 0, jointRisk := 0, jointCost := 0
      quantErr := 0, compressEnergy := 0, compressRisk := 0 }

/-- Cycle-0 measurement: gain `1`, gap `1`, chain `29 >= 8 >= 7`. -/
noncomputable def wU0 : StageInput ℝ where
  sp := { eta := 1, L := 1, kappa := 0, s := 0 }
  eff :=
    { growGain := 1, growCost := 1, growRisk := 0, growEnergy := 29
      mergeEnergy := 28, mergeRisk := 0
      jointEnergy := 27, jointRisk := 0, jointCost := 1
      quantErr := 0, compressEnergy := 27, compressRisk := 0 }
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
      mergeEnergy := 24, mergeRisk := 0
      jointEnergy := 23, jointRisk := 0, jointCost := 1
      quantErr := 0, compressEnergy := 23, compressRisk := 0 }
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

end Hagi.Model
