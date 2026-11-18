/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.CertifiedTransition
import Hagi.Unified.LogitCert

/-!
# Scalar logit learning with measured state transitions

The only objective in this module is the scalar one-example loss
`logitCE w`. Its negative is used as the capability gauge on this
specific carrier; no claim about LLM capability or general neural-network
convergence is made. Every `StageInput` is computed from the current
parameter and the actual gradient successor. In particular, the
measured capability gain is the actual CE decrease, not an arbitrary
`alpha * capability` annotation. Arbitrary finite orbits preserve both
parameter-energy-capability equalities.

Budget `eta` is the same normalized model charge as in `logitStepCertExact'`.
It is not floating-point work, wall-clock time, or a physical energy
measurement. Nonnegative budgets require an explicit affordability
hypothesis. The total CE-derived gain is bounded by the initial loss.

Actual energy descent is proved directly by CE strict antitonicity.
The legacy `advance_energy_drop` and `ctv3_of_stageLaws` are deliberately
NOT used here: putting the same CE drop into the grow and joint channels
would count it twice. V3 certification instead uses
`ctv3_of_actualDescent`. There is no artificial quantization credit.
-/

namespace Hagi.Unified.LogitGrowth

open Hagi.Model Hagi.System

noncomputable def next (w eta : ℝ) : ℝ :=
  w + eta / (1 + Real.exp w)

noncomputable def measuredInput (w eta : ℝ) (heta : 0 < eta) : StageInput ℝ where
  sp := { eta := eta, L := 1, kappa := 0, s := 0 }
  eff := {
    growGain := logitCE w - logitCE (next w eta),
    growCost := eta,
    growRisk := 0,
    growEnergy := logitCE (next w eta),
    mergeEnergy := logitCE (next w eta),
    mergeRisk := 0,
    mergeCost := 0,
    jointEnergy := logitCE (next w eta),
    jointRisk := 0,
    jointCost := 0,
    quantErr := 0,
    compressEnergy := logitCE (next w eta),
    compressRisk := 0,
    compressCost := 0 }
  gap := 0
  stepDir := -1 / (1 + Real.exp w)
  grad := -1 / (1 + Real.exp w)
  h_costs_nn := ⟨heta.le, le_refl _, le_refl _, le_refl _⟩
  h_risks_nn := by norm_num
  h_eta_pos := heta

noncomputable def step (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta) :
    GrowthState ℝ :=
  advance S (measuredInput S.params eta heta)

def Consistent (S : GrowthState ℝ) : Prop :=
  S.energy = logitCE S.params ∧ S.capability = -logitCE S.params

noncomputable def initial (w budget : ℝ) : GrowthState ℝ where
  weightDim := 0
  weights := fun _ => 0
  params := w
  experts := 0
  energy := logitCE w
  protectedRisk := 0
  budget := budget
  gap := 0
  dataField := 0
  capability := -logitCE w
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := { eta := 1, L := 1, kappa := 0, s := 0 }
  effects :=
    { growGain := 0, growCost := 0, growRisk := 0, growEnergy := 0
      mergeEnergy := 0, mergeRisk := 0, mergeCost := 0
      jointEnergy := 0, jointRisk := 0, jointCost := 0
      quantErr := 0, compressEnergy := 0, compressRisk := 0, compressCost := 0 }

theorem initial_consistent (w budget : ℝ) : Consistent (initial w budget) :=
  ⟨rfl, rfl⟩

theorem measured_gain_pos (w eta : ℝ) (heta : 0 < eta) :
    0 < (measuredInput w eta heta).eff.growGain := by
  change 0 < logitCE w - logitCE (next w eta)
  exact sub_pos.mpr (Hagi.Unified.LogitCert.descent_step_strict w eta heta)

theorem step_params (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta) :
    (step S eta heta).params = next S.params eta := by
  change S.params - eta • (-1 / (1 + Real.exp S.params)) = next S.params eta
  simp only [smul_eq_mul, next]
  ring

theorem step_energy (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta) :
    (step S eta heta).energy = logitCE (next S.params eta) := rfl

theorem step_capability (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta)
    (hC : S.capability = -logitCE S.params) :
    (step S eta heta).capability = -logitCE (next S.params eta) := by
  change S.capability + (logitCE S.params - logitCE (next S.params eta))
    = -logitCE (next S.params eta)
  rw [hC]
  ring

theorem step_budget (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta) :
    (step S eta heta).budget = S.budget - eta := by
  change S.budget - eta - 0 - 0 - 0 = S.budget - eta
  ring

theorem step_strict_gain (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta) :
    S.capability < (step S eta heta).capability := by
  change S.capability < S.capability
    + (logitCE S.params - logitCE (next S.params eta))
  have hg := measured_gain_pos S.params eta heta
  change 0 < logitCE S.params - logitCE (next S.params eta) at hg
  linarith

theorem step_consistent (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta)
    (hS : Consistent S) : Consistent (step S eta heta) := by
  have hP := step_params S eta heta
  constructor
  · rw [hP]
    exact step_energy S eta heta
  · rw [hP]
    exact step_capability S eta heta hS.2

theorem step_actual_descent (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta)
    (hE : S.energy = logitCE S.params) :
    (step S eta heta).energy < S.energy := by
  calc
    (step S eta heta).energy = logitCE (next S.params eta) := step_energy S eta heta
    _ < logitCE S.params := Hagi.Unified.LogitCert.descent_step_strict S.params eta heta
    _ = S.energy := hE.symm

theorem step_certified (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta) :
    CertifiedTransition S (step S eta heta) (measuredInput S.params eta heta)
      ((measuredInput S.params eta heta).eff.growRisk
        + (measuredInput S.params eta heta).eff.mergeRisk
        + (measuredInput S.params eta heta).eff.jointRisk
        + (measuredInput S.params eta heta).eff.compressRisk) := by
  simpa [step, measuredInput] using
    certifiedTransition_of_advance S (measuredInput S.params eta heta)
      (by rfl) heta.le (by
        change 0 * 0 < 2 * (logitCE S.params - logitCE (next S.params eta))
        have hpos := mul_pos (by norm_num : (0:ℝ) < 2) (sub_pos.mpr
          (Hagi.Unified.LogitCert.descent_step_strict S.params eta heta))
        simpa only [next, zero_mul] using hpos)

theorem step_certified_v3 (S : GrowthState ℝ) (eta : ℝ) (heta : 0 < eta)
    (hS : Consistent S) :
    CertifiedTransitionV3 S (step S eta heta) (measuredInput S.params eta heta)
      ((measuredInput S.params eta heta).eff.growRisk
        + (measuredInput S.params eta heta).eff.mergeRisk
        + (measuredInput S.params eta heta).eff.jointRisk
        + (measuredInput S.params eta heta).eff.compressRisk) := by
  apply ctv3_of_actualDescent
  · refine ctv2_of_ct (step_certified S eta heta) ?_
    simp only [step, advance, measuredInput, add_zero, sub_self]
    exact le_refl 0
  · exact step_actual_descent S eta heta hS.1

noncomputable def orbit (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) : ℕ → GrowthState ℝ
  | 0 => S0
  | n + 1 => step (orbit S0 eta heta n) (eta n) (heta n)

noncomputable def trajectory (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) (T : ℕ) : Trajectory ℝ where
  T := T
  state := orbit S0 eta heta
  input := fun t => measuredInput (orbit S0 eta heta t).params (eta t) (heta t)
  h_step := fun _ _ => rfl

theorem orbit_consistent (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) (h0 : Consistent S0) (n : ℕ) :
    Consistent (orbit S0 eta heta n) := by
  induction n with
  | zero => exact h0
  | succ n ih => exact step_consistent _ _ _ ih

theorem orbit_step_certified (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) (T : ℕ) :
    ∀ t < T, CertifiedTransition (orbit S0 eta heta t)
      (orbit S0 eta heta (t + 1))
      (measuredInput (orbit S0 eta heta t).params (eta t) (heta t))
      ((measuredInput (orbit S0 eta heta t).params (eta t) (heta t)).eff.growRisk
        + (measuredInput (orbit S0 eta heta t).params (eta t) (heta t)).eff.mergeRisk
        + (measuredInput (orbit S0 eta heta t).params (eta t) (heta t)).eff.jointRisk
        + (measuredInput (orbit S0 eta heta t).params (eta t) (heta t)).eff.compressRisk) := by
  intro t _
  exact step_certified _ _ _

theorem orbit_step_v3 (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) (h0 : Consistent S0) (T : ℕ) :
    ∀ t < T, CertifiedTransitionV3 (orbit S0 eta heta t)
      (orbit S0 eta heta (t + 1))
      (measuredInput (orbit S0 eta heta t).params (eta t) (heta t))
      ((measuredInput (orbit S0 eta heta t).params (eta t) (heta t)).eff.growRisk
        + (measuredInput (orbit S0 eta heta t).params (eta t) (heta t)).eff.mergeRisk
        + (measuredInput (orbit S0 eta heta t).params (eta t) (heta t)).eff.jointRisk
        + (measuredInput (orbit S0 eta heta t).params (eta t) (heta t)).eff.compressRisk) := by
  intro t _
  exact step_certified_v3 _ _ _ (orbit_consistent S0 eta heta h0 t)

theorem orbit_budget (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) (T : ℕ) :
    (orbit S0 eta heta T).budget = S0.budget
      - ∑ t ∈ Finset.range T, eta t := by
  simpa only [orbit, measuredInput, add_zero, zero_add] using
    certified_trajectory_budget (orbit S0 eta heta)
      (fun t => measuredInput (orbit S0 eta heta t).params (eta t) (heta t))
      T (orbit_step_certified S0 eta heta T)

theorem orbit_capability (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) (T : ℕ) :
    (orbit S0 eta heta T).capability = S0.capability +
      ∑ t ∈ Finset.range T,
        (logitCE (orbit S0 eta heta t).params
          - logitCE (orbit S0 eta heta (t + 1)).params) := by
  have h := certified_trajectory_capability (orbit S0 eta heta)
      (fun t => measuredInput (orbit S0 eta heta t).params (eta t) (heta t))
      T (orbit_step_certified S0 eta heta T)
  have hsum : ∑ t ∈ Finset.range T,
      (measuredInput (orbit S0 eta heta t).params (eta t) (heta t)).eff.growGain
      = ∑ t ∈ Finset.range T,
        (logitCE (orbit S0 eta heta t).params
          - logitCE (orbit S0 eta heta (t + 1)).params) := by
    apply Finset.sum_congr rfl
    intro t _
    change logitCE (orbit S0 eta heta t).params
        - logitCE (next (orbit S0 eta heta t).params (eta t))
      = logitCE (orbit S0 eta heta t).params
        - logitCE (orbit S0 eta heta (t + 1)).params
    rw [← step_params (orbit S0 eta heta t) (eta t) (heta t)]
    rfl
  simpa only [orbit, hsum] using h

theorem orbit_strict (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) {n : ℕ} (hn : 0 < n) :
    S0.capability < (orbit S0 eta heta n).capability := by
  induction n with
  | zero => simp at hn
  | succ n ih =>
    have hstep := step_strict_gain (orbit S0 eta heta n) (eta n) (heta n)
    by_cases h0 : n = 0
    · subst n
      exact hstep
    · exact hstep.trans' (ih (Nat.pos_of_ne_zero h0))

theorem orbit_quality_bounded (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) (h0 : Consistent S0) (T : ℕ) :
    (orbit S0 eta heta T).capability - S0.capability ≤ logitCE S0.params := by
  have h0C := h0.2
  have hTC := (orbit_consistent S0 eta heta h0 T).2
  linarith [logitCE_nonneg (orbit S0 eta heta T).params]

theorem orbit_budget_nonneg (S0 : GrowthState ℝ) (eta : ℕ → ℝ)
    (heta : ∀ t, 0 < eta t) (T : ℕ) (hB0 : 0 ≤ S0.budget)
    (hFund : ∀ t < T, eta t ≤ (orbit S0 eta heta t).budget) :
    ∀ t ≤ T, 0 ≤ (orbit S0 eta heta t).budget := by
  intro t
  induction t with
  | zero =>
      intro _
      exact hB0
  | succ n ih =>
    intro hn
    have hprev := ih (by omega)
    have hfund := hFund n (by omega)
    change 0 ≤ (step (orbit S0 eta heta n) (eta n) (heta n)).budget
    rw [step_budget]
    linarith

noncomputable abbrev unitEta : ℕ → ℝ := fun _ => 1

theorem unitEta_pos (t : ℕ) : 0 < unitEta t := by norm_num

theorem finite_budget (w : ℝ) (T n : ℕ) :
    (orbit (initial w (T : ℝ)) unitEta unitEta_pos n).budget
      = (T : ℝ) - (n : ℝ) := by
  rw [orbit_budget (initial w (T : ℝ)) unitEta unitEta_pos n]
  change (T : ℝ) - ∑ t ∈ Finset.range n, unitEta t = (T : ℝ) - (n : ℝ)
  simp

theorem finite_strict (w : ℝ) (T n : ℕ) (hn : 0 < n) :
    (initial w (T : ℝ)).capability
      < (orbit (initial w (T : ℝ)) unitEta unitEta_pos n).capability :=
  orbit_strict (S0 := initial w (T : ℝ)) (eta := unitEta) unitEta_pos hn

theorem unit_budget_zero (w : ℝ) (T : ℕ) :
    (orbit (initial w (T : ℝ)) unitEta unitEta_pos T).budget = 0 := by
  rw [finite_budget]
  exact sub_self _

theorem unit_budget_nonneg {T n : ℕ} (w : ℝ) (hn : n ≤ T) :
    0 ≤ (orbit (initial w (T : ℝ)) unitEta unitEta_pos n).budget := by
  rw [finite_budget]
  have h : (n : ℝ) ≤ (T : ℝ) := by exact_mod_cast hn
  linarith

theorem two_step_nonvacuous (w : ℝ) :
    (initial w 2).capability <
      (orbit (initial w 2) unitEta unitEta_pos 2).capability ∧
      (orbit (initial w 2) unitEta unitEta_pos 2).budget = 0 :=
  ⟨finite_strict w 2 2 (by norm_num), unit_budget_zero w 2⟩

theorem hundred_step_nonvacuous (w : ℝ) :
    (initial w 100).capability <
      (orbit (initial w 100) unitEta unitEta_pos 100).capability ∧
      (orbit (initial w 100) unitEta unitEta_pos 100).budget = 0 :=
  ⟨finite_strict w 100 100 (by norm_num), unit_budget_zero w 100⟩

theorem first_parameter_nonzero :
    (orbit (initial 0 1) unitEta unitEta_pos 1).params = 1 / 2 := by
  change (step (initial 0 1) (unitEta 0) (unitEta_pos 0)).params = 1 / 2
  rw [step_params]
  norm_num [next, initial]

theorem budget_overspend_visible :
    (orbit (initial 0 1) unitEta unitEta_pos 2).budget < 0 := by
  have h : (orbit (initial 0 1) unitEta unitEta_pos 2).budget = (1:ℝ) - 2 := by
    simpa using finite_budget 0 1 2
  rw [h]
  norm_num

end Hagi.Unified.LogitGrowth
