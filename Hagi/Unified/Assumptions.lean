/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.MasterHAGITrunc

set_option linter.style.header false

/-!
# R263 (audit §7.2): the consolidated assumption record

The audit's complaint: the capstones take their measured
premises as a SCATTER of positional hypotheses (`h_emp_grow`,
`h_emp_merge`, ..., 26 binders on `MasterHAGI_trunc`) with no
single named home.

This module collects the horizon premises of
`MasterHAGI_trunc` into ONE structure with named fields:

* `Assumptions.Trunc` — the truncated-horizon premise set
  (stage cores, net cover, budget, risk nonnegativity, energy
  floor), parameterized over the state sequence;
* `masterhagi_trunc_of_assumptions` — the capstone invariant
  from the record: `MasterHAGI_trunc` with ALL positional
  binders supplied from the named fields.

Nothing here is new mathematics — this is the audit's
"Assumptions.lean" plumbing: the same premises, one named
home, one bridge theorem.
-/

open Real Finset InnerProductSpace Hagi Hagi.Foundations

namespace Hagi.Unified

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The truncated-horizon premise record (audit stage 7.2):
every `h_emp_*` binder of `MasterHAGI_trunc` as a named
field. -/
structure Trunc (S : ℕ → Hagi.GenState X) (lam nu Qtarget Emin : ℝ)
    (T : ℕ) where
  /-- Weights of the Qgen scalarization (fixed over the run). -/
  w : Fin 5 → ℝ
  hlam : 0 ≤ lam
  hnu : 0 < nu
  epsQ : ℕ → ℝ
  h_epsQ : ∀ t, 0 ≤ epsQ t
  h_core : ∀ t < T, CorePremises (S t) (S (t + 1)) (epsQ t) w
  h_net : ∀ t < T, lam * (verify (S t).toGrowthState).riskSpend
    + nu * epsQ t ≤ (verify (S t).toGrowthState).decrease
  h_budget0 : ∑ t ∈ Finset.range T,
      (verify (S t).toGrowthState).budgetSpend
    ≤ (S 0).toGrowthState.budget
  h_risk_nn : ∀ t, 0 ≤ (S t).toGrowthState.protectedRisk
  h_Emin : Emin ≤ (S T).toGrowthState.energy

/-- The capstone invariant from the consolidated record:
`MasterHAGI_trunc` with every positional binder supplied from
the named fields of `Assumptions.Trunc` plus the growth-block
telemetry. -/
theorem masterhagi_trunc_of_assumptions
    {K : Type*} [Fintype K] [Nonempty K]
    (S : ℕ → Hagi.GenState X) (lam nu Qtarget Emin : ℝ) (T : ℕ)
    (gd : Trunc S lam nu Qtarget Emin T)
    (g : ℕ → K → X)
    (dL eps L : ℕ → K → ℝ) (etaq : ℕ → ℝ)
    (hLq : ∀ t i, 0 < L t i) (hepsq : ∀ t i, 0 ≤ eps t i)
    (hetaq : ∀ t, 0 ≤ etaq t)
    (hd : ∀ t < T, (S t).toGrowthState.stepDir ≠ 0)
    (h_lipline : ∀ t < T, ∀ i, dL t i ≤ -etaq t
        * ⟪g t i, (S t).toGrowthState.stepDir⟫_ℝ
        + L t i * etaq t * etaq t * ‖(S t).toGrowthState.stepDir‖ ^ 2 / 2)
    (h_eta : ∀ t < T, etaq t
        ≤ safeqpEtaMax (g t) (eps t) (L t) (S t).toGrowthState.stepDir)
    (h_sumdL : ∀ t < T, (S (t + 1)).toGrowthState.protectedRisk
        = (S t).toGrowthState.protectedRisk + ∑ i, dL t i)
    (C G D xi : ℕ → ℝ) (alpha gamma rho beta : ℝ)
    (hα : 0 < alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hC0 : 0 < C 0)
    (h_emp_cone0 : alpha / gamma * C 0 ≤ D 0)
    (h_emp_step : ∀ t < T, C (t + 1) = C t + G t)
    (h_emp_gain_prod : ∀ t < T, gamma * D t ≤ G t)
    (h_emp_dyn : ∀ t < T, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (h_emp_C_cap : ∀ t < T, C (t + 1) ≤ (1 + alpha) * C t)
    (h_emp_beta : ∀ t < T,
      alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta) :
    CertifiedHAGIInvariant T
      (fun t => (S t).toGrowthState.protectedRisk)
      (fun t => hagiPotential (S t) lam nu Qtarget gd.w)
      C
      (fun t => (S t).toGrowthState.budget)
      (fun t => (verify (S t).toGrowthState).budgetSpend)
      (fun t => Qgen (S t).gen gd.w)
      (fun t => ∑ i, eps t i)
      alpha
      (Qtarget - (hagiPotential (S 0) lam nu Qtarget gd.w - Emin) / nu) :=
  MasterHAGI_trunc S lam nu Qtarget Emin gd.w gd.hlam gd.hnu gd.epsQ
    gd.h_epsQ T g dL eps L etaq hLq hepsq hetaq hd h_lipline h_eta h_sumdL
    gd.h_core gd.h_net gd.h_budget0 gd.h_risk_nn gd.h_Emin
    C G D xi alpha gamma rho beta hα hγ hρ hC0 h_emp_cone0
    h_emp_step h_emp_gain_prod h_emp_dyn h_emp_C_cap h_emp_beta

/-! ## Nonvacuity: a concrete idle-trajectory witness (R336, audit v3 Phase 6)

`trunc_nonvacuous`: the `Trunc` premise structure is inhabited
by a constant idle trajectory — every stage at equality
(zero gain/gap/risk/cost, `stepDir = 0`, `quantErr = 0`,
`sp = {eta := 0, L := 1, kappa := 0, s := 0}`), all stage
energies equal to `E0`, budget 1. On this trajectory the
composed cycle fixes energy/protectedRisk/budget, so every
`CorePremises` conjunct holds with `epsQ = 0`, `h_net` at
equality, and the budget sum is 0. This is the
structure-level companion of the arithmetic witnesses
(`masterhagi_growth_witness`, `cert_horizon_witness`): a
nondegenerate (T arbitrary, E0 arbitrary) admissible
trajectory of the formalized system. -/

/-- The idle stage constants: `eta = 0`, `L = 1`, `kappa = 0`, `s = 0`. -/
def idleSp : Hagi.StageParams where
  eta := 0
  L := 1
  kappa := 0
  s := 0

/-- The idle growth state: all stage energies `E0`, all
gains/gaps/risks/costs zero, `stepDir = 0`, budget 1. -/
def idleGrowth {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x0 : X) (E0 : ℝ) : Hagi.GrowthState X where
  weightDim := 0
  weights := Fin.elim0
  params := x0
  experts := 0
  energy := E0
  protectedRisk := 0
  budget := 1
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := idleSp
  effects := {
    growGain := 0
    growCost := 0
    growRisk := 0
    growEnergy := E0
    mergeEnergy := E0
    mergeRisk := 0
    jointEnergy := E0
    jointRisk := 0
    jointCost := 0
    quantErr := 0
    compressEnergy := E0
    compressRisk := 0
  }

/-- The idle GenState: the idle growth state with the zero
probe vector (all `Qvec` components 0, so `Qgen · w = 0` for
any `w`). -/
def idleGen {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x0 : X) (E0 : ℝ) : Hagi.GenState X where
  toGrowthState := idleGrowth x0 E0
  gen := ⟨0, 0, 0, 0, 0⟩

/-- On the idle state the composed cycle fixes the three
accounting carriers. -/
theorem idle_cycle_fixed {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x0 : X) (E0 : ℝ) :
    (Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (idleGrowth x0 E0))))).energy
      = (idleGrowth x0 E0).energy
    ∧ (Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (idleGrowth x0 E0))))).protectedRisk
      = (idleGrowth x0 E0).protectedRisk
    ∧ (Hagi.compress (Hagi.joint (Hagi.merge (Hagi.grow (idleGrowth x0 E0))))).budget
      = (idleGrowth x0 E0).budget := by
  simp [Hagi.grow, Hagi.merge, Hagi.joint, Hagi.compress, idleGrowth, idleSp]

/-- The zero probe vector scalarizes to 0 for any weights. -/
theorem idle_Qgen_zero (w : Fin 5 → ℝ) :
    Hagi.Qgen (⟨0, 0, 0, 0, 0⟩ : Hagi.GenMetrics) w = 0 := by
  unfold Hagi.Qgen Hagi.Qvec
  apply Finset.sum_eq_zero
  intro i _
  fin_cases i <;> simp

noncomputable def trunc_idle_witness {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (x0 : X) (E0 : ℝ) (T : ℕ) :
    Trunc (fun _ => idleGen x0 E0) 1 1 0 E0 T where
  w := 0
  hlam := by norm_num
  hnu := one_pos
  epsQ := 0
  h_epsQ := fun _ => le_refl 0
  h_core := by
    intro t _
    unfold Hagi.CorePremises idleGen
    simp only [Hagi.grow, Hagi.merge, Hagi.joint, Hagi.compress,
      idleGrowth, idleSp, Hagi.gainJoint, Hagi.Qgen, Hagi.Qvec]
    norm_num
  h_net := by
    intro t _
    have hv : (Hagi.verify (idleGen x0 E0).toGrowthState).riskSpend = 0
        ∧ (Hagi.verify (idleGen x0 E0).toGrowthState).decrease = 0 := by
      constructor <;> simp [Hagi.verify, idleGen, idleGrowth, idleSp, Hagi.gainJoint]
    rw [hv.1, hv.2]
    norm_num
  h_budget0 := by
    have hv : (Hagi.verify (idleGen x0 E0).toGrowthState).budgetSpend = 0 := by
      simp [Hagi.verify, idleGen, idleGrowth]
    show ∑ t ∈ Finset.range T,
        (Hagi.verify ((fun _ => idleGen x0 E0) t).toGrowthState).budgetSpend
      ≤ ((fun _ => idleGen x0 E0) 0).toGrowthState.budget
    simp only []
    rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.range T) => hv)]
    simp [idleGen, idleGrowth]
  h_risk_nn := fun _ => by simp [idleGen, idleGrowth]
  h_Emin := le_refl E0

/-- **`Trunc` is inhabited** (R336, audit v3 Phase 6): the idle
trajectory is an admissible premise set for any horizon `T`
and any idle energy `E0` — the structure-level companion of
the arithmetic witnesses. -/
theorem trunc_nonvacuous {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (x0 : X) (E0 : ℝ) (T : ℕ) :
    Nonempty (Trunc (fun _ => idleGen x0 E0) 1 1 0 E0 T) :=
  ⟨trunc_idle_witness x0 E0 T⟩

end Hagi.Unified