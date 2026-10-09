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

namespace Hagi.Assumptions

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
    (C G D xi : ℕ → ℝ) (alpha gamma rho beta Cstar : ℝ)
    (hα : 0 < alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hC0 : 0 < C 0)
    (h_emp_cone0 : alpha / gamma * C 0 ≤ D 0)
    (h_emp_step : ∀ t < T, C (t + 1) = C t + G t)
    (h_emp_gain_prod : ∀ t < T, gamma * D t ≤ G t)
    (h_emp_dyn : ∀ t < T, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (h_emp_C_cap : ∀ t < T, C (t + 1) ≤ (1 + alpha) * C t)
    (h_emp_beta : ∀ t < T,
      alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta)
    (hCeil : C 0 * (1 + alpha) ^ T ≤ Cstar) :
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
    C G D xi alpha gamma rho beta Cstar hα hγ hρ hC0 h_emp_cone0
    h_emp_step h_emp_gain_prod h_emp_dyn h_emp_C_cap h_emp_beta hCeil

end Hagi.Assumptions
