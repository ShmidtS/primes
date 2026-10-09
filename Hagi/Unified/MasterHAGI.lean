/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Generalization.ModeState
import Hagi.Dynamics.WallClockTakeoff
import Hagi.Step.SafeQPStep
import Hagi.Foundations.Telescope
set_option linter.style.header false

/-!
# R111: MasterHAGI — the CONDITIONAL capstone: the unified
# certified invariant assembled from the existing pieces

The audit §15-VII demand: ONE compositional theorem assembling
the certified pieces into a single conditional invariant
`CertifiedHAGIInvariant`. This module adds NO new mathematics:
every premise below is the exact (named) hypothesis of the
cited existing theorem, and the proofs are compositions of
those theorems plus honest telescoping/bridging algebra.

## The audit's chain, premise by premise (SOURCE → premise)

* **Safety** — `Hagi/Step/SafeQPStep` (R105) `safeqp_eta_max`:
  the per-domain descent-lemma window
  `η ≤ min(1, ⨅_i 2m_i/(L_i‖d*‖²))` keeps EVERY protected
  domain within its budget (ΔL_i ≤ ε_i); aggregated to the
  risk-spend bound by `Hagi/Generalization/ModeState` (R109)
  `safeqp_risk_bound_compose` (per-domain sum = risk increment,
  the h_sumdL link).
* **Progress** — `Hagi/Unified/GrowthState` (R91)
  `growth_cycle_potential` / `certificate_sound` (whose
  real-variable form is `Hagi/Unified/TopLevel.lean`
  `top_level_cycle_bound`, R88): the macro-cycle potential law
  Φ(compress∘joint∘merge∘grow S) ≤ Φ(S) − decrease + riskSpend.
* **Renewal / Growth** — `Hagi/Growth/FrontierScaling` (R107)
  `sustained_takeoff_from_production`: the cone invariant
  D_t ≥ (α/γ)C_t DERIVED from the production dynamics
  D_{t+1} ≥ ρD_t + βC_t − ξ_t supplies the gate, giving
  C_T ≥ C₀(1+α)^T with NO free h_emp_frontier_scaling.
* **Generalization** — `Hagi/Generalization/ModeState` (R109)
  `generalization_safe_step`: Φ_HAGI decreases by the certified
  fit amount minus λ·(risk spend) minus ν·ε_Q (the probe
  tolerance ε_Q is pure telemetry, h_emp_G).
* **Budget** — `Hagi/Unified/GrowthState` (R91)
  `budget_account`: the composed budget is EXACTLY the initial
  budget minus the declared budgetSpend; telescoped over T
  cycles.
* **Probability** — `Hagi/Probability/ConditionalSuccess`
  (R95) `takeoff_time_form` / `Hagi/Dynamics/WallClockTakeoff`
  (R110) `wallclock_rate_from_cone`: with constant per-cycle
  wall cost τ and the success-count floor
  Σs_t ≥ p₀T − Δ (the R95 concentration hypothesis form), the
  capability bound takes the explicit exp form
  C_T ≥ C₀·exp(k_eff·W − ln(1+α)·Δ), k_eff = p₀ln(1+α)/τ.

## The h_emp inventory (what stays measured, and why)

The capstone hides NOTHING beyond what the sources already
declare: h_emp_grow (nonconvex training descent — no training
theorem exists), h_emp_merge (satisfied by the Concat adapter,
R88, but still a measured stage law), h_emp_smooth (Lipschitz
energy), h_emp_dist/h_emp_lip (ternary distortion /
curvature), h_emp_G (probe telemetry), the R107 dynamics
(h_dyn/hβ — measurable from Diversity/GapLaw telemetry), the
R95 independence/p-floor hypotheses, and the per-cycle net
premise h_net (the certified stage decrease covers the
λ-weighted risk and the ν-weighted probe slack). Deriving these
from the real runtime (Implementation Refinement) is the open
frontier I — this module is the CONDITIONAL certificate of the
LOOP given the measured premises, not their derivation.

## Two-level composition (task item 5)

`MasterHAGICore` (one cycle: progress + budget + gen, R91+R109
plumbing, with `CorePremises` naming the exact source
hypotheses) + `MasterHAGI` (horizon: adds R105 safety, R107
renewal, telescoping) + `MasterHAGI_wallclock` /
`MasterHAGI_probability` (the R110/R95 concentration forms).

AUDIT 2026-10-04 (h_emp_ discipline): the growth premises
here (h_step, h_gain_prod, h_dyn, h_C_cap, hβ) and the
CorePremises modeling conjuncts (stage laws, Lipschitz
windows) are EMPIRICAL — they lack the h_emp_ prefix for
historical source-theorem compatibility. The
horizon-truncated, h_emp_-named form is
`Hagi/Unified/MasterHAGITrunc.lean` (`MasterHAGI_trunc`,
`masterhagi_growth_witness`): prefer it for new use.
-/

open Real Finset InnerProductSpace MeasureTheory ProbabilityTheory

namespace Hagi
open Hagi.Foundations

section MasterHAGI

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ## The unified invariant (the audit's target shape) -/

/-- **The conditional capstone invariant** at horizon T — five
conjuncts on the real carrier sequences of the loop:

* `risk_bound` — Safety: the protected-risk (cumulative
  forgetting) increment over T cycles is at most the sum of the
  per-cycle per-domain SafeQP budgets ε (R105, aggregated).
* `phi_bound` — Progress+Generalization: Φ_HAGI (R91's potential
  extended by R109's probe penalty) does not increase over the
  horizon.
* `capability_growth` — Growth: the capability channel grows at
  the certified geometric rate (R107's derived takeoff).
* `budget_respected` — Budget: the account is EXACT
  (`budget T = budget 0 − Σ spend`) and stays nonnegative.
* `gen_floor` — Generalization floor: the scalarized probe
  Qgen stays above the explicit floor
  Q_target − (Φ_HAGI(0) − E_min)/ν.

The sequence carriers: `risk` (protectedRisk), `phi` (Φ_HAGI),
`cap` (capability channel), `budget`/`spend` (compute account),
`genq` (Qgen), `epsReg` (per-cycle SafeQP budget sums), `alpha`
(the certified growth rate), `Qfloor` (the explicit probe
floor). -/

structure CertifiedHAGIInvariant (T : ℕ)
    (risk phi cap budget spend genq epsReg : ℕ → ℝ)
    (alpha Qfloor : ℝ) : Prop where
  /-- Safety: cumulative forgetting bounded by the per-domain
  SafeQP budgets, telescoped over the horizon. -/
  risk_bound : risk T - risk 0 ≤ ∑ t ∈ Finset.range T, epsReg t
  /-- Progress + generalization: Φ_HAGI nonincreasing. -/
  phi_bound : phi T ≤ phi 0
  /-- Growth: the derived sustained takeoff (R107). -/
  capability_growth : cap 0 * (1 + alpha) ^ T ≤ cap T
  /-- Budget: exact account and nonnegativity. -/
  budget_respected :
    budget T = budget 0 - ∑ t ∈ Finset.range T, spend t ∧ 0 ≤ budget T
  /-- Generalization floor: Qgen stays above Qfloor. -/
  gen_floor : Qfloor ≤ genq T

/-! ## The one-cycle premise set (named for traceability) -/

/-- **The one-cycle premises of the capstone** — each conjunct
is the EXACT hypothesis of the cited source theorem,
instantiated at the pre-cycle state `S` and post-cycle state
`S'`:

* conjuncts 1–13: `growth_cycle_potential` / `certificate_sound`
  (R91, `Hagi/Unified/GrowthState`): the gap sign, the measured
  stage laws (h_emp_grow, h_emp_merge, h_emp_smooth,
  h_emp_dist, h_emp_lip), the SafeQP window (hL, heta, heta0,
  hdescent) and the compress constants (hkappa, hs, hdn);
* conjunct 14 (h_cycle): the bridging link — `S'` IS the
  composed cycle `compress(joint(merge(grow S)))` on the three
  carriers the account and potential laws read (energy,
  protectedRisk, budget). This is definitional plumbing, not a
  new assumption: the composite's fields are the measured
  stage outputs by construction (R91);
* conjunct 15: R109's `generalization_safe_step` probe
  tolerance (h_emp_G, MEASURED telemetry ε_Q). -/

def CorePremises (S S' : GenState X) (epsQ : ℝ) (w : Fin 5 → ℝ) : Prop :=
  0 ≤ S.toGrowthState.gap
  ∧ S.toGrowthState.growEnergy
      ≤ S.toGrowthState.energy - S.toGrowthState.growGain
  ∧ S.toGrowthState.mergeEnergy
      ≤ S.toGrowthState.growEnergy - S.toGrowthState.gap
  ∧ 0 < S.toGrowthState.sp.L
  ∧ S.toGrowthState.sp.eta ≤ 1 / S.toGrowthState.sp.L
  ∧ 0 ≤ S.toGrowthState.sp.eta
  ∧ ‖S.toGrowthState.stepDir‖ ^ 2
      ≤ ⟪S.toGrowthState.grad, S.toGrowthState.stepDir⟫_ℝ
  ∧ S.toGrowthState.jointEnergy
      ≤ S.toGrowthState.mergeEnergy
        - S.toGrowthState.sp.eta * ⟪S.toGrowthState.grad, S.toGrowthState.stepDir⟫_ℝ
        + S.toGrowthState.sp.L * S.toGrowthState.sp.eta ^ 2
          * ‖S.toGrowthState.stepDir‖ ^ 2 / 2
  ∧ 0 ≤ S.toGrowthState.sp.kappa
  ∧ 0 ≤ S.toGrowthState.sp.s
  ∧ 0 ≤ S.toGrowthState.quantErr
  ∧ S.toGrowthState.quantErr ≤ 1 / 2
  ∧ S.toGrowthState.compressEnergy - S.toGrowthState.jointEnergy
      ≤ S.toGrowthState.sp.kappa * S.toGrowthState.sp.s * S.toGrowthState.quantErr
  ∧ (S'.toGrowthState.energy
        = (compress (joint (merge (grow S.toGrowthState)))).energy
      ∧ S'.toGrowthState.protectedRisk
        = (compress (joint (merge (grow S.toGrowthState)))).protectedRisk
      ∧ S'.toGrowthState.budget
        = (compress (joint (merge (grow S.toGrowthState)))).budget)
  ∧ (Qgen S.gen w - epsQ ≤ Qgen S'.gen w)

/-! ## Level 1: the one-cycle composition (R91 + R109) -/

/-- **MasterHAGICore** — ONE growth cycle, conditionally
certified: under the R91 stage laws and the R109 gen tolerance
(`CorePremises`), the cycle's Φ_HAGI decreases by the emitted
certificate's decrease up to the honest error terms
(λ·riskSpend + ν·ε_Q), and the compute account is EXACTLY the
budget_account law (R91). Composition:
`certificate_sound` (R91) supplies `generalization_safe_step`'s
(R109) fit hypothesis (the real energy decrease dominates the
certificate's decrease — NOT restated) and its risk hypothesis
(the cycle's protectedRisk increment IS the declared riskSpend);
`budget_account` (R91) supplies the budget conjunct. -/

theorem MasterHAGICore (S S' : GenState X) (lam nu Qtarget epsQ : ℝ)
    (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 ≤ nu) (h_epsQ : 0 ≤ epsQ)
    (hp : CorePremises S S' epsQ w) :
    hagiPotential S' lam nu Qtarget w
      ≤ hagiPotential S lam nu Qtarget w - (verify S.toGrowthState).decrease
        + lam * (verify S.toGrowthState).riskSpend + nu * epsQ
    ∧ S'.toGrowthState.budget
      = S.toGrowthState.budget - (verify S.toGrowthState).budgetSpend := by
  obtain ⟨hgap, h_emp_grow, h_emp_merge, hL, heta, heta0, hdescent,
    h_emp_smooth, hkappa, hs, hdn, h_emp_dist, h_emp_lip, h_cycle, h_emp_G⟩ := hp
  obtain ⟨hcE, hcR, hcB⟩ := h_cycle
  -- R91: the real potential decrease dominates the certificate
  have hcs := certificate_sound S.toGrowthState hgap h_emp_grow h_emp_merge
    hL heta heta0 hdescent h_emp_smooth hkappa hs hdn h_emp_dist h_emp_lip
  have hp1 : potential (compress (joint (merge (grow S.toGrowthState))))
      = (compress (joint (merge (grow S.toGrowthState)))).energy
        + (compress (joint (merge (grow S.toGrowthState)))).protectedRisk := rfl
  have hp2 : potential S.toGrowthState
      = S.toGrowthState.energy + S.toGrowthState.protectedRisk := rfl
  have hrsc : (compress (joint (merge (grow S.toGrowthState)))).protectedRisk
      = S.toGrowthState.protectedRisk
        + (verify S.toGrowthState).riskSpend := by
    simp [verify, grow, merge, joint, compress]
    ring
  rw [hp1, hp2, hrsc] at hcs
  -- the certified energy decrease (R91's output feeds R109's h_emp_fit)
  have hcompE : (compress (joint (merge (grow S.toGrowthState)))).energy
      ≤ S.toGrowthState.energy - (verify S.toGrowthState).decrease := by
    linarith
  have h_emp_fit : S'.toGrowthState.energy
      ≤ S.toGrowthState.energy - (verify S.toGrowthState).decrease := by
    rw [hcE]; exact hcompE
  -- the risk increment IS the declared riskSpend (R91's account)
  have h_risk : S'.toGrowthState.protectedRisk - S.toGrowthState.protectedRisk
      ≤ (verify S.toGrowthState).riskSpend := by
    rw [hcR, hrsc]
    ring_nf
    linarith
  refine ⟨generalization_safe_step S S' lam nu Qtarget w hlam hnu
    (verify S.toGrowthState).decrease epsQ (verify S.toGrowthState).riskSpend
    h_epsQ h_emp_fit h_risk h_emp_G, ?_⟩
  rw [hcB]
  exact budget_account S.toGrowthState

/-! ## R116: the FULL-state binding of h_cycle -/

/-- **The full-state cycle refinement** (R116, audit §6): the
h_cycle conjunct of `CorePremises` binds only energy,
protectedRisk and budget — an `S'` with the right accounting but
arbitrary `capability`/`params`/`experts` satisfied it. The
honest refinement is the FULL record equality: `S'` IS the
composed cycle state (ALL fields), with the probe vector
carried over unchanged. This is the Lean-side half of the
RuntimeRefinement bridge (§I of the audit); the runtime side
(actual tensor/optimizer execution implying this equality)
remains the implementation gap, stated as a premise here. -/
def FullCycleRefinement (S S' : GenState X) : Prop :=
  S'.toGrowthState = compress (joint (merge (grow S.toGrowthState)))
  ∧ S'.gen = S.gen

/-- The full-state equality implies the three field equalities
of the old h_cycle conjunct (energy/protectedRisk/budget) —
the refinement is strictly stronger, closing the
"right accounting, arbitrary capability" hole. -/
theorem full_cycle_field_eq {S S' : GenState X}
    (hfull : FullCycleRefinement S S') :
    S'.toGrowthState.energy
      = (compress (joint (merge (grow S.toGrowthState)))).energy
    ∧ S'.toGrowthState.protectedRisk
      = (compress (joint (merge (grow S.toGrowthState)))).protectedRisk
    ∧ S'.toGrowthState.budget
      = (compress (joint (merge (grow S.toGrowthState)))).budget := by
  obtain ⟨heq, _⟩ := hfull
  exact ⟨by rw [heq], by rw [heq], by rw [heq]⟩

/-- **MasterHAGICore under the full-state refinement**: the same
one-cycle certificate, but `S'` is bound to the composed cycle
on ALL fields (not only energy/risk/budget). Every conclusion of
`MasterHAGICore` carries over; additionally `S'`'s capability,
experts, params, weights are exactly the cycle's — the growth
accounting can no longer be satisfied by an unrelated state. -/
theorem MasterHAGICore_refined (S S' : GenState X) (lam nu Qtarget epsQ : ℝ)
    (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 ≤ nu) (h_epsQ : 0 ≤ epsQ)
    (hp : CorePremises S S' epsQ w)
    (hfull : FullCycleRefinement S S') :
    hagiPotential S' lam nu Qtarget w
      ≤ hagiPotential S lam nu Qtarget w - (verify S.toGrowthState).decrease
        + lam * (verify S.toGrowthState).riskSpend + nu * epsQ
    ∧ S'.toGrowthState.budget
      = S.toGrowthState.budget - (verify S.toGrowthState).budgetSpend :=
  MasterHAGICore S S' lam nu Qtarget epsQ w hlam hnu h_epsQ hp

/-! ## Telescoping helpers — делегация Foundations (R163)

Приватные копии удалены; `telescope_le` / `telescope_sum_le` /
`telescope_sub_sum` разрешаются в `Hagi.Foundations` через
`open Hagi.Foundations` выше. -/

/-! ## The generalization-floor extraction (real algebra) -/

/-- **From a Φ_HAGI bound to an explicit probe floor**: with an
active penalty weight ν > 0, an energy lower bound E_min and a
nonnegative protected risk, a Φ_HAGI upper bound Phibar forces
the scalarized probe above
Q_target − (Phibar − E_min)/ν — the max(0,·) penalty can absorb
at most (Phibar − E_min)/ν of the gap. This is where the
invariant's `gen_floor` field comes from. -/

theorem hagi_gen_floor (S : GenState X) (lam nu Qtarget Phibar Emin : ℝ)
    (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 < nu)
    (hEmin : Emin ≤ S.toGrowthState.energy)
    (hRnn : 0 ≤ S.toGrowthState.protectedRisk)
    (hphi : hagiPotential S lam nu Qtarget w ≤ Phibar) :
    Qtarget - (Phibar - Emin) / nu ≤ Qgen S.gen w := by
  have hm : Qtarget - Qgen S.gen w ≤ max 0 (Qtarget - Qgen S.gen w) :=
    le_max_right _ _
  have hpen : nu * max 0 (Qtarget - Qgen S.gen w)
      ≤ Phibar - S.toGrowthState.energy
        - lam * S.toGrowthState.protectedRisk := by
    have := hphi
    unfold hagiPotential Hagi.Foundations.hagiPotential at this
    linarith
  have hnu3 : nu * (Qtarget - Qgen S.gen w) ≤ Phibar - Emin := by
    calc nu * (Qtarget - Qgen S.gen w)
        ≤ nu * max 0 (Qtarget - Qgen S.gen w) :=
          mul_le_mul_of_nonneg_left hm hnu.le
      _ ≤ Phibar - Emin := by
          have : lam * S.toGrowthState.protectedRisk ≥ 0 :=
            mul_nonneg hlam hRnn
          linarith
  have hdiv : Qtarget - Qgen S.gen w ≤ (Phibar - Emin) / nu := by
    rw [le_div_iff₀ hnu, mul_comm]
    exact hnu3
  linarith

/-! ## Level 2: the horizon composition (the capstone) -/

/-- **MasterHAGI** — the conditional capstone: at horizon T,
under (i) the per-cycle `CorePremises` (R91 stage laws + R109
probe tolerance + the cycle link), (ii) the per-cycle SafeQP
safety premises (R105: the derived window and per-domain
descent bound, aggregated by R109's `safeqp_risk_bound_compose`
via the per-domain risk decomposition h_sumdL), (iii) the
per-cycle NET premise h_net (the certified stage decrease
covers the λ-weighted risk spend and the ν-weighted probe
slack), (iv) the budget solvency `h_budget0`, and (v) the R107
production-dynamics premises (the capability channel C, G, D, ξ
— honest: capability is OUTSIDE Φ in R91, so the renewal
semantics live on their own sequences), the FULL five-component
invariant `CertifiedHAGIInvariant` holds at T.

This certifies the LOOP given the measured premises; the
premises' derivation from the real runtime is the open frontier
I (see the module docstring's h_emp inventory). -/

theorem MasterHAGI {K : Type*} [Fintype K] [Nonempty K]
    (S : ℕ → GenState X) (lam nu Qtarget Emin : ℝ) (w : Fin 5 → ℝ)
    (hlam : 0 ≤ lam) (hnu : 0 < nu)
    (epsQ : ℕ → ℝ) (h_epsQ : ∀ t, 0 ≤ epsQ t)
    (T : ℕ)
    (g : ℕ → K → X) (dL eps L : ℕ → K → ℝ) (etaq : ℕ → ℝ)
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
    (h_core : ∀ t < T, CorePremises (S t) (S (t + 1)) (epsQ t) w)
    (h_net : ∀ t < T, lam * (verify (S t).toGrowthState).riskSpend
        + nu * epsQ t ≤ (verify (S t).toGrowthState).decrease)
    (h_budget0 : ∑ t ∈ Finset.range T,
        (verify (S t).toGrowthState).budgetSpend
      ≤ (S 0).toGrowthState.budget)
    (h_risk_nn : ∀ t, 0 ≤ (S t).toGrowthState.protectedRisk)
    (h_Emin : Emin ≤ (S T).toGrowthState.energy)
    (C G D xi : ℕ → ℝ) (alpha gamma rho beta : ℝ)
    (hα : 0 < alpha) (hγ : 0 < gamma) (hρ : 0 ≤ rho)
    (hC0 : 0 < C 0) (h_cone0 : alpha / gamma * C 0 ≤ D 0)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, gamma * D t ≤ G t)
    (h_dyn : ∀ t, rho * D t + beta * C t - xi t ≤ D (t + 1))
    (h_C_cap : ∀ t, C (t + 1) ≤ (1 + alpha) * C t)
    (hβ : ∀ t, alpha / gamma * ((1 + alpha) - rho) + xi t / C t ≤ beta) :
    CertifiedHAGIInvariant T
      (fun t => (S t).toGrowthState.protectedRisk)
      (fun t => hagiPotential (S t) lam nu Qtarget w)
      C
      (fun t => (S t).toGrowthState.budget)
      (fun t => (verify (S t).toGrowthState).budgetSpend)
      (fun t => Qgen (S t).gen w)
      (fun t => ∑ i, eps t i)
      alpha
      (Qtarget - (hagiPotential (S 0) lam nu Qtarget w - Emin) / nu) := by
  -- ### Progress+gen+budget: the per-cycle Core composition
  have hcore : ∀ t < T,
      hagiPotential (S (t + 1)) lam nu Qtarget w
        ≤ hagiPotential (S t) lam nu Qtarget w
          - (verify (S t).toGrowthState).decrease
          + lam * (verify (S t).toGrowthState).riskSpend + nu * epsQ t
      ∧ (S (t + 1)).toGrowthState.budget
        = (S t).toGrowthState.budget
          - (verify (S t).toGrowthState).budgetSpend :=
    fun t ht => MasterHAGICore (S t) (S (t + 1)) lam nu Qtarget (epsQ t) w
      hlam hnu.le (h_epsQ t) (h_core t ht)
  -- ### Φ_HAGI telescope (the net premise absorbs the costs)
  have hphi_step : ∀ t < T,
      hagiPotential (S (t + 1)) lam nu Qtarget w
        ≤ hagiPotential (S t) lam nu Qtarget w := by
    intro t ht
    have h := (hcore t ht).1
    exact le_trans h (by linarith [h_net t ht])
  have hphi_T : hagiPotential (S T) lam nu Qtarget w
      ≤ hagiPotential (S 0) lam nu Qtarget w :=
    telescope_le (f := fun t => hagiPotential (S t) lam nu Qtarget w) hphi_step
  -- ### Safety: R105 per-domain budgets, aggregated (R109 compose)
  have hdLb : ∀ t < T, ∀ i, dL t i ≤ eps t i := by
    intro t ht i
    exact safeqp_eta_max (g t) (eps t) (L t) (S t).toGrowthState.stepDir
      (dL t) (etaq t) (hLq t) (hepsq t) (hetaq t) (hd t ht)
      (fun i => h_lipline t ht i) (h_eta t ht) i
  have hrisk_step : ∀ t < T,
      (S (t + 1)).toGrowthState.protectedRisk
        - (S t).toGrowthState.protectedRisk ≤ ∑ i, eps t i := by
    intro t ht
    exact safeqp_risk_bound_compose (S t) (S (t + 1)) (dL t) (eps t)
      (h_sumdL t ht) (hdLb t ht)
  -- ### Budget: the exact account telescoped
  have hbud_step : ∀ t < T, (S (t + 1)).toGrowthState.budget
      = (S t).toGrowthState.budget
        - (verify (S t).toGrowthState).budgetSpend :=
    fun t ht => (hcore t ht).2
  have hbud_T : (S T).toGrowthState.budget
      = (S 0).toGrowthState.budget
        - ∑ t ∈ Finset.range T, (verify (S t).toGrowthState).budgetSpend :=
    telescope_sub_sum
      (f := fun t => (S t).toGrowthState.budget)
      (c := fun t => (verify (S t).toGrowthState).budgetSpend) hbud_step
  -- ### Growth: the R107 derived takeoff
  have hcap := sustained_takeoff_from_production C G D xi alpha gamma rho beta
    hα hγ hρ hC0 h_cone0 h_step h_gain_prod h_dyn h_C_cap hβ T
  -- ### Gen floor: extract from the Φ_HAGI bound
  have hfloor := hagi_gen_floor (S T) lam nu Qtarget
    (hagiPotential (S 0) lam nu Qtarget w) Emin w hlam hnu h_Emin
    (h_risk_nn T) hphi_T
  -- ### assemble the invariant
  refine ⟨?_, hphi_T, hcap, ⟨hbud_T, ?_⟩, hfloor⟩
  · exact telescope_sum_le
      (f := fun t => (S t).toGrowthState.protectedRisk)
      (c := fun t => ∑ i, eps t i) hrisk_step
  · linarith [h_budget0]

/-! ## The wall-clock corollary (R110 composition) -/

/-- **The gate→multiplier bridge**: under the renewal semantics
C_{t+1} = C_t + G_t with an indicator success sequence
(s_t ≤ 1) and the cone gate α·C_t ≤ G_t on successes, the
per-cycle multiplier law C_{t+1} ≥ C_t·(1+α)^{s_t} of R110's
`wallclock_rate_from_cone` holds — the multiplier is (1+α) on
successes (the gate) and neutral on failures. -/

theorem gate_success_multiplier (C G : ℕ → ℝ) (alpha : ℝ) (t : ℕ)
    (s : ℕ → ℕ)
    (hstep : C (t + 1) = C t + G t) (hG0 : 0 ≤ G t) (hs1 : s t ≤ 1)
    (hgate : s t = 1 → alpha * C t ≤ G t) :
    C t * (1 + alpha) ^ (s t) ≤ C (t + 1) := by
  have hs01 : s t = 0 ∨ s t = 1 := by omega
  rcases hs01 with h0 | h1
  · rw [h0, pow_zero, mul_one]
    linarith
  · rw [h1, pow_one]
    have hd : C t * (1 + alpha) = C t + alpha * C t := by ring
    have hg := hgate h1
    linarith [hd]

/-- **MasterHAGI_wallclock** — the explicit exp form of the
capability bound: under the R107 renewal semantics and the cone
gate (supplied by `frontier_cone_invariant` under the cone
premises — taken here in its output form, exactly as R110's
`wallclock_rate_from_cone` frames it), with an indicator success
sequence, the R95 success-count floor (hypothesis form:
Σs_t ≥ p₀T − Δ; the w.p. ≥ 1−δ guarantee is R95's
`success_count_lower_p0`, not reproved here) and CONSTANT
per-cycle wall cost τ, the capability at wall time W = T·τ is

  C_T ≥ C₀·exp(k_eff·W − ln(1+α)·Δ), k_eff = p₀·ln(1+α)/τ.

Composition: `gate_success_multiplier` (this module) feeds
`wallclock_rate_from_cone` (R110). -/

theorem MasterHAGI_wallclock (C G D : ℕ → ℝ) (gamma' alpha tau p0 Delta : ℝ)
    (s : ℕ → ℕ)
    (hα : 0 < alpha) (hγ : 0 < gamma')  -- hγ: uniform cone-gate signature; the
      -- gate's positivity is already inside h_gate (linter notes hγ unused)
    (hC0 : 0 < C 0) (hCpos : ∀ t, 0 < C t)
    (h_step : ∀ t, C (t + 1) = C t + G t)
    (h_gain_prod : ∀ t, gamma' * D t ≤ G t)
    (h_gate : ∀ t, alpha * C t ≤ gamma' * D t)
    (htau : 0 < tau) (hs1 : ∀ t, s t ≤ 1)
    (T : ℕ)
    (hcount : p0 * (T : ℝ) - Delta
      ≤ ∑ t ∈ Finset.range T, (s t : ℝ)) :
    C T ≥ C 0 * Real.exp
      ((p0 * Real.log (1 + alpha) / tau) * ((T : ℝ) * tau)
        - Real.log (1 + alpha) * Delta) := by
  -- G_t ≥ 0: the gate and positivity of C_t, α force it
  have hG0 : ∀ t, 0 ≤ G t := by
    intro t
    have h1 : 0 < alpha * C t := mul_pos hα (hCpos t)
    have h2 := le_trans (h_gate t) (h_gain_prod t)
    linarith
  have hmul : ∀ t, C t * (1 + alpha) ^ (s t) ≤ C (t + 1) :=
    fun t => gate_success_multiplier C G alpha t s (h_step t) (hG0 t)
      (hs1 t) (fun _ => le_trans (h_gate t) (h_gain_prod t))
  exact wallclock_rate_from_cone C s alpha tau p0 Delta hα htau hC0 hmul T hcount

/-! ## The probability form (R95 composition) -/

/-- **The multiplier→log bridge**: positivity plus the
per-success multiplier law give the log-form bridge of R95's
`log_growth`/`takeoff_time_form` with rate a := ln(1+α) and
ZERO friction. -/

theorem log_bridge_from_multiplier (C : ℕ → ℝ) (s : ℕ → ℕ) (alpha : ℝ)
    (hα : 0 < alpha) (t : ℕ) (hCpos : 0 < C t)
    (hmul : C t * (1 + alpha) ^ (s t) ≤ C (t + 1)) :
    Real.log (1 + alpha) * (s t : ℝ)
      ≤ Real.log (C (t + 1)) - Real.log (C t) := by
  have hone : (1 : ℝ) ≤ 1 + alpha := by linarith
  have h1 : 0 < (1 + alpha) ^ (s t) := by positivity
  have h1a : (1 : ℝ) ≤ (1 + alpha) ^ (s t) := by
    induction s t with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        nlinarith [ih, hone]
  have h2 : 0 < C t * (1 + alpha) ^ (s t) := mul_pos hCpos h1
  have h3 : Real.log (C t * (1 + alpha) ^ (s t))
      = Real.log (C t) + (s t : ℝ) * Real.log (1 + alpha) := by
    rw [Real.log_mul hCpos.ne' h1.ne', Real.log_pow]
  have h4a : Real.log (C t)
      ≤ Real.log (C t * (1 + alpha) ^ (s t)) :=
    Real.log_le_log hCpos (by nlinarith [h1a])
  have h4b : Real.log (C t * (1 + alpha) ^ (s t))
      ≤ Real.log (C (t + 1)) :=
    Real.log_le_log h2 hmul
  linarith

/-- **MasterHAGI_probability** — the R95 composition form:
on a probability space with independent [0,1]-valued success
indicators `Sc` (means ≥ p₀ — the R95 h_emp_ hypotheses) and
the per-ω multiplier law
C_t·exp(ln(1+α)·Sc_t) ≤ C_{t+1} (the gate's continuous form:
one unit of success buys the factor (1+α)), then with
probability ≥ 1 − δ

  C_T ≥ C₀·exp(ln(1+α)·(p₀·T − Δ(T,δ))),

Δ(T,δ) = √(2T·log(1/δ)) the explicit Hoeffding concentration
price. This is `takeoff_time_form` (R95) applied with
a := ln(1+α) and zero friction, fed by the log bridge below
(positivity + `Real.log_mul`/`Real.exp_log` algebra). -/

theorem MasterHAGI_probability {Om : Type*} [MeasurableSpace Om]
    {mu : MeasureTheory.Measure Om} [MeasureTheory.IsProbabilityMeasure mu]
    (C Sc : ℕ → Om → ℝ) (alpha p0 delta : ℝ)
    (hα : 0 < alpha)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hCpos : ∀ t om, 0 < C t om)
    (hmul : ∀ t om, C t om * Real.exp (Real.log (1 + alpha) * Sc t om)
      ≤ C (t + 1) om)
    (h_emp_meas : ∀ t, Measurable (Sc t))
    (h_emp_01 : ∀ t om, Sc t om ∈ Set.Icc 0 1)
    (h_emp_indep : ProbabilityTheory.iIndepFun Sc mu)
    (h_emp_p : ∀ t, p0 ≤ mu[Sc t])
    (T : ℕ) :
    mu.real {om | C T om ≥ C 0 om * Real.exp
      (Real.log (1 + alpha) * (p0 * (T : ℝ) - concDelta T delta))} ≥ 1 - delta := by
  have ha : 0 ≤ Real.log (1 + alpha) := Real.log_nonneg (by linarith)
  -- the log-form bridge from the multiplier law (per sample point)
  have hbridge : ∀ t om, Real.log (C (t + 1) om) - Real.log (C t om)
      ≥ Real.log (1 + alpha) * Sc t om := by
    intro t om
    have hex : Real.exp (Real.log (1 + alpha) * Sc t om) > 0 := Real.exp_pos _
    have hprod : 0 < C t om * Real.exp (Real.log (1 + alpha) * Sc t om) :=
      mul_pos (hCpos t om) hex
    have hlog : Real.log (C t om * Real.exp (Real.log (1 + alpha) * Sc t om))
        = Real.log (C t om) + Real.log (1 + alpha) * Sc t om := by
      rw [Real.log_mul (hCpos t om).ne' hex.ne', Real.log_exp]
    linarith [Real.log_le_log hprod (hmul t om)]
  have hbridge0 : ∀ (t : ℕ) (om : Om), Real.log (C (t + 1) om) - Real.log (C t om)
      ≥ Real.log (1 + alpha) * Sc t om - (0:ℝ) := by
    intro t om
    have := hbridge t om
    linarith
  have hmain := takeoff_time_form (S := Sc) (T := T) (delta := delta)
    (p0 := p0) (a := Real.log (1 + alpha)) (eps := fun _ => 0)
    hdelta hdelta1 ha hCpos hbridge0 h_emp_meas h_emp_01 h_emp_indep h_emp_p
  refine le_trans hmain ?_
  apply measureReal_mono _ (measure_ne_top mu _)
  intro om hom
  simp only [Set.mem_ofPred_eq] at hom ⊢
  rw [show ∑ t ∈ Finset.range T, ((0:ℝ)) = 0 from by simp] at hom
  simp only [sub_zero] at hom
  exact hom

end MasterHAGI

end Hagi
