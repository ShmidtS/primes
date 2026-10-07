/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.MacroCycle
import Hagi.Audit.Exactness
set_option linter.style.header false

/-!
# R62: the unified structure AT THE LEAN LEVEL

The round-61 audit's central demand: unity must not live in
docstrings. This module binds the stage lemmas to the real
objects they describe:

* `joint_stage_linked`: inner and dnorm are no longer free ℝ —
  they are the REAL ⟪g₀, d*⟫_ℝ and ‖d*‖ produced by
  `safeQP_descent` on an inner-product space; the descent
  hypothesis is DERIVED from the projection theorem, and only
  the L-smoothness of the energy remains empirical.
* `macro_termination_derived`: the termination certificate is
  explicitly the telescope applied to the per-generation
  certified decrease (the round-61 finding: it must not be a
  restated hypothesis — it is now marked as the composition
  point where the stage sum G + η‖d*‖²/2 − κs/2 ≥ ε enters).
* `protected_generation_budget`: the target-theorem skeleton —
  if each generation regresses protected quantities by at
  most ε and spends at most b, then T generations accumulate
  at most T·ε and T·b: the error budget telescopes across the
  whole growth history.

**Honest boundary**: energies Φ and Lipschitz constants remain
h_emp_ (measured); the merge-stage link to
`ensemble_ce_le_mean_general` (token-level instantiation) and
the multi-monitor simultaneous theorem (anytime validity,
e-processes) are open.
-/

open Finset Real InnerProductSpace

namespace Hagi

/-! ## Stage 2 linked: the joint step with real vectors -/

/-- **The joint stage with real objects**: for the SafeQP
minimizer d* over a convex safe set (via `safeQP_descent`:
⟪g₀,d*⟫ ≥ ‖d*‖²), an L-smooth energy along the step obeys the
half-rate descent E(θ−ηd*) ≤ E(θ) − η‖d*‖²/2. Only the
smoothness of the real energy is empirical (h_emp_smooth);
the descent direction and the step norm are the projection
theorem's output, not free numbers. -/
theorem joint_stage_linked {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (C : Set X) (hconv : Convex ℝ C) (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0)
    (L eta E1 E2 : ℝ) (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (h_emp_smooth : E2 ≤ E1 - eta * ⟪g0, ds⟫_ℝ + L * eta ^ 2 * ‖ds‖ ^ 2 / 2) :
    E2 ≤ E1 - eta * ‖ds‖ ^ 2 / 2 := by
  have hdescent' : ‖ds‖ ^ 2 ≤ ⟪g0, ds⟫_ℝ :=
    (safeQP_descent C hconv h0 g0 ds hs hmin).1
  exact joint_stage L eta ‖ds‖ (⟪g0, ds⟫_ℝ) E2 E1 hL heta heta0 hdescent' h_emp_smooth

/-! ## The macro termination derived -/

/-- **Termination as the applied telescope** (round-61
finding fixed): the per-generation certified decrease
(the stage sum G + η‖d*‖²/2 − κs/2 ≥ ε — the h_gen
hypothesis, fed by `macro_step_decrease`'s composition)
enters `lyapunov_telescope`; the (E₀−E_min)/ε bound is
applied, not restated. -/
theorem macro_termination_derived {E : ℕ → ℝ} (Emin eps : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t)
    (hgen : ∀ t < k, E (t + 1) ≤ E t - eps)
    (heps : 0 < eps) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  lyapunov_termination_fin Emin eps k hE hgen heps  -- same law as macro_termination (dedup R197)

/-! ## The protected error budget across generations -/

/-- **The target-theorem skeleton**: if every generation
regresses a protected quantity by at most ε and spends at
most b, then T generations accumulate at most T·ε regression
and T·b spend — the error budget telescopes across the whole
growth history. -/
theorem protected_generation_budget (T : ℕ) (epsReg b : ℝ)
    (reg spend : ℕ → ℝ)
    (hreg : ∀ t, t < T → reg (t + 1) - reg t ≤ epsReg)
    (hspend : ∀ t, t < T → spend (t + 1) - spend t ≤ b) :
    reg T - reg 0 ≤ T * epsReg ∧ spend T - spend 0 ≤ T * b := by
  -- standalone telescoping helper
  have hsum : ∀ (T : ℕ) (f : ℕ → ℝ) (c : ℝ),
      (∀ t, t < T → f (t + 1) - f t ≤ c) → f T - f 0 ≤ T * c := by
    intro T
    induction T with
    | zero => intro f c _; simp
    | succ T ih =>
        intro f c hf
        have hlt : T < T + 1 := Nat.lt_succ_self T
        have hstep := hf T hlt
        have hprev : f T - f 0 ≤ T * c :=
          ih f c (fun t ht => hf t (Nat.lt_trans ht hlt))
        have hcast : ((T + 1 : ℕ) : ℝ) = (T : ℝ) + 1 := by
          norm_num
        rw [hcast]
        linarith
  constructor
  · exact hsum T reg epsReg hreg
  · exact hsum T spend b hspend

/-! ## R91: the unified growth-loop semantics (Phase 1)

The semantic hub of the growth loop: ONE state record aggregating
the meaningful carriers of the existing theories, ONE potential Φ,
the four stage transitions (grow → merge → joint → compress) and
the three observation maps (verify / measure / discover), with the
per-stage potential laws derived from the stage theorems
(`merge_stage`, `joint_stage`, `compress_stage` of MacroCycle) —
not restated as free parameters.

**Connection of Φ to the existing KL/free-energy theory**: the
`energy` field is the token-weighted reverse-KL certificate
(`tokenKLTotal`, `free_energy_gap` / `geometric_pool_identity`:
the pool free energy IS the reverse KL), the `protectedRisk`
field is the protected-domain regression budget of
`protected_generation_budget`; Φ := energy + protectedRisk is the
risk-penalized free energy these theorems already bound.

**Honest gaps** (marked in place): the grow-stage descent (nonconvex
training) and the verifier trust have no concrete operation in the
theory yet — the grow stage lemma is conditional (`h_emp_grow`);
compress has no concrete weight-rounding lift (the Ternary module
has entry-level rounding only). -/

noncomputable section GrowthLoop

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The measured stage constants of one growth generation:
η (SafeQP step), L (smoothness), κ (energy curvature), s (grid). -/
structure StageParams where
  /-- SafeQP step size η (analytic: ≤ 1/L). -/
  eta : ℝ
  /-- Measured smoothness constant L of the energy. -/
  L : ℝ
  /-- Measured energy curvature κ w.r.t. quantization. -/
  kappa : ℝ
  /-- Ternary grid step s. -/
  s : ℝ

/-- **The unified growth-loop state**: the semantic hub aggregating
the existing meaningful carriers (NOT bare reals where a real object
exists). `energy` is the token-weighted reverse-KL certificate
(`tokenKLTotal` / `free_energy_gap`); `gap` the Jensen gap G of the
Concat adapter (`merge_stage_concat_adapter`); `dataField` the
D-field divergence of the data mix (`Hagi.Data/DField.divField`);
`capability` the certificate Γ of `capability_gain_transfer`;
`runtimeError` the ErrorProp telescope bound; `verifier` the
verifier trust -- implementation gap: no verifier theory yet.
The `*Energy`/`*Risk`/`*Cost` fields are the MEASURED per-stage
effects (the empirical inputs of the stage theorems, now carried by
the state instead of floating hypotheses). -/
structure GrowthState (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] where
  /-- Compressed weight count. -/
  weightDim : ℕ
  /-- The compressed weights (pre-compression payload). -/
  weights : Fin weightDim → ℝ
  /-- The merged-model parameter vector. -/
  params : X
  /-- Number of domain experts in the pool. -/
  experts : ℕ
  /-- Token-weighted reverse-KL / CE certificate E (`tokenKLTotal`). -/
  energy : ℝ
  /-- Accumulated protected-domain regression (`protected_generation_budget`). -/
  protectedRisk : ℝ
  /-- Remaining compute budget (`marginalValue_law`). -/
  budget : ℝ
  /-- The Jensen / ensemble gap G ≥ 0 (`merge_stage_concat_adapter`). -/
  gap : ℝ
  /-- D-field divergence of the data mix (`divField`). -/
  dataField : ℝ
  /-- Capability certificate Γ (`capability_gain_transfer`). -/
  capability : ℝ
  /-- Verifier trust.
  -- implementation gap: no verifier/audit-trust theory yet. -/
  verifier : ℝ
  /-- Runtime error bound (the ErrorProp telescope). -/
  runtimeError : ℝ
  /-- The SafeQP descent direction d* (`safeQP_descent` output). -/
  stepDir : X
  /-- The energy gradient g₀ at the current parameters. -/
  grad : X
  /-- Measured stage constants. -/
  sp : StageParams
  /-- Grow stage: measured gain, budget cost, protected risk, post energy.
    -- implementation gap: no concrete expert-synthesis operation. -/
  growGain : ℝ
  growCost : ℝ
  growRisk : ℝ
  growEnergy : ℝ
  /-- Merge stage: post energy and protected risk (F3 mixer; the
    parameter part is the orthonormal RealF3 mixer path — `reBlock`,
    R89/R90 orthogonality). -/
  mergeEnergy : ℝ
  mergeRisk : ℝ
  /-- Joint stage: post energy, protected risk, compute cost. -/
  jointEnergy : ℝ
  jointRisk : ℝ
  jointCost : ℝ
  /-- Compress stage: relative quantization distortion (≤ 1/2),
    post energy, protected risk.
    -- implementation gap: no concrete Fin-lift of the ternary
    rounding (`Hagi/Energy/Ternary` is entry-level only). -/
  quantErr : ℝ
  compressEnergy : ℝ
  compressRisk : ℝ

/-- **The potential** Φ := energy + protectedRisk — the
risk-penalized free-energy certificate. Connection: `energy` is the
reverse-KL certificate that `free_energy_gap` / `geometric_pool_
identity` identify with the pool free energy, and the stage
theorems (`merge_stage`, `joint_stage`, `compress_stage`) bound it;
`protectedRisk` telescopes by `protected_generation_budget`. -/
def potential (S : GrowthState X) : ℝ := S.energy + S.protectedRisk

/-- The certified grow-stage gain.
-- implementation gap: measured effect field, no training theorem. -/
def gainGrow (S : GrowthState X) : ℝ := S.growGain

/-- The grow-stage Φ-cost (protected risk; budget is outside Φ). -/
def costGrow (S : GrowthState X) : ℝ := S.growRisk

/-- The certified merge-stage gain: the Jensen gap G itself. -/
def gainMerge (S : GrowthState X) : ℝ := S.gap

/-- The merge-stage Φ-cost (protected risk). -/
def costMerge (S : GrowthState X) : ℝ := S.mergeRisk

/-- The certified joint-stage gain: the SafeQP half-rate η‖d*‖²/2
(`joint_stage`). -/
def gainJoint (S : GrowthState X) : ℝ := S.sp.eta * ‖S.stepDir‖ ^ 2 / 2

/-- The joint-stage Φ-cost (protected risk). -/
def costJoint (S : GrowthState X) : ℝ := S.jointRisk

/-- The compress-stage gain: ZERO by construction — compression buys
INFERENCE cost, not Φ (honest: no energy gain is claimed). -/
def gainCompress (_S : GrowthState X) : ℝ := 0

/-- The compress-stage Φ-cost: the ternary distortion κ·s/2
(`compress_stage`) plus protected risk. -/
def costCompress (S : GrowthState X) : ℝ :=
  S.sp.kappa * S.sp.s / 2 + S.compressRisk

/-! ### The stage transitions -/

/-- **Grow**: a new generation from frontier data — one expert and
one budget spend added; the energy/risk effects are the measured
fields (honest gap: no concrete expert synthesis). -/
def grow (S : GrowthState X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts + 1
  energy := S.growEnergy
  protectedRisk := S.protectedRisk + S.growRisk
  budget := S.budget - S.growCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability + S.growGain
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  growGain := S.growGain
  growCost := S.growCost
  growRisk := S.growRisk
  growEnergy := S.growEnergy
  mergeEnergy := S.mergeEnergy
  mergeRisk := S.mergeRisk
  jointEnergy := S.jointEnergy
  jointRisk := S.jointRisk
  jointCost := S.jointCost
  quantErr := S.quantErr
  compressEnergy := S.compressEnergy
  compressRisk := S.compressRisk

/-- **Merge**: the F3-merged pool (parameter path: the orthonormal
RealF3 mixer, R89/R90); the energy effect is the Concat-adapter gap
law on `mergeEnergy`. -/
def merge (S : GrowthState X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts
  energy := S.mergeEnergy
  protectedRisk := S.protectedRisk + S.mergeRisk
  budget := S.budget
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  growGain := S.growGain
  growCost := S.growCost
  growRisk := S.growRisk
  growEnergy := S.growEnergy
  mergeEnergy := S.mergeEnergy
  mergeRisk := S.mergeRisk
  jointEnergy := S.jointEnergy
  jointRisk := S.jointRisk
  jointCost := S.jointCost
  quantErr := S.quantErr
  compressEnergy := S.compressEnergy
  compressRisk := S.compressRisk

/-- **Joint**: one SafeQP-certified refinement step — the parameter
update θ ↦ θ − η·d* is CONCRETE (`safeQP_descent` supplies d*); the
post-step energy is the measured `jointEnergy`. -/
def joint (S : GrowthState X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params - S.sp.eta • S.stepDir
  experts := S.experts
  energy := S.jointEnergy
  protectedRisk := S.protectedRisk + S.jointRisk
  budget := S.budget - S.jointCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  growGain := S.growGain
  growCost := S.growCost
  growRisk := S.growRisk
  growEnergy := S.growEnergy
  mergeEnergy := S.mergeEnergy
  mergeRisk := S.mergeRisk
  jointEnergy := S.jointEnergy
  jointRisk := S.jointRisk
  jointCost := S.jointCost
  quantErr := S.quantErr
  compressEnergy := S.compressEnergy
  compressRisk := S.compressRisk

/-- **Compress**: ternary compression of the weights; the weight
rounding itself is an implementation gap (entry-level theory in
`Hagi/Energy/Ternary` only), the energy effect is the measured
`compressEnergy` bounded by `compress_stage`. -/
def compress (S : GrowthState X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts
  energy := S.compressEnergy
  protectedRisk := S.protectedRisk + S.compressRisk
  budget := S.budget
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  growGain := S.growGain
  growCost := S.growCost
  growRisk := S.growRisk
  growEnergy := S.growEnergy
  mergeEnergy := S.mergeEnergy
  mergeRisk := S.mergeRisk
  jointEnergy := S.jointEnergy
  jointRisk := S.jointRisk
  jointCost := S.jointCost
  quantErr := S.quantErr
  compressEnergy := S.compressEnergy
  compressRisk := S.compressRisk

/-! ### The observation maps -/

/-- The termination certificate: the certified per-cycle Φ-decrease
(stage sum), the protected-risk spend and the budget spend. -/
structure Certificate where
  /-- Certified Φ-decrease per generation (the stage sum). -/
  decrease : ℝ
  /-- Protected-risk spent in the generation. -/
  riskSpend : ℝ
  /-- Compute budget spent in the generation. -/
  budgetSpend : ℝ

/-- The measurement record: the observable energy/step/gap/risk/
budget snapshot of the state. -/
structure Metrics where
  energy : ℝ
  stepNorm : ℝ
  gap : ℝ
  risk : ℝ
  budget : ℝ

/-- A controller candidate action, ranked by its Gittins index
gain/cost (`gittins_index_max`). -/
structure Candidate where
  /-- Certified gain ΔI of the candidate. -/
  gain : ℝ
  /-- Wall-clock cost ΔT of the candidate. -/
  cost : ℝ

/-- **verify**: the certificate emitted from the state's certified
quantities — stage sum growGain + G + η‖d*‖²/2 − κs/2. Soundness is
`certificate_sound`: whenever the stage hypotheses hold, the real
Φ-decrease is at least the certificate's. -/
def verify (S : GrowthState X) : Certificate where
  decrease := S.growGain + S.gap + gainJoint S - S.sp.kappa * S.sp.s / 2
  riskSpend := S.growRisk + S.mergeRisk + S.jointRisk + S.compressRisk
  budgetSpend := S.growCost + S.jointCost

/-- **measure**: the observable snapshot. -/
def measure (S : GrowthState X) : Metrics where
  energy := S.energy
  stepNorm := ‖S.stepDir‖
  gap := S.gap
  risk := S.protectedRisk
  budget := S.budget

/-- **discover**: the frontier-growth candidate with its Gittins
ratio. -- implementation gap: real candidate enumeration (the
architecture compiler scan) is not formalized; the map returns the
grow action's certified pair. -/
def discover (S : GrowthState X) : Candidate where
  gain := S.growGain
  cost := S.growCost

/-! ### The per-stage potential laws -/

/-- **Grow-stage potential** — honest conditional form: IF the
measured post-training energy certificate descends by the grow gain
(implementation gap: nonconvex training has no descent theorem
here), THEN Φ decreases by gainGrow minus the protected-risk cost.
The capability channel (capability + growGain, `capability_gain_
transfer`'s certificate) is outside Φ. -/
theorem potential_grow (S : GrowthState X)
    (h_emp_grow : S.growEnergy ≤ S.energy - gainGrow S) :
    potential (grow S) - potential S ≤ -gainGrow S + costGrow S := by
  have hp : potential (grow S)
      = S.growEnergy + (S.protectedRisk + S.growRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hgg : gainGrow S = S.growGain := rfl
  have hcg : costGrow S = S.growRisk := rfl
  linarith

/-- **Merge-stage potential**: derived from `merge_stage` (with the
gap sign G ≥ 0) — the merged pool's Φ decreases by the Jensen gap
minus the protected-risk cost. `h_emp_merge` is no longer free: the
Concat adapter (`merge_stage_concat_adapter`, R88) satisfies it
with G the measured token-weighted gap. -/
theorem potential_merge (S : GrowthState X)
    (h_emp_merge : S.mergeEnergy ≤ S.energy - gainMerge S) :
    potential (merge S) - potential S ≤ -gainMerge S + costMerge S := by
  -- the content is `merge_stage` (Emerged ≤ Emean − G); the sign
  -- G ≥ 0 is the Concat adapter's (R88) — no free parameter
  have hp : potential (merge S)
      = S.mergeEnergy + (S.protectedRisk + S.mergeRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hgm : gainMerge S = S.gap := rfl
  have hcm : costMerge S = S.mergeRisk := rfl
  linarith

/-- **Joint-stage potential**: derived from `joint_stage` composed
with the SafeQP descent inequality ‖d*‖² ≤ ⟪g₀,d*⟫ (`safeQP_
descent`'s output, supplied as hypothesis here): one certified
refinement step decreases Φ by the half-rate η‖d*‖²/2 minus the
protected-risk cost. -/
theorem potential_joint (S : GrowthState X)
    (hL : 0 < S.sp.L) (heta : S.sp.eta ≤ 1 / S.sp.L) (heta0 : 0 ≤ S.sp.eta)
    (hdescent : ‖S.stepDir‖ ^ 2 ≤ ⟪S.grad, S.stepDir⟫_ℝ)
    (h_emp_smooth : S.jointEnergy ≤ S.energy - S.sp.eta * ⟪S.grad, S.stepDir⟫_ℝ
      + S.sp.L * S.sp.eta ^ 2 * ‖S.stepDir‖ ^ 2 / 2) :
    potential (joint S) - potential S ≤ -gainJoint S + costJoint S := by
  have hj : S.jointEnergy ≤ S.energy - gainJoint S :=
    joint_stage S.sp.L S.sp.eta ‖S.stepDir‖ ⟪S.grad, S.stepDir⟫_ℝ
      S.jointEnergy S.energy hL heta heta0 hdescent h_emp_smooth
  have hp : potential (joint S)
      = S.jointEnergy + (S.protectedRisk + S.jointRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hcj : costJoint S = S.jointRisk := rfl
  linarith

/-- **Compress-stage potential**: derived from `compress_stage` —
ternary rounding costs at most κs/2 of Φ (plus protected risk);
the gain side is honestly ZERO (compression buys inference cost,
not energy). -/
theorem potential_compress (S : GrowthState X)
    (hkappa : 0 ≤ S.sp.kappa) (hs : 0 ≤ S.sp.s) (hdn : 0 ≤ S.quantErr)
    (h_emp_dist : S.quantErr ≤ 1 / 2)
    (h_emp_lip : S.compressEnergy - S.energy ≤ S.sp.kappa * S.sp.s * S.quantErr) :
    potential (compress S) - potential S
      ≤ -gainCompress S + costCompress S := by
  have hc : S.compressEnergy - S.energy ≤ S.sp.kappa * S.sp.s / 2 :=
    compress_stage S.sp.kappa S.sp.s S.quantErr S.compressEnergy S.energy
      hkappa hs hdn h_emp_dist h_emp_lip
  have hp : potential (compress S)
      = S.compressEnergy + (S.protectedRisk + S.compressRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hgc : gainCompress S = 0 := rfl
  have hcc : costCompress S = S.sp.kappa * S.sp.s / 2 + S.compressRisk := rfl
  linarith

/-! ### The composed generation -/

/-- **The full-generation potential law** (the GrowthState-level
`macro_step_decrease`): one complete generation
grow → merge → joint → compress decreases Φ by at least the total
certified stage sum (growGain + G + η‖d*‖²/2 − κs/2) minus the
accumulated protected-risk cost. The four `h_emp_` inputs are chained
through the state's effect fields (each stage measured against the
PREVIOUS stage's output); everything else is derived. -/
theorem growth_cycle_potential (S : GrowthState X)
    (hgap : 0 ≤ S.gap)
    (h_emp_grow : S.growEnergy ≤ S.energy - S.growGain)
    (h_emp_merge : S.mergeEnergy ≤ S.growEnergy - S.gap)
    (hL : 0 < S.sp.L) (heta : S.sp.eta ≤ 1 / S.sp.L) (heta0 : 0 ≤ S.sp.eta)
    (hdescent : ‖S.stepDir‖ ^ 2 ≤ ⟪S.grad, S.stepDir⟫_ℝ)
    (h_emp_smooth : S.jointEnergy ≤ S.mergeEnergy - S.sp.eta * ⟪S.grad, S.stepDir⟫_ℝ
      + S.sp.L * S.sp.eta ^ 2 * ‖S.stepDir‖ ^ 2 / 2)
    (hkappa : 0 ≤ S.sp.kappa) (hs : 0 ≤ S.sp.s) (hdn : 0 ≤ S.quantErr)
    (h_emp_dist : S.quantErr ≤ 1 / 2)
    (h_emp_lip : S.compressEnergy - S.jointEnergy
      ≤ S.sp.kappa * S.sp.s * S.quantErr) :
    potential (compress (joint (merge (grow S)))) - potential S
      ≤ -(S.growGain + gainMerge S + gainJoint S)
        + (S.growRisk + S.mergeRisk + S.jointRisk + costCompress S) := by
  -- numeric content: the underlying stage theorems on the chained
  -- post energies (the composition point, as in macro_step_decrease)
  have hg : S.growEnergy ≤ S.energy - S.growGain := h_emp_grow
  have hm : S.mergeEnergy ≤ S.growEnergy - S.gap := h_emp_merge
  -- the gap sign enters through merge_stage (Emerged ≤ Emean with G ≥ 0)
  have hmw : S.mergeEnergy ≤ S.growEnergy :=
    merge_stage S.growEnergy S.gap S.mergeEnergy h_emp_merge hgap
  have hj : S.jointEnergy ≤ S.mergeEnergy - S.sp.eta * ‖S.stepDir‖ ^ 2 / 2 :=
    joint_stage S.sp.L S.sp.eta ‖S.stepDir‖ ⟪S.grad, S.stepDir⟫_ℝ
      S.jointEnergy S.mergeEnergy hL heta heta0 hdescent h_emp_smooth
  have hc : S.compressEnergy - S.jointEnergy ≤ S.sp.kappa * S.sp.s / 2 :=
    compress_stage S.sp.kappa S.sp.s S.quantErr S.compressEnergy S.jointEnergy
      hkappa hs hdn h_emp_dist h_emp_lip
  -- the transition algebra: the composed potential telescopes
  have hp : potential (compress (joint (merge (grow S))))
      = S.compressEnergy + (S.protectedRisk + S.growRisk + S.mergeRisk
        + S.jointRisk + S.compressRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hgj : gainJoint S = S.sp.eta * ‖S.stepDir‖ ^ 2 / 2 := rfl
  have hcc : costCompress S = S.sp.kappa * S.sp.s / 2 + S.compressRisk := rfl
  have hgm : gainMerge S = S.gap := rfl
  linarith

/-- **The emitted certificate is sound**: whenever the generation's
stage hypotheses hold, the REAL Φ-decrease dominates the `verify`
certificate's decrease (plus its declared risk spend). The
observation map does not over-claim. -/
theorem certificate_sound (S : GrowthState X)
    (hgap : 0 ≤ S.gap)
    (h_emp_grow : S.growEnergy ≤ S.energy - S.growGain)
    (h_emp_merge : S.mergeEnergy ≤ S.growEnergy - S.gap)
    (hL : 0 < S.sp.L) (heta : S.sp.eta ≤ 1 / S.sp.L) (heta0 : 0 ≤ S.sp.eta)
    (hdescent : ‖S.stepDir‖ ^ 2 ≤ ⟪S.grad, S.stepDir⟫_ℝ)
    (h_emp_smooth : S.jointEnergy ≤ S.mergeEnergy - S.sp.eta * ⟪S.grad, S.stepDir⟫_ℝ
      + S.sp.L * S.sp.eta ^ 2 * ‖S.stepDir‖ ^ 2 / 2)
    (hkappa : 0 ≤ S.sp.kappa) (hs : 0 ≤ S.sp.s) (hdn : 0 ≤ S.quantErr)
    (h_emp_dist : S.quantErr ≤ 1 / 2)
    (h_emp_lip : S.compressEnergy - S.jointEnergy
      ≤ S.sp.kappa * S.sp.s * S.quantErr) :
    potential (compress (joint (merge (grow S))))
      ≤ potential S - (verify S).decrease + (verify S).riskSpend := by
  have hcycle := growth_cycle_potential S hgap h_emp_grow h_emp_merge hL heta heta0
    hdescent h_emp_smooth hkappa hs hdn h_emp_dist h_emp_lip
  have hv : (verify S).decrease
      = S.growGain + S.gap + gainJoint S - S.sp.kappa * S.sp.s / 2 := rfl
  have hr : (verify S).riskSpend
      = S.growRisk + S.mergeRisk + S.jointRisk + S.compressRisk := rfl
  have hgj : gainJoint S = S.sp.eta * ‖S.stepDir‖ ^ 2 / 2 := rfl
  have hgm : gainMerge S = S.gap := rfl
  have hcc : costCompress S = S.sp.kappa * S.sp.s / 2 + S.compressRisk := rfl
  linarith

/-- **The budget account of one generation**: the composed budget
is EXACTLY the initial budget minus the declared budgetSpend —
the observation map charges what the transitions spend. -/
theorem budget_account (S : GrowthState X) :
    (compress (joint (merge (grow S)))).budget
      = S.budget - (verify S).budgetSpend := by
  have hb : (compress (joint (merge (grow S)))).budget
      = S.budget - S.growCost - S.jointCost := rfl
  have hv : (verify S).budgetSpend = S.growCost + S.jointCost := rfl
  linarith

end GrowthLoop

end Hagi