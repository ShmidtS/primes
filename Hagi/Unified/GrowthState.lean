/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Unified.MacroCycle
import Hagi.Step.ProjectionDescent
set_option linter.style.header false

/-!
# The unified growth-loop structure

`joint_stage_linked`: the joint-stage descent with the real
inner product and norm from `safeQP_descent`; only smoothness
is h_emp_. `macro_termination_derived`: the Lyapunov telescope
applied to the per-generation certified decrease.
`protected_generation_budget`: per-generation regression ≤ ε
and spend ≤ b accumulate to at most `T·ε` and `T·b` over `T`
generations.

The `GrowthLoop` section below defines the growth-loop state,
the potential `Φ = energy + protectedRisk`, the four stage
transitions, and per-stage/composed potential laws derived
from the MacroCycle stage theorems. Grow-stage descent and
compress-stage weight-rounding lifts remain h_emp_ inputs.
-/

open Finset Real InnerProductSpace

namespace Hagi.Unified

/-! ## Stage 2 linked: the joint step with real vectors -/

/-- With `ds` the minimizer of the distance to `g0` over a
convex set (so `‖ds‖² ≤ ⟪g0, ds⟫` by `safeQP_descent`),
`0 < L`, `0 ≤ eta ≤ 1/L`, and the smoothness premise
(h_emp_), `E2 ≤ E1 − eta * ‖ds‖² / 2`. -/
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

/-- If `Emin ≤ E t` for `t ≤ k` and each generation decreases
`E` by at least `eps > 0`, then
`k ≤ (E 0 − Emin) / eps` (delegation to
`lyapunov_termination_fin`). -/
theorem macro_termination_derived {E : ℕ → ℝ} (Emin eps : ℝ) (k : ℕ)
    (hE : ∀ t ≤ k, Emin ≤ E t)
    (hgen : ∀ t < k, E (t + 1) ≤ E t - eps)
    (heps : 0 < eps) :
    (k : ℝ) ≤ (E 0 - Emin) / eps :=
  lyapunov_termination_fin Emin eps k hE hgen heps  -- same law as macro_termination (dedup R197)

/-! ## The protected error budget across generations -/

/-- If `reg (t+1) − reg t ≤ epsReg` and
`spend (t+1) − spend t ≤ b` for all `t < T`, then
`reg T − reg 0 ≤ T * epsReg` and `spend T − spend 0 ≤ T * b`. -/
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

/-! ## The growth-loop semantics

The state record `GrowthState` with the potential
`Φ = energy + protectedRisk` (energy = the token-weighted
reverse-KL certificate; protectedRisk = the protected-domain
regression budget), the four stage transitions, and the
observation maps verify / measure / discover. The per-stage
potential laws derive from the MacroCycle stage theorems.
Grow-stage descent and the compress rounding lift remain
h_emp_ inputs (no training or verifier theorem here). -/

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

/-- The growth-loop state: weights, parameters, expert count,
the measured energy (token-weighted reverse-KL certificate),
protected risk, budget, the Jensen gap, and the measured
per-stage energy/risk/cost effect fields (the h_emp_ inputs of
the stage theorems). -/
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

/-- The potential `Φ := energy + protectedRisk`. -/
def potential (S : GrowthState X) : ℝ := S.energy + S.protectedRisk

/-- The certified grow-stage gain (measured field; no
training theorem backs it). -/
def gainGrow (S : GrowthState X) : ℝ := S.growGain

/-- The grow-stage Φ-cost (protected risk; budget is outside Φ). -/
def costGrow (S : GrowthState X) : ℝ := S.growRisk

/-- The certified merge-stage gain: the Jensen gap G itself. -/
def gainMerge (S : GrowthState X) : ℝ := S.gap

/-- The merge-stage Φ-cost (protected risk). -/
def costMerge (S : GrowthState X) : ℝ := S.mergeRisk

/-- The joint-stage gain `eta * ‖stepDir‖² / 2`. -/
def gainJoint (S : GrowthState X) : ℝ := S.sp.eta * ‖S.stepDir‖ ^ 2 / 2

/-- The joint-stage Φ-cost (protected risk). -/
def costJoint (S : GrowthState X) : ℝ := S.jointRisk

/-- The compress-stage gain: zero (no energy gain claimed). -/
def gainCompress (_S : GrowthState X) : ℝ := 0

/-- The compress-stage cost `kappa * s / 2 + compressRisk`. -/
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

/-- If the measured grow-stage energy descends by the gain
(h_emp_grow), then Φ decreases by at least
`gainGrow − costGrow`. -/
theorem potential_grow (S : GrowthState X)
    (h_emp_grow : S.growEnergy ≤ S.energy - gainGrow S) :
    potential (grow S) - potential S ≤ -gainGrow S + costGrow S := by
  have hp : potential (grow S)
      = S.growEnergy + (S.protectedRisk + S.growRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hgg : gainGrow S = S.growGain := rfl
  have hcg : costGrow S = S.growRisk := rfl
  linarith

/-- If the measured merge-stage energy descends by the gap
(h_emp_merge), then Φ decreases by at least
`gainMerge − costMerge`. -/
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

/-- With `0 < L`, `0 ≤ eta ≤ 1/L`, the SafeQP descent
hypothesis, and the smoothness premise (h_emp_), Φ decreases
by at least `gainJoint − costJoint`. -/
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

/-- With the compress-stage premises (h_emp_ distortion and
Lipschitz bounds), Φ increases by at most
`costCompress` (gain side zero). -/
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

/-- Under the chained stage premises (h_emp_ per stage, measured
against the previous stage's output), one full generation
grow → merge → joint → compress satisfies
`Φ' − Φ ≤ −(growGain + gap + eta·‖stepDir‖²/2) +
(growRisk + mergeRisk + jointRisk + costCompress)`. -/
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

/-- Under the same stage premises as `growth_cycle_potential`,
the real Φ-decrease dominates the `verify` certificate's
`decrease` minus its declared `riskSpend`. -/
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

/-- The composed budget after one generation equals
`S.budget − (verify S).budgetSpend`. -/
theorem budget_account (S : GrowthState X) :
    (compress (joint (merge (grow S)))).budget
      = S.budget - (verify S).budgetSpend := by
  have hb : (compress (joint (merge (grow S)))).budget
      = S.budget - S.growCost - S.jointCost := rfl
  have hv : (verify S).budgetSpend = S.growCost + S.jointCost := rfl
  linarith

end GrowthLoop

end Hagi.Unified
namespace Hagi
export Hagi.Unified (joint_stage_linked macro_termination_derived protected_generation_budget StageParams GrowthState potential gainGrow costGrow gainMerge costMerge gainJoint costJoint gainCompress costCompress grow merge joint compress Certificate Metrics Candidate verify measure discover potential_grow potential_merge potential_joint potential_compress growth_cycle_potential certificate_sound budget_account)
end Hagi
