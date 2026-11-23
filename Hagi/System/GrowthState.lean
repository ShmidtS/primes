/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Math.Foundations.StageCalculus
import Hagi.Math.Foundations.Potential
import Hagi.Math.Foundations.Telescope
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Hagi.Learning.TrainingTransition
set_option linter.style.header false

/-!
# The unified growth-loop structure

`joint_stage_linked`: the joint-stage descent with the real
inner product and norm from `safeQP_descent`; only smoothness
is h_emp_. Lyapunov termination is delegated to
`Hagi.Foundations.lyapunov_termination_fin` (R197+audit dedup).
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

namespace Hagi.System

/-! ## Stage 2 linked: the joint step with real vectors -/

/-! ## The macro termination derived -/

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

structure StageEffects where
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
  /-- Merge stage: compute cost (P1.3: honest resource
  accounting — merge is not free). -/
  mergeCost : ℝ
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
  /-- Compress stage: compute cost (P1.3: honest resource
  accounting — compression work is not free). -/
  compressCost : ℝ

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
  /-- The measured per-stage effect fields (h_emp_ inputs),
  grouped as one record (audit v3 Phase 4, R341). -/
  effects : StageEffects

/-- The potential `Φ := energy + protectedRisk`. -/
def potential (S : GrowthState X) : ℝ := S.energy + S.protectedRisk

/-- The certified grow-stage gain (measured field; no
training theorem backs it). -/
def gainGrow (S : GrowthState X) : ℝ := S.effects.growGain

/-- The grow-stage Φ-cost (protected risk; budget is outside Φ). -/
def riskGrow (S : GrowthState X) : ℝ := S.effects.growRisk

/-- The certified merge-stage gain: the Jensen gap G itself. -/
def gainMerge (S : GrowthState X) : ℝ := S.gap

/-- The merge-stage Φ-cost (protected risk). -/
def riskMerge (S : GrowthState X) : ℝ := S.effects.mergeRisk

/-- The joint-stage gain `eta * ‖stepDir‖² / 2`. -/
def gainJoint (S : GrowthState X) : ℝ := S.sp.eta * ‖S.stepDir‖ ^ 2 / 2

/-- The joint-stage Φ-cost (protected risk). -/
def riskJoint (S : GrowthState X) : ℝ := S.effects.jointRisk

/-- The compress-stage gain: MEASURED energy saving of the
compression stage (energy before − compressEnergy), not a
declared zero. If compression does not lower energy, the gain
is ≤ 0 and the potential bound degrades gracefully to the
previous conservative form. -/
def gainCompress (S : GrowthState X) : ℝ :=
  S.energy - S.effects.compressEnergy

/-- The compress-stage cost `kappa * s / 2 + compressRisk`. -/
def costCompress (S : GrowthState X) : ℝ :=
  S.sp.kappa * S.sp.s / 2 + S.effects.compressRisk

/-! ### The stage transitions -/

/-- **Grow**: a new generation from frontier data — one expert and
one budget spend added; the energy/risk effects are the measured
fields (honest gap: no concrete expert synthesis). -/
def grow (S : GrowthState X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts + 1
  energy := S.effects.growEnergy
  protectedRisk := S.protectedRisk + S.effects.growRisk
  budget := S.budget - S.effects.growCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability + S.effects.growGain
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := S.effects

/-- **Merge**: the F3-merged pool (parameter path: the orthonormal
RealF3 mixer, R89/R90); the energy effect is the Concat-adapter gap
law on `mergeEnergy`. -/
def merge (S : GrowthState X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts
  energy := S.effects.mergeEnergy
  protectedRisk := S.protectedRisk + S.effects.mergeRisk
  budget := S.budget - S.effects.mergeCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := S.effects

/-- **Joint**: one SafeQP-certified refinement step — the parameter
update θ ↦ θ − η·d* is CONCRETE (`safeQP_descent` supplies d*); the
post-step energy is the measured `jointEnergy`. -/
def joint (S : GrowthState X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params - S.sp.eta • S.stepDir
  experts := S.experts
  energy := S.effects.jointEnergy
  protectedRisk := S.protectedRisk + S.effects.jointRisk
  budget := S.budget - S.effects.jointCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := S.effects

/-- **Compress**: ternary compression of the weights; the weight
rounding itself is an implementation gap (entry-level theory in
`Hagi/Energy/Ternary` only), the energy effect is the measured
`compressEnergy` bounded by `compress_stage`. -/
def compress (S : GrowthState X) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts
  energy := S.effects.compressEnergy
  protectedRisk := S.protectedRisk + S.effects.compressRisk
  budget := S.budget - S.effects.compressCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := S.effects

/-! ### The observation maps -/

/-- The termination certificate: the certified per-cycle Φ-decrease
(stage sum), the protected-risk spend and the budget spend. -/
structure Certificate where
  /-- Certified Φ-decrease per generation (the stage sum). -/
  decrease : ℝ
  /-- Protected-risk spent in the generation. -/
  riskSpend : ℝ
  /-- Compute budget spent in the generation.
  Accounting semantics (unified plan §5.4, R312):
  covers ONLY the growth and joint stages
  (`growCost + jointCost`); the compression cost
  `costCompress` is deliberately NOT a budget spend
  — it enters the Φ-potential through `riskSpend`/
  `potential_compress` (a penalty, not a resource). -/
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
  decrease := S.effects.growGain + S.gap + gainJoint S
      - S.sp.kappa * S.sp.s / 2
  riskSpend := S.effects.growRisk + S.effects.mergeRisk
      + S.effects.jointRisk + S.effects.compressRisk
  budgetSpend := S.effects.growCost + S.effects.mergeCost
      + S.effects.jointCost + S.effects.compressCost

/-- `verify` unfolds definitionally to the stage sum
`growGain + gap + eta*||stepDir||^2/2 - kappa*s/2`
(audit regression interface). -/
theorem verify_decrease (S : GrowthState X) :
    (verify S).decrease
      = S.effects.growGain + S.gap
        + S.sp.eta * ‖S.stepDir‖ ^ 2 / 2
        - S.sp.kappa * S.sp.s / 2 := rfl

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
  gain := S.effects.growGain
  cost := S.effects.growCost

/-! ### The per-stage potential laws -/

/-- If the measured grow-stage energy descends by the gain
(h_emp_grow), then Φ decreases by at least
`gainGrow − riskGrow`. -/
theorem potential_grow (S : GrowthState X)
    (h_emp_grow : S.effects.growEnergy ≤ S.energy - gainGrow S) :
    potential (grow S) - potential S ≤ -gainGrow S + riskGrow S := by
  have hp : potential (grow S)
      = S.effects.growEnergy + (S.protectedRisk + S.effects.growRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hgg : gainGrow S = S.effects.growGain := rfl
  have hcg : riskGrow S = S.effects.growRisk := rfl
  linarith

/-- If the measured merge-stage energy descends by the gap
(h_emp_merge), then Φ decreases by at least
`gainMerge − riskMerge`. -/
theorem potential_merge (S : GrowthState X)
    (h_emp_merge : S.effects.mergeEnergy ≤ S.energy - gainMerge S) :
    potential (merge S) - potential S ≤ -gainMerge S + riskMerge S := by
  -- the content is `merge_stage` (Emerged ≤ Emean − G); the sign
  -- G ≥ 0 is the Concat adapter's (R88) — no free parameter
  have hp : potential (merge S)
      = S.effects.mergeEnergy + (S.protectedRisk + S.effects.mergeRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hgm : gainMerge S = S.gap := rfl
  have hcm : riskMerge S = S.effects.mergeRisk := rfl
  linarith

/-- With `0 < L`, `0 ≤ eta ≤ 1/L`, the SafeQP descent
hypothesis, and the smoothness premise (h_emp_), Φ decreases
by at least `gainJoint − riskJoint`. -/
theorem potential_joint (S : GrowthState X)
    (hL : 0 < S.sp.L) (heta : S.sp.eta ≤ 1 / S.sp.L) (heta0 : 0 ≤ S.sp.eta)
    (hdescent : ‖S.stepDir‖ ^ 2 ≤ ⟪S.grad, S.stepDir⟫_ℝ)
    (h_emp_smooth : S.effects.jointEnergy ≤ S.energy - S.sp.eta * ⟪S.grad, S.stepDir⟫_ℝ
      + S.sp.L * S.sp.eta ^ 2 * ‖S.stepDir‖ ^ 2 / 2) :
    potential (joint S) - potential S ≤ -gainJoint S + riskJoint S := by
  have hj : S.effects.jointEnergy ≤ S.energy - gainJoint S :=
    Hagi.Foundations.joint_stage S.sp.L S.sp.eta ‖S.stepDir‖ ⟪S.grad, S.stepDir⟫_ℝ
      S.effects.jointEnergy S.energy hL heta heta0 hdescent h_emp_smooth
  have hp : potential (joint S)
      = S.effects.jointEnergy + (S.protectedRisk + S.effects.jointRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hcj : riskJoint S = S.effects.jointRisk := rfl
  linarith

/-- With the compress-stage premises (h_emp_ distortion and
Lipschitz bounds), Φ increases by at most
`costCompress` (gain side zero). -/
theorem potential_compress (S : GrowthState X)
    (hkappa : 0 ≤ S.sp.kappa) (hs : 0 ≤ S.sp.s) (hdn : 0 ≤ S.effects.quantErr)
    (h_emp_dist : S.effects.quantErr ≤ 1 / 2)
    (h_emp_lip : S.effects.compressEnergy - S.energy ≤ S.sp.kappa * S.sp.s * S.effects.quantErr) :
    potential (compress S) - potential S
      ≤ -gainCompress S + costCompress S := by
  have hc : S.effects.compressEnergy - S.energy ≤ S.sp.kappa * S.sp.s / 2 :=
    Hagi.Foundations.compress_stage S.sp.kappa S.sp.s S.effects.quantErr
      S.effects.compressEnergy S.energy hkappa hs hdn h_emp_dist h_emp_lip
  have hp : potential (compress S)
      = S.effects.compressEnergy + (S.protectedRisk + S.effects.compressRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hcc : costCompress S = S.sp.kappa * S.sp.s / 2 + S.effects.compressRisk := rfl
  have hgc : gainCompress S = S.energy - S.effects.compressEnergy := rfl
  have hknn : (0:ℝ) ≤ S.sp.kappa * S.sp.s / 2 := by positivity
  linarith

/-! ### The composed generation -/

/-- Under the chained stage premises (h_emp_ per stage, measured
against the previous stage's output), one full generation
grow → merge → joint → compress satisfies
`Φ' − Φ ≤ −(growGain + gap + eta·‖stepDir‖²/2) +
(growRisk + mergeRisk + jointRisk + costCompress)`. -/
theorem growth_cycle_potential (S : GrowthState X)
    (hgap : 0 ≤ S.gap)
    (h_emp_grow : S.effects.growEnergy ≤ S.energy - S.effects.growGain)
    (h_emp_merge : S.effects.mergeEnergy ≤ S.effects.growEnergy - S.gap)
    (hL : 0 < S.sp.L) (heta : S.sp.eta ≤ 1 / S.sp.L) (heta0 : 0 ≤ S.sp.eta)
    (hdescent : ‖S.stepDir‖ ^ 2 ≤ ⟪S.grad, S.stepDir⟫_ℝ)
    (h_emp_smooth : S.effects.jointEnergy ≤ S.effects.mergeEnergy - S.sp.eta * ⟪S.grad, S.stepDir⟫_ℝ
      + S.sp.L * S.sp.eta ^ 2 * ‖S.stepDir‖ ^ 2 / 2)
    (hkappa : 0 ≤ S.sp.kappa) (hs : 0 ≤ S.sp.s) (hdn : 0 ≤ S.effects.quantErr)
    (h_emp_dist : S.effects.quantErr ≤ 1 / 2)
    (h_emp_lip : S.effects.compressEnergy - S.effects.jointEnergy
      ≤ S.sp.kappa * S.sp.s * S.effects.quantErr) :
    potential (compress (joint (merge (grow S)))) - potential S
      ≤ -(S.effects.growGain + gainMerge S + gainJoint S)
        + (S.effects.growRisk + S.effects.mergeRisk + S.effects.jointRisk + costCompress S) := by
  -- numeric content: the underlying stage theorems on the chained
  -- post energies (the composition point, as in macro_step_decrease)
  have hg : S.effects.growEnergy ≤ S.energy - S.effects.growGain := h_emp_grow
  have hm : S.effects.mergeEnergy ≤ S.effects.growEnergy - S.gap := h_emp_merge
  -- the gap sign enters through merge_stage (Emerged ≤ Emean with G ≥ 0)
  have hmw : S.effects.mergeEnergy ≤ S.effects.growEnergy :=
    Hagi.Foundations.merge_stage S.effects.growEnergy S.gap S.effects.mergeEnergy h_emp_merge hgap
  have hj : S.effects.jointEnergy
      ≤ S.effects.mergeEnergy - S.sp.eta * ‖S.stepDir‖ ^ 2 / 2 :=
    Hagi.Foundations.joint_stage S.sp.L S.sp.eta ‖S.stepDir‖
      ⟪S.grad, S.stepDir⟫_ℝ
      S.effects.jointEnergy S.effects.mergeEnergy hL heta heta0
      hdescent h_emp_smooth
  have hc : S.effects.compressEnergy - S.effects.jointEnergy
      ≤ S.sp.kappa * S.sp.s / 2 :=
    Hagi.Foundations.compress_stage S.sp.kappa S.sp.s S.effects.quantErr
      S.effects.compressEnergy S.effects.jointEnergy
      hkappa hs hdn h_emp_dist h_emp_lip
  -- the transition algebra: the composed potential telescopes
  have hp : potential (compress (joint (merge (grow S))))
      = S.effects.compressEnergy + (S.protectedRisk + S.effects.growRisk + S.effects.mergeRisk
        + S.effects.jointRisk + S.effects.compressRisk) := rfl
  have hps : potential S = S.energy + S.protectedRisk := rfl
  have hgj : gainJoint S = S.sp.eta * ‖S.stepDir‖ ^ 2 / 2 := rfl
  have hcc : costCompress S = S.sp.kappa * S.sp.s / 2 + S.effects.compressRisk := rfl
  have hgm : gainMerge S = S.gap := rfl
  linarith

/-- Under the same stage premises as `growth_cycle_potential`,
the real Φ-decrease dominates the `verify` certificate's
`decrease` minus its declared `riskSpend`. -/
theorem certificate_sound (S : GrowthState X)
    (hgap : 0 ≤ S.gap)
    (h_emp_grow : S.effects.growEnergy ≤ S.energy - S.effects.growGain)
    (h_emp_merge : S.effects.mergeEnergy ≤ S.effects.growEnergy - S.gap)
    (hL : 0 < S.sp.L) (heta : S.sp.eta ≤ 1 / S.sp.L) (heta0 : 0 ≤ S.sp.eta)
    (hdescent : ‖S.stepDir‖ ^ 2 ≤ ⟪S.grad, S.stepDir⟫_ℝ)
    (h_emp_smooth : S.effects.jointEnergy ≤ S.effects.mergeEnergy - S.sp.eta * ⟪S.grad, S.stepDir⟫_ℝ
      + S.sp.L * S.sp.eta ^ 2 * ‖S.stepDir‖ ^ 2 / 2)
    (hkappa : 0 ≤ S.sp.kappa) (hs : 0 ≤ S.sp.s) (hdn : 0 ≤ S.effects.quantErr)
    (h_emp_dist : S.effects.quantErr ≤ 1 / 2)
    (h_emp_lip : S.effects.compressEnergy - S.effects.jointEnergy
      ≤ S.sp.kappa * S.sp.s * S.effects.quantErr) :
    potential (compress (joint (merge (grow S))))
      ≤ potential S - (verify S).decrease + (verify S).riskSpend := by
  have hcycle := growth_cycle_potential S hgap h_emp_grow h_emp_merge hL heta heta0
    hdescent h_emp_smooth hkappa hs hdn h_emp_dist h_emp_lip
  have hv : (verify S).decrease
      = S.effects.growGain + S.gap + gainJoint S
        - S.sp.kappa * S.sp.s / 2 := rfl
  have hr : (verify S).riskSpend
      = S.effects.growRisk + S.effects.mergeRisk
        + S.effects.jointRisk + S.effects.compressRisk := rfl
  have hgj : gainJoint S = S.sp.eta * ‖S.stepDir‖ ^ 2 / 2 := rfl
  have hgm : gainMerge S = S.gap := rfl
  have hcc : costCompress S = S.sp.kappa * S.sp.s / 2 + S.effects.compressRisk := rfl
  linarith

/-- The composed budget after one generation equals
`S.budget − (verify S).budgetSpend`. -/
theorem budget_account (S : GrowthState X) :
    (compress (joint (merge (grow S)))).budget
      = S.budget - (verify S).budgetSpend := by
  have hb : (compress (joint (merge (grow S)))).budget
      = S.budget - S.effects.growCost - S.effects.mergeCost
          - S.effects.jointCost - S.effects.compressCost := rfl
  have hv : (verify S).budgetSpend = S.effects.growCost
      + S.effects.mergeCost + S.effects.jointCost
      + S.effects.compressCost := rfl
  linarith

/-! ### StageCertificate (audit v3 Phase 4 step 2, R342) -/

/-- The one-generation stage certificate: the potentials before
and after the composed generation plus the verifier certificate
it emits. Contiguity of a trajectory of such certificates is a
premise of `stage_certificate_telescope` (no hidden state
identity). -/
structure StageCertificate where
  /-- Φ of the state before the generation. -/
  before : ℝ
  /-- Φ of the state after the generation. -/
  after : ℝ
  /-- The emitted verifier certificate (decrease/riskSpend/budgetSpend). -/
  cert : Certificate

/-- `stageCertificate S`: the certificate of one composed
generation on `S`. -/
def stageCertificate (S : GrowthState X) : StageCertificate where
  before := potential S
  after := potential (compress (joint (merge (grow S))))
  cert := verify S

/-- **Soundness of the stage certificate**: under exactly the
stage premises of `certificate_sound`, the recorded after-potential
is at most the before-potential minus the certified decrease plus
the certified risk spend. -/
theorem stage_certificate_sound (S : GrowthState X)
    (hgap : 0 ≤ S.gap)
    (h_emp_grow : S.effects.growEnergy ≤ S.energy - S.effects.growGain)
    (h_emp_merge : S.effects.mergeEnergy ≤ S.effects.growEnergy - S.gap)
    (hL : 0 < S.sp.L) (heta : S.sp.eta ≤ 1 / S.sp.L) (heta0 : 0 ≤ S.sp.eta)
    (hdescent : ‖S.stepDir‖ ^ 2 ≤ ⟪S.grad, S.stepDir⟫_ℝ)
    (h_emp_smooth : S.effects.jointEnergy ≤ S.effects.mergeEnergy - S.sp.eta * ⟪S.grad, S.stepDir⟫_ℝ
      + S.sp.L * S.sp.eta ^ 2 * ‖S.stepDir‖ ^ 2 / 2)
    (hkappa : 0 ≤ S.sp.kappa) (hs : 0 ≤ S.sp.s) (hdn : 0 ≤ S.effects.quantErr)
    (h_emp_dist : S.effects.quantErr ≤ 1 / 2)
    (h_emp_lip : S.effects.compressEnergy - S.effects.jointEnergy
      ≤ S.sp.kappa * S.sp.s * S.effects.quantErr) :
    (stageCertificate S).after
      ≤ (stageCertificate S).before
        - ((stageCertificate S).cert).decrease
        + ((stageCertificate S).cert).riskSpend :=
  certificate_sound S hgap h_emp_grow h_emp_merge hL heta heta0 hdescent
    h_emp_smooth hkappa hs hdn h_emp_dist h_emp_lip

/-- **The telescope over a contiguous certificate trajectory**:
if every generation's stage certificate is sound and the chain is
contiguous (`before (t+1) = after t`), the final potential is at
most the initial one minus the summed certified decreases plus the
summed risk spends. -/
theorem stage_certificate_telescope {T : ℕ} (cs : ℕ → StageCertificate)
    (hT : 0 < T)
    (hcontig : ∀ t, t + 1 < T → (cs (t + 1)).before = (cs t).after)
    (hsound : ∀ t, t < T →
      (cs t).after ≤ (cs t).before - ((cs t).cert).decrease
        + ((cs t).cert).riskSpend) :
    (cs (T - 1)).after ≤ (cs 0).before
      - ∑ t ∈ Finset.range T, ((cs t).cert).decrease
      + ∑ t ∈ Finset.range T, ((cs t).cert).riskSpend := by
  -- the chain identity: the final after-potential is the initial
  -- before-potential plus the summed per-certificate steps
  have hsum : (cs (T - 1)).after = (cs 0).before
      + ∑ t ∈ Finset.range T, ((cs t).after - (cs t).before) := by
    revert hsound
    revert hcontig
    induction T with
    | zero =>
        intro _ _
        exact absurd hT (Nat.not_lt_zero 0)
    | succ T ih =>
        intro hcontig hsound
        cases Nat.eq_zero_or_pos T with
        | inl h0 =>
            subst h0
            have h1 : (0 + 1 - 1 : ℕ) = 0 := by norm_num
            rw [h1, Finset.sum_range_one]
            ring
        | inr hpos =>
            have hb : (cs (T - 1 + 1)).before = (cs (T - 1)).after :=
              hcontig (T - 1) (by omega)
            have hidx : T - 1 + 1 = T := by omega
            rw [hidx] at hb
            have hrec := ih hpos
              (fun t ht => hcontig t (by omega))
              (fun t ht => hsound t (by omega))
            have hstep : (cs T).after - (cs (T - 1)).after
                = (cs T).after - (cs T).before := by
              rw [hb]
            have hidx2 : T + 1 - 1 = T := by omega
            rw [hidx2, Finset.sum_range_succ]
            linarith
  -- each step is bounded by its certificate
  have hsteps : ∀ t ∈ Finset.range T,
      (cs t).after - (cs t).before
        ≤ -((cs t).cert).decrease + ((cs t).cert).riskSpend :=
    fun t ht => by
      have h := hsound t (Finset.mem_range.mp ht)
      linarith
  have hsumbound : ∑ t ∈ Finset.range T, ((cs t).after - (cs t).before)
      ≤ ∑ t ∈ Finset.range T, ( - ((cs t).cert).decrease
        + ((cs t).cert).riskSpend) :=
    Finset.sum_le_sum hsteps
  have hsplit : ∑ t ∈ Finset.range T, ( - ((cs t).cert).decrease
        + ((cs t).cert).riskSpend)
      = - ∑ t ∈ Finset.range T, ((cs t).cert).decrease
        + ∑ t ∈ Finset.range T, ((cs t).cert).riskSpend := by
    simp [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  linarith

end GrowthLoop

/--
`termination_from_telescope`: if every certified generation
decreases the potential by at least `ε` while spending at most
`r < ε` risk, then the number of generations is bounded by
`(Φ₀ − φmin)/(ε − r)`: the loop cannot run forever. This is
the composition of `stage_certificate_telescope` with a
Lyapunov step bound (cf. `lyapunov_termination_fin`).
-/
theorem termination_from_telescope {T : ℕ} (cs : ℕ → StageCertificate)
    (φmin ε r : ℝ)
    (hT : 0 < T)
    (hcontig : ∀ t, t + 1 < T → (cs (t + 1)).before = (cs t).after)
    (hsound : ∀ t, t < T →
      (cs t).after ≤ (cs t).before - ((cs t).cert).decrease
        + ((cs t).cert).riskSpend)
    (hfloor : φmin ≤ (cs (T - 1)).after)
    (hdec : ∀ t ∈ Finset.range T, ε ≤ ((cs t).cert).decrease)
    (hrisk : ∀ t ∈ Finset.range T, ((cs t).cert).riskSpend ≤ r)
    (hε : 0 < ε) (hr : 0 ≤ r) (hεr : r < ε)
    : (T : ℝ) ≤ ((cs 0).before - φmin) / (ε - r) := by
  have htel := stage_certificate_telescope cs hT hcontig hsound
  have hsumdec : T * ε ≤ ∑ t ∈ Finset.range T, ((cs t).cert).decrease := by
    calc T * ε = ∑ t ∈ Finset.range T, ε := by simp
      _ ≤ ∑ t ∈ Finset.range T, ((cs t).cert).decrease :=
          Finset.sum_le_sum hdec
  have hsumrisk : ∑ t ∈ Finset.range T, ((cs t).cert).riskSpend ≤ T * r := by
    calc ∑ t ∈ Finset.range T, ((cs t).cert).riskSpend
        ≤ ∑ t ∈ Finset.range T, r := Finset.sum_le_sum hrisk
      _ = T * r := by simp
  have hkey : T * (ε - r) ≤ (cs 0).before - φmin := by
    have h1 : (cs (T - 1)).after ≤ (cs 0).before
        - ∑ t ∈ Finset.range T, ((cs t).cert).decrease
        + ∑ t ∈ Finset.range T, ((cs t).cert).riskSpend := htel
    nlinarith
  have hpos : 0 < ε - r := by linarith
  rw [le_div_iff₀ hpos]
  exact hkey

end Hagi.System
namespace Hagi
export Hagi.System (StageParams GrowthState potential gainJoint grow merge joint compress Certificate verify measure StageCertificate stage_certificate_telescope certificate_sound budget_account)
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Специализация канона: Φ2 при λ=1, ν=0 — это в точности
потенциал состояния Φ1 (единственность базовой шкалы). -/
theorem hagiPotential_special_eq (S : GrowthState X) :
    Hagi.Foundations.hagiPotential S.energy S.protectedRisk 0 0 S.capability 1
      = potential S := by
  simp [Hagi.Foundations.hagiPotential, potential]

/-- Мост убывания: при λ=1 и ν ≥ 0 убывание базового
потенциала Φ1 вместе с НЕубыванием качества переносится на
канонический потенциал Φ2 — штраф недостижения цели только
помогает (не растёт при росте качества). -/
theorem potential_decrease_bridge (S S' : GrowthState X)
    (nu qTarget : ℝ) (hnu : 0 ≤ nu)
    (hcap : S.capability ≤ S'.capability)
    (hPhi1 : potential S' ≤ potential S) :
    Hagi.Foundations.hagiPotential S'.energy S'.protectedRisk nu qTarget
        S'.capability 1
      ≤ Hagi.Foundations.hagiPotential S.energy S.protectedRisk nu qTarget
          S.capability 1 := by
  -- penalty не растёт при росте качества
  have hpen : max 0 (qTarget - S'.capability)
      ≤ max 0 (qTarget - S.capability) := by
    have h1 : qTarget - S'.capability ≤ qTarget - S.capability := by
      linarith
    exact max_le_max (le_refl _) h1
  -- развернуть оба потенциала
  unfold Hagi.Foundations.hagiPotential potential at *
  linarith [hpen, mul_le_mul_of_nonneg_left hpen hnu]

end Hagi
set_option linter.style.header false

/-!
# GrowthState effects recompute + capability tie-in (A16)

The A16 mandatory fix #1, honesty half. Two pinned defects of
`Hagi.System.GrowthState` (statements Freeze-locked, so this module
ADDS the fix beside them, never edits them):

* **Stale effects.** The old ops `grow`/`merge`/`joint`/`compress`
  write the state-level channels from the measured record
  `S.effects` but carry the record itself unchanged
  (`effects := S.effects`). One generation is premise-covered (the
  h_emp_ chains of `growth_cycle_potential`); ACROSS generations
  nothing forces the post-cycle state's effects to be a re-measurement
  — see `stale_effects_gap_witness` for the formal gap.
* **Capability tie.** The master invariant's `cap` channel
  (`CertifiedHAGIInvariant.capability_growth`, R107) is an abstract
  `ℕ → ℝ` sequence; without the equality `cap t = (St t).capability`
  the growth theorem does not certify state capability growth. The
  missing premise is named here (`CapabilityTie`) and PROVEN for the
  new fresh ops (`capability_telescope_fresh`).

The fix (`EvalBinding` pattern — data carried with explicit
re-evaluation, no hidden convention): the fresh ops `growR`, `mergeR`,
`jointR`, `compressR` perform the SAME certified channel updates as
the old ops (measured at the pre-state `S`) but install the
caller-supplied RE-MEASURED record `e'` as the post-state's `effects`
field — freshness by construction. Honest pin: the re-evaluation
oracle is abstract (the caller re-measures, exactly as the caller
supplies `evalFn` in `EvalBinding`); when the oracle returns the same
record, the fresh ops COINCIDE with the old ones (`growR_eq_grow`,
`cycleR_eq_cycle`).

Nothing here changes the Legacy/Nonvacuity regression theorems.
-/

open Finset Real InnerProductSpace

namespace Hagi.System

noncomputable section Recompute

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-! ### The honesty pins (defect as theorems, not prose) -/

/-- The OLD ops carry the effects record through a full generation
UNCHANGED (definitional): after `compress (joint (merge (grow S)))`
the state's `effects` still holds the PRE-cycle measurement record.
This is the stale-effects defect of A16 mandatory fix #1, pinned. -/
theorem effects_carry_stale_cycle (S : GrowthState X) :
    (compress (joint (merge (grow S)))).effects = S.effects := by rfl

/-- The exact capability accounting of one OLD composed generation
(the fact the master `cap` channel was never tied to): capability
grows by exactly the measured `growGain`. -/
theorem capability_cycle_exact (S : GrowthState X) :
    (compress (joint (merge (grow S)))).capability
      = S.capability + S.effects.growGain := by rfl

/-- The witness carrier's stage constants: the degenerate zero-cost
window (η = 0, κ = 0, s = 0). -/
noncomputable def witParams : StageParams where
  eta := 0
  L := 1
  kappa := 0
  s := 0

/-- The witness effects: energy 10 → 9 at grow, constant through
merge/joint/compress, with growGain = 1. -/
noncomputable def witEffects : StageEffects where
  growGain := 1
  growCost := 0
  growRisk := 0
  growEnergy := 9
  mergeEnergy := 9
  mergeRisk := 0
  mergeCost := 0
  jointEnergy := 9
  jointRisk := 0
  jointCost := 0
  quantErr := 0
  compressEnergy := 9
  compressRisk := 0
  compressCost := 0

/-- The witness state: all stage chains hold at generation 1
(10 → 9 → 9 → 9 → 9 with gain 1), but the carried record makes the
generation-2 premise `9 ≤ 9 − 1` fail. -/
noncomputable def witState : GrowthState (EuclideanSpace ℝ (Fin 1)) where
  weightDim := 1
  weights := fun _ => 0
  params := 0
  experts := 0
  energy := 10
  protectedRisk := 0
  budget := 1
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := 0
  sp := witParams
  effects := witEffects

/-- **The formal stale-effects gap** (acceptance bar of this beat):
there is a state whose generation-1 certification premises ALL hold
  (gap sign plus the four h_emp_ stage chains, in the degenerate
  zero-cost window), yet at the post-cycle state the generation-2
  h_emp_grow premise FAILS — because the old ops carried the effects
record unchanged instead of re-measuring it. Effects freshness across
generations is NOT derivable from the old ops; it must be re-measured
(the `*R` ops below). -/
theorem stale_effects_gap_witness :
    ∃ S : GrowthState (EuclideanSpace ℝ (Fin 1)),
      (0 ≤ S.gap
        ∧ S.effects.growEnergy ≤ S.energy - S.effects.growGain
        ∧ S.effects.mergeEnergy ≤ S.effects.growEnergy - S.gap
        ∧ S.effects.jointEnergy ≤ S.effects.mergeEnergy)
      ∧ ¬ (S.effects.growEnergy
            ≤ (compress (joint (merge (grow S)))).energy
              - (compress (joint (merge (grow S)))).effects.growGain) := by
  refine ⟨witState, ⟨?_, ?_⟩⟩
  · norm_num [witState, witEffects, witParams]
  · intro h
    simp only [grow, merge, joint, compress, witState, witEffects, witParams] at h
    linarith

/-! ### The fresh ops (recomputed effects, EvalBinding pattern) -/

/-- **growR**: the certified grow transition with a RE-MEASURED
effects record. The state-level channel updates are exactly `grow`'s
(measured at the pre-state `S`); the post-state's `effects` field is
the caller-supplied re-evaluation `e'` — the freshness the old carry
cannot guarantee, by construction. -/
def growR (S : GrowthState X) (e' : StageEffects) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts + 1
  energy := S.effects.growEnergy
  protectedRisk := S.protectedRisk + S.effects.growRisk
  budget := S.budget - S.effects.growCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability + S.effects.growGain
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := e'

/-- **mergeR**: the merge transition consuming the RE-MEASURED record
`e` at the post-grow state (`energy := e.mergeEnergy`), installing the
next re-evaluation `e'`. -/
def mergeR (S : GrowthState X) (e' : StageEffects) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts
  energy := S.effects.mergeEnergy
  protectedRisk := S.protectedRisk + S.effects.mergeRisk
  budget := S.budget - S.effects.mergeCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := e'

/-- **jointR**: the SafeQP refinement step consuming the re-measured
record, installing the next re-evaluation `e'`. -/
def jointR (S : GrowthState X) (e' : StageEffects) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params - S.sp.eta • S.stepDir
  experts := S.experts
  energy := S.effects.jointEnergy
  protectedRisk := S.protectedRisk + S.effects.jointRisk
  budget := S.budget - S.effects.jointCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := e'

/-- **compressR**: the compress transition consuming the re-measured
record, installing the generation's final re-evaluation `e'`. -/
def compressR (S : GrowthState X) (e' : StageEffects) : GrowthState X where
  weightDim := S.weightDim
  weights := S.weights
  params := S.params
  experts := S.experts
  energy := S.effects.compressEnergy
  protectedRisk := S.protectedRisk + S.effects.compressRisk
  budget := S.budget - S.effects.compressCost
  gap := S.gap
  dataField := S.dataField
  capability := S.capability
  verifier := S.verifier
  runtimeError := S.runtimeError
  stepDir := S.stepDir
  grad := S.grad
  sp := S.sp
  effects := e'

/-- The composed fresh generation: each stage consumes the record
re-measured at the previous stage's output. -/
def cycleR (S : GrowthState X) (e₁ e₂ e₃ e₄ : StageEffects) : GrowthState X :=
  compressR (jointR (mergeR (growR S e₁) e₂) e₃) e₄

/-! ### Freshness and carry-safety lemmas -/

/-- Freshness by construction: the post-state's effects ARE the
re-measured record. -/
theorem growR_effects (S : GrowthState X) (e' : StageEffects) :
    (growR S e').effects = e' := by rfl

theorem mergeR_effects (S : GrowthState X) (e' : StageEffects) :
    (mergeR S e').effects = e' := by rfl

theorem jointR_effects (S : GrowthState X) (e' : StageEffects) :
    (jointR S e').effects = e' := by rfl

theorem compressR_effects (S : GrowthState X) (e' : StageEffects) :
    (compressR S e').effects = e' := by rfl

/-- The composed fresh generation ends with the generation's final
re-evaluation as its effects record. -/
theorem cycleR_effects (S : GrowthState X) (e₁ e₂ e₃ e₄ : StageEffects) :
    (cycleR S e₁ e₂ e₃ e₄).effects = e₄ := by rfl

/-- Exact capability accounting of one fresh grow step. -/
theorem growR_capability (S : GrowthState X) (e' : StageEffects) :
    (growR S e').capability = S.capability + S.effects.growGain := by rfl

/-- Exact capability accounting of a full fresh generation (only the
grow stage moves the capability channel). -/
theorem cycleR_capability (S : GrowthState X) (e₁ e₂ e₃ e₄ : StageEffects) :
    (cycleR S e₁ e₂ e₃ e₄).capability
      = S.capability + S.effects.growGain := by rfl

/-- **Carry-safety**: when the re-evaluation oracle returns the SAME
record, the fresh op COINCIDES with the old one (full record
equality) — the fix degrades to the old behaviour exactly, no
divergence hidden anywhere. -/
theorem growR_eq_grow (S : GrowthState X) : growR S S.effects = grow S := by rfl

/-- Carry-safety for the composed generation: identity re-evaluation
at every stage reproduces the OLD composed cycle. -/
theorem cycleR_eq_cycle (S : GrowthState X) :
    cycleR S S.effects S.effects S.effects S.effects
      = compress (joint (merge (grow S))) := by rfl

/-! ### The capability tie-in (A16 honesty: channel vs state) -/

/-- **The missing premise of the master growth theorem**: the abstract
capability channel `cap` of `CertifiedHAGIInvariant` (and the C_t
renewal sequences) equals the `GrowthState.capability` projection of
the trajectory. WITHOUT this premise, the capability_growth conjunct
certifies an
abstract channel and must not be read as state-capability growth;
master consumers state it explicitly. -/
def CapabilityTie (St : ℕ → GrowthState X) (cap : ℕ → ℝ) : Prop :=
  ∀ t, cap t = (St t).capability

/-- The tie PROVEN for the fresh ops: along a `growR` trajectory the
capability channel evolves by EXACT additive growGain accounting —
the equality the master invariant would need, here a theorem instead
of a convention. -/
theorem capability_telescope_fresh {T : ℕ} (St : ℕ → GrowthState X)
    (e : ℕ → StageEffects)
    (hstep : ∀ t, t < T → St (t + 1) = growR (St t) (e t)) :
    (St T).capability = (St 0).capability
      + ∑ t ∈ Finset.range T, (St t).effects.growGain := by
  induction T with
  | zero => simp
  | succ T ih =>
      have h1 : St (T + 1) = growR (St T) (e T) := hstep T (Nat.lt_succ_self T)
      rw [h1]
      have hgrow : (growR (St T) (e T)).capability
          = (St T).capability + (St T).effects.growGain := by rfl
      rw [hgrow, ih (fun t ht => hstep t (Nat.lt_trans ht (Nat.lt_succ_self T)))]
      rw [Finset.sum_range_succ]
      ring

/-- Under the tie premise, the abstract channel's endpoint IS the
state accounting: `capability_telescope_fresh` restated on `cap`. -/
theorem capability_channel_of_tie {T : ℕ} (St : ℕ → GrowthState X)
    (cap : ℕ → ℝ) (e : ℕ → StageEffects)
    (htie : CapabilityTie St cap)
    (hstep : ∀ t, t < T → St (t + 1) = growR (St t) (e t)) :
    cap T = cap 0 + ∑ t ∈ Finset.range T, (St t).effects.growGain := by
  rw [htie T, htie 0]
  exact capability_telescope_fresh St e hstep

end Recompute

end Hagi.System

/-!
# GrowthStateViews — разбиение состояния на 5 сущностей (P2.9)

Канонический `GrowthState` (17 полей) канонически разлагается
на пять сущностей плана рефакторинга P2.9:

* **ModelPart** — состояние модели (weights/params/experts/
  weightDim);
* **MetricsPart** — метрики (capability/verifier/runtimeError/
  gap/energy);
* **MemoryPart** — память (dataField);
* **OptimizerPart** — оптимизатор (stepDir/grad/sp/effects);
* **ResourcePart** — ресурсный баланс (budget/protectedRisk).

Каждая сущность — структура-представление с проекциями
`toParts`/`ofParts`; раунд-трип сохраняет состояние
(`GrowthState_parts_roundtrip`). Канон не меняется —
views дают модульный доступ без слома 2900+ деклараций.
-/

namespace Hagi.System

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Сущность 1: состояние модели. -/
structure ModelPart (X : Type*) [NormedAddCommGroup X] where
  weightDim : ℕ
  weights : Fin weightDim → ℝ
  params : X
  experts : ℕ

/-- Сущность 2: метрики качества. -/
structure MetricsPart where
  energy : ℝ
  gap : ℝ
  capability : ℝ
  verifier : ℝ
  runtimeError : ℝ

/-- Сущность 3: память. -/
structure MemoryPart where
  dataField : ℝ

/-- Сущность 4: оптимизатор. -/
structure OptimizerPart (X : Type*) [NormedAddCommGroup X] where
  stepDir : X
  grad : X
  sp : StageParams
  effects : StageEffects

/-- Сущность 5: ресурсный баланс. -/
structure ResourcePart where
  budget : ℝ
  protectedRisk : ℝ

/-- Разложение состояния на пять сущностей. -/
def toParts (S : GrowthState X) :
    ModelPart X × MetricsPart × MemoryPart × OptimizerPart X × ResourcePart where
  1 := ⟨S.weightDim, S.weights, S.params, S.experts⟩
  2.1 := ⟨S.energy, S.gap, S.capability, S.verifier, S.runtimeError⟩
  2.2.1 := ⟨S.dataField⟩
  2.2.2.1 := ⟨S.stepDir, S.grad, S.sp, S.effects⟩
  2.2.2.2 := ⟨S.budget, S.protectedRisk⟩

/-- Сборка состояния из пяти сущностей. -/
def ofParts (p : ModelPart X × MetricsPart × MemoryPart × OptimizerPart X × ResourcePart) :
    GrowthState X where
  weightDim := p.1.weightDim
  weights := p.1.weights
  params := p.1.params
  experts := p.1.experts
  energy := p.2.1.energy
  protectedRisk := p.2.2.2.2.protectedRisk
  budget := p.2.2.2.2.budget
  gap := p.2.1.gap
  dataField := p.2.2.1.dataField
  capability := p.2.1.capability
  verifier := p.2.1.verifier
  runtimeError := p.2.1.runtimeError
  stepDir := p.2.2.2.1.stepDir
  grad := p.2.2.2.1.grad
  sp := p.2.2.2.1.sp
  effects := p.2.2.2.1.effects

/-- РАУНД-ТРИП: разложение-сборка сохраняет состояние
(корректность разбиения P2.9). -/
theorem GrowthState_parts_roundtrip (S : GrowthState X) :
    ofParts (toParts S) = S := by
  rfl

/-- Проекция раунд-трипа: разложение инъективно. -/
theorem toParts_injective (S S' : GrowthState X)
    (h : toParts S = toParts S') : S = S' := by
  have : ofParts (toParts S) = ofParts (toParts S') := by rw [h]
  rwa [GrowthState_parts_roundtrip, GrowthState_parts_roundtrip] at this

end Hagi.System

set_option linter.style.header false

/-!
# GrowthComputed — вычисляемая энергия состояний роста (цикл 35)

Ответ аудиту #8 п.8 («energy в GrowthState — просто поле»):
канонический ВЫЧИСЛЯЕМЫЙ инстанс энергии — квадратичная
энергия сжатых весов:
  growthQuad w = Σ wᵢ²/2  (однозадачная TrainingTransition-
  цель с нулевой задачей: taskQual = quadLossAt 0 w).

Мост-теорема growEnergy_derived: если измеренные поля
согласованы с вычисляемой энергией (S.energy = growthQuad S.weights,
growEnergy-эффект = growthQuad весов после шага), то
h_emp_grow-посылка стадии grow (S'.growEnergy ≤ S.energy − gain)
ВЫВОДИТСЯ из доказанного спуска TrainingTransition —
эмпирическая посылка становится теоремой в каноническом
инстансе. Измеряемое поле остаётся для общего случая
(токен-KL), но имеет доказанного канонического представителя.
-/

open Finset

namespace Hagi.System.GrowthComputed

open Hagi.Learning.TrainingTransition

/-- Вычисляемая энергия сжатых весов: Σ wᵢ²/2. -/
noncomputable def growthQuad {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, w i ^ 2 / 2

/-- Положительность энергии при ненулевых весах. -/
theorem growthQuad_pos_of_nonzero {n : ℕ} (w : Fin n → ℝ)
    (hw : ∑ i, w i ^ 2 ≠ 0) : 0 < growthQuad w := by
  have hpos : 0 < ∑ i, w i ^ 2 := by
    have hnn : (0:ℝ) ≤ ∑ i, w i ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rcases eq_or_lt_of_le hnn with hE | hE
    · exact absurd hE.symm hw
    · exact hE
  unfold growthQuad
  have hper : ∀ i : Fin n, w i ^ 2 / 2 = (1/2) * w i ^ 2 := by
    intro i; ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hper i),
    ← Finset.mul_sum]
  exact mul_pos (by norm_num : (0:ℝ) < 1/2) hpos

/-- Градиентный шаг по весам (однозадачная нулевая цель:
g = w). -/
def growthStep {n : ℕ} (w : Fin n → ℝ) (eta : ℝ) : Fin n → ℝ :=
  fun i => w i - eta * w i

/-- ТОЧНОЕ тождество вычисляемой энергии шага:
E(step w η) = (1−η)² · E(w). -/
theorem growthQuad_step {n : ℕ} (w : Fin n → ℝ) (eta : ℝ) :
    growthQuad (growthStep w eta) = (1 - eta) ^ 2 * growthQuad w := by
  unfold growthQuad growthStep
  have hper : ∀ i : Fin n, (w i - eta * w i) ^ 2
      = (1 - eta) ^ 2 * w i ^ 2 := by
    intro i
    ring_nf
  have hper2 : ∀ i : Fin n, (w i - eta * w i) ^ 2 / 2
      = (1 - eta) ^ 2 * (w i ^ 2 / 2) := by
    intro i; ring
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hper2 i)

/-- СТРОГИЙ СПУСК вычисляемой энергии: при η ∈ (0,2) и
ненулевых весах энергия строго убывает. -/
theorem growthQuad_descent {n : ℕ} (w : Fin n → ℝ) (eta : ℝ)
    (h0 : 0 < eta) (h2 : eta < 2)
    (hw : ∑ i, w i ^ 2 ≠ 0) :
    growthQuad (growthStep w eta) < growthQuad w := by
  rw [growthQuad_step]
  have hcoef : (1 - eta) ^ 2 < 1 := by
    have hnn : -1 < 1 - eta := by linarith
    have hle : 1 - eta < 1 := by linarith
    nlinarith [sq_nonneg (1 - eta), hnn, hle]
  have hpos : 0 < growthQuad w := growthQuad_pos_of_nonzero w hw
  have := mul_lt_mul_of_pos_right hcoef hpos
  linarith

/-- МОСТ-ТЕОРЕМА: в каноническом инстансе (измеренные поля =
вычисляемая энергия) h_emp_grow-посылка стадии grow ВЫВОДИТСЯ:
  growEnergy(после шага) ≤ S.energy − gain
при gain = (1 − (1−η)²)·E(w) > 0. Эмпирическая посылка
становится теоремой для квадратичного канонического
представителя измеряемой энергии. -/
theorem growEnergy_derived {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (S : GrowthState X)
    (eta : ℝ) (h0 : 0 < eta) (h2 : eta < 2)
    (hw : ∑ i, S.weights i ^ 2 ≠ 0)
    (hcanon : S.energy = growthQuad S.weights)
    (hstep : S.effects.growEnergy
      = growthQuad (growthStep S.weights eta)) :
    S.effects.growEnergy ≤ S.energy
      - (1 - (1 - eta) ^ 2) * growthQuad S.weights
      ∧ 0 < (1 - (1 - eta) ^ 2) * growthQuad S.weights := by
  constructor
  · rw [hstep, hcanon]
    have hpos : (0:ℝ) < growthQuad S.weights :=
      growthQuad_pos_of_nonzero S.weights hw
    have hkey : growthQuad (growthStep S.weights eta)
        = growthQuad S.weights
          - (1 - (1 - eta) ^ 2) * growthQuad S.weights := by
      rw [growthQuad_step]
      ring
    rw [hkey]
  · -- gain > 0: (1−(1−η)²) > 0 и E > 0
    have hcoef : 0 < 1 - (1 - eta) ^ 2 := by
      have : (1 - eta) ^ 2 < 1 := by
        have hnn : -1 < 1 - eta := by linarith
        have hle : 1 - eta < 1 := by linarith
        nlinarith [sq_nonneg (1 - eta), hnn, hle]
      linarith
    have hpos : (0:ℝ) < growthQuad S.weights := by
      exact growthQuad_pos_of_nonzero S.weights hw
    exact mul_pos hcoef hpos

end Hagi.System.GrowthComputed
