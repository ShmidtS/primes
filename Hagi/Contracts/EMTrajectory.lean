/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.FiniteMultiEM
import Hagi.Contracts.ObjectiveTrajectory

/-!
# EM trajectory contracts

Canonical Contracts-side EM trajectory family in one file: finite closed-family EM,
changing-family EM, categorical mixtures, factorized complete-CE selection.
-/


/-!
Canonical generalized-EM trajectories through finite time-varying model
banks, with exact posteriors recomputed at the actual current model.
Whole-current-pair retention and posterior support closure imply additive
observation NLL monotonicity and real complete-CE/posterior-KL information
budgets. No fixed-bank stabilization, model optimality, parameter
convergence or computational claim is made.
-/


set_option relaxedAutoImplicit false

open Hagi.Prelude
open Hagi.Probability
open Hagi.Probability.FiniteBayes
open Hagi.Probability.FiniteLogScore
open Hagi.Probability.FiniteEM
open Hagi.Probability.FiniteMultiEM
open Filter Topology
open scoped BigOperators ENNReal

namespace Hagi.Contracts.ChangingEMTrajectory

private noncomputable def currentPosterior {A I X Y : Type} [Fintype I]
    [Fintype X] (y : I → Y) (c : ℕ → A → I → PMF X × (X → PMF Y))
    (hE : ∀ t a i, 0 < observationEvidence (c t a i).1 (c t a i).2 (y i))
    (a : ℕ → A) (t : ℕ) : I → PMF X :=
  fun i => posterior (c t (a t) i).1 (c t (a t) i).2 (y i) (hE t (a t) i)

private theorem currentPosterior_def {A I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (c : ℕ → A → I → PMF X × (X → PMF Y))
    (hE : ∀ t a i, 0 < observationEvidence (c t a i).1 (c t a i).2 (y i))
    (a : ℕ → A) (t : ℕ) :
    currentPosterior y c hE a t =
      fun i => posterior (c t (a t) i).1 (c t (a t) i).2 (y i) (hE t (a t) i) := rfl

section
variable {A I X Y : Type} [Fintype A] [Nonempty A] [Fintype I] [Fintype X]
variable (y : I → Y) (c : ℕ → A → I → PMF X × (X → PMF Y))
variable (hE : ∀ t a i, 0 < observationEvidence (c t a i).1 (c t a i).2 (y i))
variable (a₀ : A)

/-- The canonical changing-bank trajectory, selecting into bank `t + 1` with
exact posteriors freshly computed at the actual pair selected at time `t`. -/
noncomputable def changingEMPath (y : I → Y) (c : ℕ → A → I → PMF X × (X → PMF Y))
    (hE : ∀ t a i, 0 < observationEvidence (c t a i).1 (c t a i).2 (y i))
    (a₀ : A) : ℕ → A
  | 0 => a₀
  | t + 1 => batchMStep (fun i => posterior
      (c t (changingEMPath y c hE a₀ t) i).1
      (c t (changingEMPath y c hE a₀ t) i).2 (y i)
      (hE t (changingEMPath y c hE a₀ t) i)) y (c (t + 1))

/-- Actual additive observation negative log evidence on the selected path. -/
noncomputable def changingEMPathNLL (t : ℕ) : ℝ :=
  ∑ i, -Real.log (observationEvidence
    (c t (changingEMPath y c hE a₀ t) i).1
    (c t (changingEMPath y c hE a₀ t) i).2 (y i)).toReal

/-- The actual decreasing-information drop between consecutive path NLLs. -/
noncomputable def changingEMPathDrop (t : ℕ) : ℝ :=
  changingEMPathNLL y c hE a₀ t - changingEMPathNLL y c hE a₀ (t + 1)

/-- Complete-CE improvement at the exact old posterior, using the actual old
pair and the actual next selected pair; the retained baseline is not hidden
inside this numerical definition. -/
noncomputable def changingEMPathMGain (t : ℕ) : ℝ :=
  (∑ i, ceDef
    (fromPMF (currentPosterior y c hE (changingEMPath y c hE a₀) t i))
    (jointMass (c t (changingEMPath y c hE a₀ t) i).1
      (c t (changingEMPath y c hE a₀ t) i).2 (y i))) -
  ∑ i, ceDef
    (fromPMF (currentPosterior y c hE (changingEMPath y c hE a₀) t i))
    (jointMass (c (t + 1) (changingEMPath y c hE a₀ (t + 1)) i).1
      (c (t + 1) (changingEMPath y c hE a₀ (t + 1)) i).2 (y i))

/-- Sum of old-to-new posterior KL residuals on the actual changing-bank path. -/
noncomputable def changingEMPathKLResidual (t : ℕ) : ℝ :=
  ∑ i, klDef
    (fromPMF (currentPosterior y c hE (changingEMPath y c hE a₀) t i))
    (fromPMF (posterior
      (c (t + 1) (changingEMPath y c hE a₀ (t + 1)) i).1
      (c (t + 1) (changingEMPath y c hE a₀ (t + 1)) i).2 (y i)
      (hE (t + 1) (changingEMPath y c hE a₀ (t + 1)) i)))

/-- Actual additive path NLL is nonnegative without any retention premise. -/
theorem changingEMPath_nll_nonneg (t : ℕ) :
    0 ≤ changingEMPathNLL y c hE a₀ t := by
  exact total_negativeLogEvidence_nonneg
    (c t (changingEMPath y c hE a₀ t)) y

section Retained
variable (base : ℕ → A)
variable (hKeep : ∀ t, c (t + 1) (base t) = c t (changingEMPath y c hE a₀ t))
variable (hClose : ∀ t d i,
  (currentPosterior y c hE (changingEMPath y c hE a₀) t i).support ⊆
    (posterior (c (t + 1) d i).1 (c (t + 1) d i).2 (y i)
      (hE (t + 1) d i)).support)

include hKeep hClose

/-- Whole-pair retention and support closure imply one-step NLL nonincrease. -/
theorem changingEMPath_nll_succ_le (t : ℕ) :
    changingEMPathNLL y c hE a₀ (t + 1) ≤ changingEMPathNLL y c hE a₀ t := by
  have hq : ∀ i, currentPosterior y c hE (changingEMPath y c hE a₀) t i =
      posterior (c (t + 1) (base t) i).1 (c (t + 1) (base t) i).2
        (y i) (hE (t + 1) (base t) i) := by
    intro i
    have hi : c (t + 1) (base t) i = c t (changingEMPath y c hE a₀ t) i :=
      congrFun (hKeep t) i
    exact posterior_congr_of_model_eq _ _ _ _ _ hi.symm
  have h := current_totalNegativeLogEvidence_le_batchMStep
    (currentPosterior y c hE (changingEMPath y c hE a₀) t) y (c (t + 1))
    (hE (t + 1)) (fun d i => hClose t d i) (base t) hq
  rw [hKeep t] at h
  simpa only [changingEMPath, changingEMPathNLL, currentPosterior_def] using h

/-- The actual changing-bank path NLL is antitone under explicit retention. -/
theorem changingEMPath_nll_antitone :
    Antitone (changingEMPathNLL y c hE a₀) := by
  apply antitone_nat_of_succ_le
  exact changingEMPath_nll_succ_le y c hE a₀ base hKeep hClose

/-- Aggregate complete-CE gain is nonnegative: the next-bank minimizer beats
the retained old pair, and whole-pair retention identifies the baseline Q. -/
theorem changingEMPath_m_nonneg (t : ℕ) :
    0 ≤ changingEMPathMGain y c hE a₀ t := by
  have hmin := (batchMStep_spec
    (currentPosterior y c hE (changingEMPath y c hE a₀) t) y (c (t + 1))
    (hE (t + 1)) (fun d i => hClose t d i)).2 (base t)
  rw [hKeep t] at hmin
  apply sub_nonneg.mpr
  simpa only [changingEMPath, currentPosterior_def] using hmin

omit hKeep in
/-- Each old-to-new selected posterior KL aggregate is nonnegative. -/
theorem changingEMPath_kl_nonneg (t : ℕ) :
    0 ≤ changingEMPathKLResidual y c hE a₀ t := by
  apply Finset.sum_nonneg
  intro i _
  exact fromPMF_kl_nonneg _ _
    (hClose t (changingEMPath y c hE a₀ (t + 1)) i)

omit hKeep in
/-- Entropy cancellation gives the exact actual-pair drop/M/KL decomposition. -/
theorem changingEMPath_drop_eq_m_add_kl (t : ℕ) :
    changingEMPathDrop y c hE a₀ t =
      changingEMPathMGain y c hE a₀ t + changingEMPathKLResidual y c hE a₀ t := by
  have h := total_negativeLogEvidence_drop_eq
    (c t (changingEMPath y c hE a₀ t))
    (c (t + 1) (changingEMPath y c hE a₀ (t + 1))) y
    (hE t (changingEMPath y c hE a₀ t))
    (hE (t + 1) (changingEMPath y c hE a₀ (t + 1)))
    (hClose t (changingEMPath y c hE a₀ (t + 1)))
  rw [Finset.sum_sub_distrib] at h
  simpa only [changingEMPathDrop, changingEMPathNLL, changingEMPathMGain,
    changingEMPathKLResidual, currentPosterior_def] using h

omit hKeep in
private theorem changingEMPath_m_le_drop (t : ℕ) :
    changingEMPathMGain y c hE a₀ t ≤ changingEMPathDrop y c hE a₀ t := by
  have hidentity := changingEMPath_drop_eq_m_add_kl y c hE a₀ hClose t
  have hkl := changingEMPath_kl_nonneg y c hE a₀ hClose t
  linarith

private theorem changingEMPath_kl_le_drop (t : ℕ) :
    changingEMPathKLResidual y c hE a₀ t ≤ changingEMPathDrop y c hE a₀ t := by
  have hidentity := changingEMPath_drop_eq_m_add_kl y c hE a₀ hClose t
  have hm := changingEMPath_m_nonneg y c hE a₀ base hKeep hClose t
  linarith

omit hKeep hClose in
private theorem changingEMPath_drop_prefix_le (T : ℕ) :
    ∑ t ∈ Finset.range T, changingEMPathDrop y c hE a₀ t ≤
      changingEMPathNLL y c hE a₀ 0 := by
  calc
    ∑ t ∈ Finset.range T, changingEMPathDrop y c hE a₀ t ≤
        changingEMPathNLL y c hE a₀ 0 - changingEMPathNLL y c hE a₀ T :=
      Hagi.Contracts.ObjectiveTrajectory.sum_drop_le_initial_sub
        (changingEMPathNLL y c hE a₀) (changingEMPathDrop y c hE a₀) T
        (fun _ => le_of_eq rfl)
    _ ≤ changingEMPathNLL y c hE a₀ 0 :=
      sub_le_self _ (changingEMPath_nll_nonneg y c hE a₀ T)

omit hKeep hClose in
private theorem bounded_nonnegative_budget (F : ℕ → ℝ) (R : ℝ)
    (hF : ∀ t, 0 ≤ F t) (hbound : ∀ T, ∑ t ∈ Finset.range T, F t ≤ R) :
    (∀ T, ∑ t ∈ Finset.range T, F t ≤ R) ∧
      (Summable F ∧ Tendsto F atTop (nhds 0) ∧ ∑' t, F t ≤ R) := by
  exact Hagi.Contracts.ObjectiveTrajectory.budget4_of_sum_le F R hF hbound

/-- Finite prefixes, summability, vanishing terms and the total actual NLL-drop
information budget, with the infinite conclusions outside every `T`. -/
theorem changingEMPathDrop_budget :
    (∀ T, ∑ t ∈ Finset.range T, changingEMPathDrop y c hE a₀ t ≤
      changingEMPathNLL y c hE a₀ 0) ∧
    (Summable (changingEMPathDrop y c hE a₀) ∧
      Tendsto (changingEMPathDrop y c hE a₀) atTop (nhds 0) ∧
      ∑' t, changingEMPathDrop y c hE a₀ t ≤ changingEMPathNLL y c hE a₀ 0) := by
  exact bounded_nonnegative_budget _ _
    (fun t => sub_nonneg.mpr (changingEMPath_nll_succ_le
      y c hE a₀ base hKeep hClose t))
    (changingEMPath_drop_prefix_le y c hE a₀)

/-- The exact aggregate complete-CE information gains have the same initial-NLL
finite and infinite budget as the actual drops that dominate them. -/
theorem changingEMPathMGain_budget :
    (∀ T, ∑ t ∈ Finset.range T, changingEMPathMGain y c hE a₀ t ≤
      changingEMPathNLL y c hE a₀ 0) ∧
    (Summable (changingEMPathMGain y c hE a₀) ∧
      Tendsto (changingEMPathMGain y c hE a₀) atTop (nhds 0) ∧
      ∑' t, changingEMPathMGain y c hE a₀ t ≤ changingEMPathNLL y c hE a₀ 0) := by
  apply bounded_nonnegative_budget
  · exact changingEMPath_m_nonneg y c hE a₀ base hKeep hClose
  · intro T
    calc
      ∑ t ∈ Finset.range T, changingEMPathMGain y c hE a₀ t ≤
          ∑ t ∈ Finset.range T, changingEMPathDrop y c hE a₀ t :=
        Finset.sum_le_sum (fun t _ => changingEMPath_m_le_drop
          y c hE a₀ hClose t)
      _ ≤ changingEMPathNLL y c hE a₀ 0 :=
        changingEMPath_drop_prefix_le y c hE a₀ T

/-- The old-to-new posterior KL residuals have a finite and infinite actual
information budget bounded by initial NLL. -/
theorem changingEMPathKLResidual_budget :
    (∀ T, ∑ t ∈ Finset.range T, changingEMPathKLResidual y c hE a₀ t ≤
      changingEMPathNLL y c hE a₀ 0) ∧
    (Summable (changingEMPathKLResidual y c hE a₀) ∧
      Tendsto (changingEMPathKLResidual y c hE a₀) atTop (nhds 0) ∧
      ∑' t, changingEMPathKLResidual y c hE a₀ t ≤
        changingEMPathNLL y c hE a₀ 0) := by
  apply bounded_nonnegative_budget
  · exact changingEMPath_kl_nonneg y c hE a₀ hClose
  · intro T
    calc
      ∑ t ∈ Finset.range T, changingEMPathKLResidual y c hE a₀ t ≤
          ∑ t ∈ Finset.range T, changingEMPathDrop y c hE a₀ t :=
        Finset.sum_le_sum (fun t _ => changingEMPath_kl_le_drop
          y c hE a₀ base hKeep hClose t)
      _ ≤ changingEMPathNLL y c hE a₀ 0 :=
        changingEMPath_drop_prefix_le y c hE a₀ T

/-- Nonnegative antitone path NLL tends to its historical infimum, not
necessarily to zero and without an attainment or model-stability assertion. -/
theorem changingEMPath_nll_tendsto_ciInf :
    Tendsto (changingEMPathNLL y c hE a₀) atTop
      (nhds (⨅ t, changingEMPathNLL y c hE a₀ t)) :=
  Hagi.Contracts.ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg
    (changingEMPathNLL y c hE a₀)
    (changingEMPath_nll_antitone y c hE a₀ base hKeep hClose)
    (changingEMPath_nll_nonneg y c hE a₀)

omit hKeep hClose in
/-- The nonnegative historical infimum of the actual path NLL is nonnegative. -/
theorem changingEMPath_nll_ciInf_nonneg :
    0 ≤ ⨅ t, changingEMPathNLL y c hE a₀ t :=
  Hagi.Contracts.ObjectiveTrajectory.ciInf_nonneg
    (changingEMPathNLL y c hE a₀) (changingEMPath_nll_nonneg y c hE a₀)

/-- Separate M/KL summability licenses the total exact drop decomposition. -/
theorem changingEMPath_drop_tsum_eq_m_add_kl :
    (∑' t, changingEMPathDrop y c hE a₀ t) =
      (∑' t, changingEMPathMGain y c hE a₀ t) +
        ∑' t, changingEMPathKLResidual y c hE a₀ t := by
  have hm : Summable (changingEMPathMGain y c hE a₀) :=
    (changingEMPathMGain_budget y c hE a₀ base hKeep hClose).2.1
  have hk : Summable (changingEMPathKLResidual y c hE a₀) :=
    (changingEMPathKLResidual_budget y c hE a₀ base hKeep hClose).2.1
  calc
    (∑' t, changingEMPathDrop y c hE a₀ t) =
        ∑' t, (changingEMPathMGain y c hE a₀ t +
          changingEMPathKLResidual y c hE a₀ t) :=
      tsum_congr (changingEMPath_drop_eq_m_add_kl y c hE a₀ hClose)
    _ = _ := hm.tsum_add hk

end Retained
end

end Hagi.Contracts.ChangingEMTrajectory

/-! # Retained categorical mixtures with changing-family EM

Construct a mixture of two categorical prior/channel models on one fixed latent
carrier and an arbitrary observation type. Positive old evidence and a strict
interior weight give positive evidence and posterior support inclusion. Zero
weight preserves the complete old model, including fallback rows. A finite
interior grid and a validity-carrying state replay exactly into the retained
changing-family EM trajectory, yielding nonincreasing aggregate observation NLL.

The labels are not latent dimensions or computation counts. No selected-model
convergence, latent-cardinality growth, parameter optimum, per-unit improvement,
physical resource bound or efficient optimizer is asserted.
-/


set_option relaxedAutoImplicit false

open Hagi.Prelude
open Hagi.Probability
open Hagi.Probability.FiniteBayes
open Hagi.Probability.FiniteLogScore
open Hagi.Probability.FiniteEM
open Hagi.Probability.FiniteMultiEM
open Hagi.Contracts.ChangingEMTrajectory
open scoped BigOperators ENNReal

namespace Hagi.Contracts.MixtureEMTrajectory

-- BEGIN ISOLATED CORE

private noncomputable def mixturePriorMass {X : Type} (ε : NNReal)
    (p r : PMF X) (x : X) : ENNReal :=
  ((1 - ε : NNReal) : ENNReal) * p x + (ε : ENNReal) * r x

private noncomputable def mixtureJointMass {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X) (y : Y) : ENNReal :=
  ((1 - ε : NNReal) : ENNReal) * p x * K x y + (ε : ENNReal) * r x * L x y

private theorem mixturePriorMass_sum {X : Type} [Fintype X] (ε : NNReal)
    (hε : ε ≤ 1) (p r : PMF X) :
    ∑ x, mixturePriorMass ε p r x = 1 := by
  have hp : ∑ x, p x = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe p
  have hr : ∑ x, r x = 1 := by
    simpa only [tsum_fintype] using PMF.tsum_coe r
  simp only [mixturePriorMass, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hr,
    mul_one]
  exact_mod_cast tsub_add_cancel_of_le hε

private theorem mixturePriorMass_ne_top {X : Type} (ε : NNReal)
    (p r : PMF X) (x : X) : mixturePriorMass ε p r x ≠ ⊤ := by
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (p.apply_ne_top x)
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (r.apply_ne_top x)

private theorem mixtureJointMass_hasSum {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X) :
    HasSum (mixtureJointMass ε p r K L x) (mixturePriorMass ε p r x) := by
  have hsum : (∑' y, mixtureJointMass ε p r K L x y) = mixturePriorMass ε p r x := by
    simp only [mixtureJointMass, mixturePriorMass]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      PMF.tsum_coe, PMF.tsum_coe, mul_one, mul_one]
  exact hsum ▸ ENNReal.summable.hasSum

private noncomputable def mixtureChannel {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X) : PMF Y :=
  dite (mixturePriorMass ε p r x = 0) (fun _ => K x) (fun hx =>
    ⟨fun y => mixtureJointMass ε p r K L x y / mixturePriorMass ε p r x, by
      have hsum : (∑' y, mixtureJointMass ε p r K L x y /
          mixturePriorMass ε p r x) = 1 := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right, (mixtureJointMass_hasSum ε p r K L x).tsum_eq,
          ← div_eq_mul_inv, ENNReal.div_self hx (mixturePriorMass_ne_top ε p r x)]
      exact hsum ▸ ENNReal.summable.hasSum⟩)

private theorem mixtureChannel_of_zero {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X)
    (hx : mixturePriorMass ε p r x = 0) : mixtureChannel ε p r K L x = K x := by
  classical
  simp [mixtureChannel, hx]

private theorem mixtureChannel_apply_of_nonzero {X Y : Type} (ε : NNReal)
    (p r : PMF X) (K L : X → PMF Y) (x : X)
    (hx : mixturePriorMass ε p r x ≠ 0) (obs : Y) :
    mixtureChannel ε p r K L x obs =
      mixtureJointMass ε p r K L x obs / mixturePriorMass ε p r x := by
  classical
  simp [mixtureChannel, hx]
  rfl

/-- Normalized same-carrier interpolation, with the original channel as the
kernel-only zero-prior fallback. No observation finiteness is required. -/
noncomputable def mixtureModel {X Y : Type} [Fintype X] (ε : NNReal)
    (hε : ε ≤ 1) (p : PMF X) (K : X → PMF Y) (r : PMF X) (L : X → PMF Y) :
    PMF X × (X → PMF Y) :=
  (PMF.ofFintype (mixturePriorMass ε p r) (mixturePriorMass_sum ε hε p r),
    mixtureChannel ε p r K L)

private theorem mixtureModel_mul_channel {X Y : Type} [Fintype X]
    (ε : NNReal) (hε : ε ≤ 1) (p : PMF X) (K : X → PMF Y)
    (r : PMF X) (L : X → PMF Y) (x : X) (obs : Y) :
    (mixtureModel ε hε p K r L).1 x * (mixtureModel ε hε p K r L).2 x obs =
      mixtureJointMass ε p r K L x obs := by
  classical
  change mixturePriorMass ε p r x * mixtureChannel ε p r K L x obs = _
  by_cases hx : mixturePriorMass ε p r x = 0
  · rw [mixtureChannel_of_zero ε p r K L x hx, hx, zero_mul]
    have hzero := hx
    rw [mixturePriorMass] at hzero
    have hold := (add_eq_zero.mp hzero).1
    have haux := (add_eq_zero.mp hzero).2
    have hfirst : ((1 - ε : NNReal) : ENNReal) * p x * K x obs = 0 := by
      rw [hold, zero_mul]
    have hsecond : (ε : ENNReal) * r x * L x obs = 0 := by
      rw [haux, zero_mul]
    rw [mixtureJointMass, hfirst, hsecond, add_zero]
  · rw [mixtureChannel_apply_of_nonzero ε p r K L x hx]
    exact ENNReal.mul_div_cancel hx (mixturePriorMass_ne_top ε p r x)

/-- Observation evidence is exactly the affine interpolation of the two old
observation evidences. -/
theorem mixtureModel_evidence {X Y : Type} [Fintype X] (ε : NNReal)
    (hε : ε ≤ 1) (p : PMF X) (K : X → PMF Y)
    (r : PMF X) (L : X → PMF Y) (obs : Y) :
    observationEvidence (mixtureModel ε hε p K r L).1
        (mixtureModel ε hε p K r L).2 obs =
      ((1 - ε : NNReal) : ENNReal) * observationEvidence p K obs +
        (ε : ENNReal) * observationEvidence r L obs := by
  rw [observationEvidence_eq_sum, observationEvidence_eq_sum,
    observationEvidence_eq_sum]
  calc
    _ = ∑ x, (((1 - ε : NNReal) : ENNReal) * (p x * K x obs) +
        (ε : ENNReal) * (r x * L x obs)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [mixtureModel_mul_channel]
      simp only [mixtureJointMass, mul_assoc]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Retained positive evidence remains positive at every strict interior
weight, even when the auxiliary observation evidence vanishes. -/
theorem mixtureModel_evidence_pos {X Y : Type} [Fintype X] (ε : NNReal)
    (hε : ε < 1) (p : PMF X) (K : X → PMF Y)
    (r : PMF X) (L : X → PMF Y) (obs : Y)
    (hold : 0 < observationEvidence p K obs) :
    0 < observationEvidence (mixtureModel ε hε.le p K r L).1
      (mixtureModel ε hε.le p K r L).2 obs := by
  rw [mixtureModel_evidence]
  have hc : 0 < (((1 - ε : NNReal) : ENNReal)) := by
    exact_mod_cast (tsub_pos_of_lt hε)
  exact add_pos_of_pos_of_nonneg (ENNReal.mul_pos hc.ne' hold.ne') zero_le

/-- Every actual old-posterior support point is retained in the normalized
mixture posterior under strict retained mass. -/
theorem mixtureModel_posterior_support {X Y : Type} [Fintype X] (ε : NNReal)
    (hε : ε < 1) (p : PMF X) (K : X → PMF Y)
    (r : PMF X) (L : X → PMF Y) (obs : Y)
    (hold : 0 < observationEvidence p K obs) :
    (posterior p K obs hold).support ⊆
      (posterior (mixtureModel ε hε.le p K r L).1
        (mixtureModel ε hε.le p K r L).2 obs
        (mixtureModel_evidence_pos ε hε p K r L obs hold)).support := by
  intro x hx
  rw [PMF.mem_support_iff, posterior_apply] at hx ⊢
  rw [mixtureModel_mul_channel]
  have hnum : p x * K x obs ≠ 0 := by
    intro hz
    exact hx (by rw [hz, ENNReal.zero_div])
  have hp : p x ≠ 0 := fun hp => hnum (by simp [hp])
  have hK : K x obs ≠ 0 := fun hK => hnum (by simp [hK])
  have hc : 0 < (((1 - ε : NNReal) : ENNReal)) := by
    exact_mod_cast (tsub_pos_of_lt hε)
  have hfirst : 0 < ((1 - ε : NNReal) : ENNReal) * p x * K x obs :=
    ENNReal.mul_pos (ENNReal.mul_pos hc.ne' hp).ne' hK
  have hjoint : mixtureJointMass ε p r K L x obs ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hfirst zero_le)
  exact (ENNReal.div_pos hjoint
    (((mixtureModel ε hε.le p K r L).1.bind
      (mixtureModel ε hε.le p K r L).2).apply_ne_top obs)).ne'

/-- Zero mixture weight preserves the entire prior/channel pair, including
old-prior-zero and unobserved channel rows. -/
theorem mixtureModel_zero {X Y : Type} [Fintype X]
    (p : PMF X) (K : X → PMF Y) (r : PMF X) (L : X → PMF Y) :
    mixtureModel 0 (by simp) p K r L = (p, K) := by
  apply Prod.ext
  · apply PMF.ext
    intro x
    simp [mixtureModel, mixturePriorMass]
  · funext x
    change mixtureChannel 0 p r K L x = K x
    by_cases hD : mixturePriorMass 0 p r x = 0
    · exact mixtureChannel_of_zero 0 p r K L x hD
    · apply PMF.ext
      intro obs
      rw [mixtureChannel_apply_of_nonzero 0 p r K L x hD]
      have hp : p x ≠ 0 := by
        intro hp
        apply hD
        simp [mixturePriorMass, hp]
      change (((1 - 0 : NNReal) : ENNReal) * p x * K x obs +
          (0 : ENNReal) * r x * L x obs) / mixturePriorMass 0 p r x = K x obs
      simpa [mixturePriorMass, mul_comm] using
        (ENNReal.mul_div_cancel_right (a := K x obs) (b := p x) hp (p.apply_ne_top x))

/-- The finite retained-family weight: baseline zero and generic strict
interior points, with no `some` label at `n = 0`. -/
noncomputable def mixtureGridWeight {n : ℕ} : Option (Fin n) → NNReal
  | none => 0
  | some k => ((k.1 + 1 : ℕ) : NNReal) / ((n + 2 : ℕ) : NNReal)

theorem mixtureGridWeight_le_one {n : ℕ} (a : Option (Fin n)) :
    mixtureGridWeight a ≤ 1 := by
  cases a with
  | none => simp [mixtureGridWeight]
  | some k =>
      simp only [mixtureGridWeight]
      apply (div_le_one (by positivity)).2
      norm_cast
      omega

theorem mixtureGridWeight_lt_one {n : ℕ} (a : Option (Fin n)) :
    mixtureGridWeight a < 1 := by
  cases a with
  | none => simp [mixtureGridWeight]
  | some k =>
      simp only [mixtureGridWeight]
      apply (div_lt_one (by positivity)).2
      norm_cast
      have hk := k.isLt
      omega

theorem mixtureGridWeight_some_pos {n : ℕ} (k : Fin n) :
    0 < mixtureGridWeight (some k) := by
  simp only [mixtureGridWeight]
  positivity

theorem mixtureGrid_card (n : ℕ) : Fintype.card (Option (Fin n)) = n + 1 := by
  simp

private structure MixtureState {n : ℕ} {I X Y : Type} [Fintype X]
    (y : I → Y) where
  label : Option (Fin n)
  model : I → PMF X × (X → PMF Y)
  positive : ∀ i, 0 < observationEvidence (model i).1 (model i).2 (y i)

private noncomputable def mixtureFamily {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (m : I → PMF X × (X → PMF Y))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) :
    Option (Fin n) → I → PMF X × (X → PMF Y) := fun a i =>
  mixtureModel (mixtureGridWeight a) (mixtureGridWeight_le_one a)
    (m i).1 (m i).2 (aux a i).1 (aux a i).2

private theorem mixtureFamily_positive {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (m : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (m i).1 (m i).2 (y i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) (a : Option (Fin n))
    (i : I) :
    0 < observationEvidence (mixtureFamily m aux a i).1
      (mixtureFamily m aux a i).2 (y i) := by
  exact mixtureModel_evidence_pos (mixtureGridWeight a)
    (mixtureGridWeight_lt_one a) (m i).1 (m i).2 (aux a i).1 (aux a i).2
    (y i) (hold i)

private theorem mixtureFamily_support {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (m : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (m i).1 (m i).2 (y i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) (a : Option (Fin n))
    (i : I) :
    (posterior (m i).1 (m i).2 (y i) (hold i)).support ⊆
      (posterior (mixtureFamily m aux a i).1 (mixtureFamily m aux a i).2 (y i)
        (mixtureFamily_positive y m hold aux a i)).support := by
  exact mixtureModel_posterior_support (mixtureGridWeight a)
    (mixtureGridWeight_lt_one a) (m i).1 (m i).2 (aux a i).1 (aux a i).2
    (y i) (hold i)

private noncomputable def mixtureStateStep {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (s : MixtureState (n := n) (X := X) y)
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) : MixtureState (n := n) (X := X) y :=
  let q : I → PMF X := fun i => posterior (s.model i).1 (s.model i).2 (y i) (s.positive i)
  let F := mixtureFamily s.model aux
  let hE : ∀ a i, 0 < observationEvidence (F a i).1 (F a i).2 (y i) :=
    mixtureFamily_positive y s.model s.positive aux
  let hS : ∀ a i, (q i).support ⊆
      (posterior (F a i).1 (F a i).2 (y i) (hE a i)).support :=
    mixtureFamily_support y s.model s.positive aux
  let a := batchMStep q y F
  { label := a
    model := F a
    positive := (batchMStep_spec q y F hE hS).1.1 }

private noncomputable def mixtureState {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) :
    ℕ → MixtureState (n := n) (X := X) y
  | 0 => ⟨none, initial, initialPositive⟩
  | t + 1 => mixtureStateStep y (mixtureState y initial initialPositive seed t) (seed t)

/-- The actual model carried by the dependent positive-evidence state. -/
noncomputable def mixtureTrajectoryModel {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ) :
    I → PMF X × (X → PMF Y) :=
  (mixtureState y initial initialPositive seed t).model

/-- Bank zero is the unchanged initial model; bank `t+1` is constructed from
the actual current state model and seed `t`. -/
noncomputable def mixtureTrajectoryBank {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) :
    ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)
  | 0 => fun _ => initial
  | t + 1 => mixtureFamily (mixtureTrajectoryModel y initial initialPositive seed t) (seed t)

/-- Positive observation evidence of the actual dependent-state model. -/
theorem mixtureTrajectory_evidence {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y))
    (t : ℕ) (i : I) :
    0 < observationEvidence (mixtureTrajectoryModel y initial initialPositive seed t i).1
      (mixtureTrajectoryModel y initial initialPositive seed t i).2 (y i) := by
  exact (mixtureState y initial initialPositive seed t).positive i

private theorem mixtureTrajectoryBank_evidence {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) :
    ∀ t a i, 0 < observationEvidence
      (mixtureTrajectoryBank y initial initialPositive seed t a i).1
      (mixtureTrajectoryBank y initial initialPositive seed t a i).2 (y i) := by
  intro t
  cases t with
  | zero => exact fun _ i => initialPositive i
  | succ t =>
      exact mixtureFamily_positive y (mixtureTrajectoryModel y initial initialPositive seed t)
        (mixtureTrajectory_evidence y initial initialPositive seed t) (seed t)

/-- Pointwise successor equation for the actual trajectory bank. -/
theorem mixtureTrajectoryBank_succ {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y))
    (t : ℕ) (a : Option (Fin n)) (i : I) :
    mixtureTrajectoryBank y initial initialPositive seed (t + 1) a i =
      mixtureModel (mixtureGridWeight a) (mixtureGridWeight_le_one a)
        (mixtureTrajectoryModel y initial initialPositive seed t i).1
        (mixtureTrajectoryModel y initial initialPositive seed t i).2
        (seed t a i).1 (seed t a i).2 := by
  rfl

private noncomputable def mixtureCanonicalPath {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) : ℕ → Option (Fin n) :=
  changingEMPath y (mixtureTrajectoryBank y initial initialPositive seed)
    (mixtureTrajectoryBank_evidence y initial initialPositive seed) none

private theorem mixtureTrajectory_replay {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ) :
    (mixtureCanonicalPath y initial initialPositive seed t,
      mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t)) =
      ((mixtureState y initial initialPositive seed t).label,
        (mixtureState y initial initialPositive seed t).model) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      let s := mixtureState y initial initialPositive seed t
      let F := mixtureFamily s.model (seed t)
      let q : I → PMF X := fun i => posterior (s.model i).1 (s.model i).2 (y i) (s.positive i)
      have hmodel : mixtureTrajectoryBank y initial initialPositive seed t
          (mixtureCanonicalPath y initial initialPositive seed t) = s.model := congrArg Prod.snd ih
      let qB : I → PMF X := fun i => posterior
          (mixtureTrajectoryBank y initial initialPositive seed t
            (mixtureCanonicalPath y initial initialPositive seed t) i).1
          (mixtureTrajectoryBank y initial initialPositive seed t
            (mixtureCanonicalPath y initial initialPositive seed t) i).2 (y i)
          (mixtureTrajectoryBank_evidence y initial initialPositive seed t
            (mixtureCanonicalPath y initial initialPositive seed t) i)
      have hq : qB = q := by
        dsimp only [qB]
        funext i
        exact posterior_congr_of_model_eq _ _ _ _ _ (congrFun hmodel i)
      change (batchMStep qB y F, F (batchMStep qB y F)) =
        (batchMStep q y F, F (batchMStep q y F))
      rw [hq]

/-- The model selected by the canonical changing-bank path is exactly the
model carried by the dependent state, at the same time index. -/
theorem mixtureTrajectory_selected_model {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ) :
    mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) =
      mixtureTrajectoryModel y initial initialPositive seed t := by
  exact congrArg Prod.snd (mixtureTrajectory_replay y initial initialPositive seed t)

private theorem mixtureTrajectory_keep {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ) :
    mixtureTrajectoryBank y initial initialPositive seed (t + 1) none =
      mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) := by
  calc
    _ = mixtureTrajectoryModel y initial initialPositive seed t := by
      funext i
      exact mixtureModel_zero _ _ _ _
    _ = _ := (mixtureTrajectory_selected_model y initial initialPositive seed t).symm

private theorem mixtureTrajectory_close {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) (t : ℕ)
    (d : Option (Fin n)) (i : I) :
    (posterior
      (mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) i).1
      (mixtureTrajectoryBank y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) i).2 (y i)
      (mixtureTrajectoryBank_evidence y initial initialPositive seed t
        (mixtureCanonicalPath y initial initialPositive seed t) i)).support ⊆
    (posterior (mixtureTrajectoryBank y initial initialPositive seed (t + 1) d i).1
      (mixtureTrajectoryBank y initial initialPositive seed (t + 1) d i).2 (y i)
      (mixtureTrajectoryBank_evidence y initial initialPositive seed (t + 1) d i)).support := by
  let s := mixtureState y initial initialPositive seed t
  have hmodel : mixtureTrajectoryBank y initial initialPositive seed t
      (mixtureCanonicalPath y initial initialPositive seed t) = s.model :=
    mixtureTrajectory_selected_model y initial initialPositive seed t
  have hp := posterior_congr_of_model_eq _ _ (y i)
    (mixtureTrajectoryBank_evidence y initial initialPositive seed t
      (mixtureCanonicalPath y initial initialPositive seed t) i) (s.positive i)
    (congrFun hmodel i)
  rw [hp]
  exact mixtureFamily_support y s.model s.positive (seed t) d i

/-- Genuine integration: retained whole models and posterior support
closure make the actual canonical path NLL antitone. -/
theorem mixtureTrajectory_nll_antitone {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (y : I → Y) (initial : I → PMF X × (X → PMF Y))
    (initialPositive : ∀ i, 0 < observationEvidence (initial i).1 (initial i).2 (y i))
    (seed : ℕ → Option (Fin n) → I → PMF X × (X → PMF Y)) :
    Antitone (changingEMPathNLL y (mixtureTrajectoryBank y initial initialPositive seed)
      (mixtureTrajectoryBank_evidence y initial initialPositive seed) none) := by
  exact changingEMPath_nll_antitone y (mixtureTrajectoryBank y initial initialPositive seed)
    (mixtureTrajectoryBank_evidence y initial initialPositive seed) none (fun _ => none)
    (mixtureTrajectory_keep y initial initialPositive seed)
    (mixtureTrajectory_close y initial initialPositive seed)

end Hagi.Contracts.MixtureEMTrajectory


/-!
Canonical finite closed-family generalized-EM trajectories with fresh
exact current posteriors. Additive observation NLL is nonnegative and
nonincreasing, eventually constant, and has its historical infimum attained.
For a fixed candidate family and observations, zero NLL drop implies equal
refreshed posteriors and equality of the next canonical selected index.
No joint independence, global likelihood optimum, continuous parameter
convergence, varying-family model stability or runtime compute is asserted.
-/


set_option relaxedAutoImplicit false

open Hagi.Prelude
open Hagi.Probability
open Hagi.Probability.FiniteBayes
open Hagi.Probability.FiniteLogScore
open Hagi.Probability.FiniteEM
open Hagi.Probability.FiniteMultiEM
open Filter Topology
open scoped BigOperators ENNReal

namespace Hagi.Contracts.FiniteEMTrajectory

private noncomputable def currentPosterior {A I X Y : Type} [Fintype X]
    (y : I → Y) (c : A → I → PMF X × (X → PMF Y))
    (hE : ∀ a i, 0 < observationEvidence (c a i).1 (c a i).2 (y i))
    (a : A) : I → PMF X :=
  fun i => posterior (c a i).1 (c a i).2 (y i) (hE a i)

section
variable {A I X Y : Type} [Fintype A] [Nonempty A] [Fintype I] [Fintype X]
variable (y : I → Y) (c : A → I → PMF X × (X → PMF Y))
variable (hE : ∀ a i, 0 < observationEvidence (c a i).1 (c a i).2 (y i))
variable (hClose : ∀ base candidate i,
  (posterior (c base i).1 (c base i).2 (y i) (hE base i)).support ⊆
  (posterior (c candidate i).1 (c candidate i).2 (y i) (hE candidate i)).support)
variable (a₀ : A)

/-- Recursively select one global candidate using the freshly computed current posterior. -/
noncomputable def finiteEMPath (y : I → Y)
    (c : A → I → PMF X × (X → PMF Y))
    (hE : ∀ a i, 0 < observationEvidence (c a i).1 (c a i).2 (y i))
    (a₀ : A) : ℕ → A
  | 0 => a₀
  | n + 1 => batchMStep
      (currentPosterior y c hE (finiteEMPath y c hE a₀ n)) y c

/-- Additive negative log observation evidence at the selected global candidate. -/
noncomputable def finiteEMPathNLL (n : ℕ) : ℝ :=
  ∑ i, -Real.log (observationEvidence
    (c (finiteEMPath y c hE a₀ n) i).1
    (c (finiteEMPath y c hE a₀ n) i).2 (y i)).toReal

/-- Selected-path additive observation NLL is nonnegative. -/
theorem finiteEMPath_nll_nonneg (n : ℕ) :
    0 ≤ finiteEMPathNLL y c hE a₀ n := by
  exact total_negativeLogEvidence_nonneg
    (c (finiteEMPath y c hE a₀ n)) y

include hClose in
/-- Support closure makes the canonical selected-path NLL nonincreasing. -/
theorem finiteEMPath_nll_antitone :
    Antitone (finiteEMPathNLL y c hE a₀) := by
  apply antitone_nat_of_succ_le
  intro n
  simpa only [finiteEMPath, finiteEMPathNLL, currentPosterior] using
    (current_totalNegativeLogEvidence_le_batchMStep
      (currentPosterior y c hE (finiteEMPath y c hE a₀ n)) y c hE
      (fun d i => hClose (finiteEMPath y c hE a₀ n) d i)
      (finiteEMPath y c hE a₀ n) (fun _ => rfl))

private theorem finiteEMPath_range_finite :
    (Set.range (finiteEMPathNLL y c hE a₀)).Finite := by
  let V : A → ℝ := fun a => ∑ i, -Real.log
    (observationEvidence (c a i).1 (c a i).2 (y i)).toReal
  apply (Set.finite_range V).subset
  rintro z ⟨n, rfl⟩
  exact ⟨finiteEMPath y c hE a₀ n, rfl⟩

private theorem eventually_constant_of_antitone_finite_range
    (E : ℕ → ℝ) (hanti : Antitone E) (hfinite : (Set.range E).Finite) :
    ∃ N, ∀ t ≥ N, E t = E N := by
  obtain ⟨z, ⟨N, hN⟩, hmin⟩ :=
    Set.exists_min_image (Set.range E) id hfinite (Set.range_nonempty E)
  subst z
  refine ⟨N, ?_⟩
  intro t ht
  exact le_antisymm (hanti ht) (hmin (E t) (Set.mem_range_self t))

end


section
variable {A I X Y : Type} [Fintype A] [Nonempty A] [Fintype I] [Fintype X]
variable (y : I → Y) (c : A → I → PMF X × (X → PMF Y))
variable (hE : ∀ a i, 0 < observationEvidence (c a i).1 (c a i).2 (y i))
variable (hClose : ∀ base candidate i,
  (posterior (c base i).1 (c base i).2 (y i) (hE base i)).support ⊆
  (posterior (c candidate i).1 (c candidate i).2 (y i) (hE candidate i)).support)
variable (a₀ : A)

include hClose

/-- A flat NLL step fixes the next canonical choice through posterior equality. -/
theorem finiteEMPath_succ_eq_of_nll_eq (n : ℕ)
    (hflat : finiteEMPathNLL y c hE a₀ (n + 1) = finiteEMPathNLL y c hE a₀ n) :
    finiteEMPath y c hE a₀ (n + 2) = finiteEMPath y c hE a₀ (n + 1) := by
  let a := finiteEMPath y c hE a₀ n
  let q := currentPosterior y c hE a
  let b := batchMStep q y c
  have hS : ∀ d i, (q i).support ⊆
      (posterior (c d i).1 (c d i).2 (y i) (hE d i)).support :=
    fun d i => hClose a d i
  have hM : 0 ≤
      (∑ i, ceDef (fromPMF (q i)) (jointMass (c a i).1 (c a i).2 (y i))) -
      ∑ i, ceDef (fromPMF (q i)) (jointMass (c b i).1 (c b i).2 (y i)) := by
    exact sub_nonneg.mpr ((batchMStep_spec q y c hE hS).2 a)
  have hKL : ∀ i, 0 ≤ klDef (fromPMF (q i))
      (fromPMF (posterior (c b i).1 (c b i).2 (y i) (hE b i))) :=
    fun i => fromPMF_kl_nonneg _ _ (hClose a b i)
  have hnflat :
      (∑ i, ((-Real.log (observationEvidence (c a i).1 (c a i).2 (y i)).toReal) -
        (-Real.log (observationEvidence (c b i).1 (c b i).2 (y i)).toReal))) = 0 := by
    rw [Finset.sum_sub_distrib]
    have ha : finiteEMPathNLL y c hE a₀ n =
        ∑ i, -Real.log (observationEvidence (c a i).1 (c a i).2 (y i)).toReal := rfl
    rw [← show finiteEMPathNLL y c hE a₀ (n + 1) =
        ∑ i, -Real.log (observationEvidence (c b i).1 (c b i).2 (y i)).toReal by
      rfl]
    rw [← ha, hflat, sub_self]
  have hdrop := total_negativeLogEvidence_drop_eq
    (c a) (c b) y (hE a) (hE b) (fun i => hClose a b i)
  rw [hnflat] at hdrop
  have hKLsum_nonneg : 0 ≤ ∑ i, klDef (fromPMF (q i))
      (fromPMF (posterior (c b i).1 (c b i).2 (y i) (hE b i))) :=
    Finset.sum_nonneg (fun i _ => hKL i)
  have hKLsum : (∑ i, klDef (fromPMF (q i))
      (fromPMF (posterior (c b i).1 (c b i).2 (y i) (hE b i)))) = 0 := by
    dsimp only [q, currentPosterior] at hM hKLsum_nonneg ⊢
    exact le_antisymm (by linarith) hKLsum_nonneg
  have hKLzero : ∀ i, klDef (fromPMF (q i))
      (fromPMF (posterior (c b i).1 (c b i).2 (y i) (hE b i))) = 0 :=
    fun i => (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hKL j)).mp hKLsum i (Finset.mem_univ i)
  have hposterior : ∀ i, posterior (c b i).1 (c b i).2 (y i) (hE b i) =
      posterior (c a i).1 (c a i).2 (y i) (hE a i) := by
    intro i
    exact (fromPMF_kl_eq_zero_iff (q i)
      (posterior (c b i).1 (c b i).2 (y i) (hE b i))
      (hClose a b i)).mp (hKLzero i)
  have hq : currentPosterior y c hE b = currentPosterior y c hE a :=
    funext hposterior
  change batchMStep (currentPosterior y c hE b) y c =
    batchMStep (currentPosterior y c hE a) y c
  exact congrArg (fun r => batchMStep r y c) hq

/-- The fixed-family canonical selected-index path is eventually constant. -/
theorem finiteEMPath_eventually_constant :
    ∃ N, ∀ n ≥ N, finiteEMPath y c hE a₀ n = finiteEMPath y c hE a₀ N := by
  obtain ⟨N, hN⟩ := eventually_constant_of_antitone_finite_range
    (finiteEMPathNLL y c hE a₀) (finiteEMPath_nll_antitone y c hE hClose a₀)
    (finiteEMPath_range_finite y c hE a₀)
  refine ⟨N + 1, ?_⟩
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      have hflat : finiteEMPathNLL y c hE a₀ ((m - 1) + 1) =
          finiteEMPathNLL y c hE a₀ (m - 1) := by
        calc
          _ = finiteEMPathNLL y c hE a₀ N := hN ((m - 1) + 1) (by omega)
          _ = _ := (hN (m - 1) (by omega)).symm
      have hstep := finiteEMPath_succ_eq_of_nll_eq
        y c hE hClose a₀ (m - 1) hflat
      rw [show (m - 1) + 2 = m + 1 by omega,
        show (m - 1) + 1 = m by omega] at hstep
      exact hstep.trans ih

/-- The finite-range, antitone selected-path NLL is eventually constant. -/
theorem finiteEMPath_nll_eventually_constant :
    ∃ N, ∀ n ≥ N, finiteEMPathNLL y c hE a₀ n = finiteEMPathNLL y c hE a₀ N :=
  eventually_constant_of_antitone_finite_range
    (finiteEMPathNLL y c hE a₀) (finiteEMPath_nll_antitone y c hE hClose a₀)
    (finiteEMPath_range_finite y c hE a₀)

/-- Nonnegative antitone path NLL converges to its historical infimum. -/
theorem finiteEMPath_nll_tendsto_ciInf :
    Filter.Tendsto (finiteEMPathNLL y c hE a₀) Filter.atTop
      (nhds (⨅ n, finiteEMPathNLL y c hE a₀ n)) :=
  Hagi.Contracts.ObjectiveTrajectory.tendsto_ciInf_of_antitone_nonneg
    (finiteEMPathNLL y c hE a₀) (finiteEMPath_nll_antitone y c hE hClose a₀)
    (finiteEMPath_nll_nonneg y c hE a₀)

/-- The historical path infimum is attained at some selected index. -/
theorem finiteEMPath_nll_ciInf_attainment :
    ∃ N, finiteEMPathNLL y c hE a₀ N = ⨅ n, finiteEMPathNLL y c hE a₀ n := by
  obtain ⟨N, hN⟩ := finiteEMPath_nll_eventually_constant y c hE hClose a₀
  refine ⟨N, le_antisymm ?_ ?_⟩
  · apply le_ciInf
    intro t
    rcases le_total N t with ht | ht
    · rw [hN t ht]
    · exact (finiteEMPath_nll_antitone y c hE hClose a₀) ht
  · apply ciInf_le
    refine ⟨0, ?_⟩
    rintro z ⟨t, rfl⟩
    exact finiteEMPath_nll_nonneg y c hE a₀ t

end


end Hagi.Contracts.FiniteEMTrajectory

/-! # Factorized finite complete-CE selection over retained mixtures

Select one retained-mixture label per unit by minimizing the exact-current-
posterior complete cross-entropy over the finite `Option (Fin n)` grid. The
independent scalar objectives bound every vector of labels, agree with the
objective of the actual vector `batchMStep`, and imply aggregate observation
NLL nonincrease relative to the current model. Transparent cell-table and
vector-domain cardinalities count abstract candidates only, not evaluation
traces, execution time, or computational resources.
-/


set_option relaxedAutoImplicit false

open Hagi.Prelude
open Hagi.Probability
open Hagi.Probability.FiniteBayes
open Hagi.Probability.FiniteLogScore
open Hagi.Probability.FiniteEM
open Hagi.Probability.FiniteMultiEM
open Hagi.Contracts.MixtureEMTrajectory
open scoped BigOperators ENNReal

namespace Hagi.Contracts.FactorizedMixtureEM

/-- Exact posterior of the current unit model at its fixed observation. -/
noncomputable def mixtureCurrentPosterior {I X Y : Type} [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i)) (i : I) :
    PMF X :=
  posterior (old i).1 (old i).2 (obs i) (hold i)

/-- The vector-indexed bank of retained categorical mixtures. Auxiliary
prior/channel pairs may depend arbitrarily on both the label and the unit. -/
noncomputable def mixtureVectorBank {n : ℕ} {I X Y : Type} [Fintype X]
    (old : I → PMF X × (X → PMF Y))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y))
    (a : I → Option (Fin n)) : I → PMF X × (X → PMF Y) := fun i =>
  mixtureModel (mixtureGridWeight (a i)) (mixtureGridWeight_le_one (a i))
    (old i).1 (old i).2 (aux (a i) i).1 (aux (a i) i).2

/-- Complete CE at one unit and one label, using the exact current posterior
and the raw joint mass of the corresponding one-unit retained mixture. -/
noncomputable def mixtureUnitScore {n : ℕ} {I X Y : Type} [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) :
    (Σ _ : I, Option (Fin n)) → ℝ := fun j =>
  ceDef (fromPMF (mixtureCurrentPosterior obs old hold j.1))
    (jointMass (mixtureVectorBank old aux (fun _ => j.2) j.1).1
      (mixtureVectorBank old aux (fun _ => j.2) j.1).2 (obs j.1))

/-- Existing finite `mStep`, independently at each unit and over the complete
one-unit label grid. -/
noncomputable def factorizedMixtureLabels {n : ℕ} {I X Y : Type} [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) :
    I → Option (Fin n) := fun i =>
  mStep (mixtureCurrentPosterior obs old hold i) (obs i)
    (fun a => mixtureVectorBank old aux (fun _ => a) i)

/-- Every retained mixture vector has positive observation evidence; only
positivity of the old evidence is required. -/
theorem mixtureVectorBank_evidence_pos {n : ℕ} {I X Y : Type} [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y))
    (a : I → Option (Fin n)) (i : I) :
    0 < observationEvidence (mixtureVectorBank old aux a i).1
      (mixtureVectorBank old aux a i).2 (obs i) := by
  exact mixtureModel_evidence_pos (mixtureGridWeight (a i))
    (mixtureGridWeight_lt_one (a i)) (old i).1 (old i).2
    (aux (a i) i).1 (aux (a i) i).2 (obs i) (hold i)

/-- Every vector candidate retains the support of the exact old posterior. -/
theorem mixtureVectorBank_posterior_support {n : ℕ} {I X Y : Type} [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y))
    (a : I → Option (Fin n)) (i : I) :
    (mixtureCurrentPosterior obs old hold i).support ⊆
      (posterior (mixtureVectorBank old aux a i).1
        (mixtureVectorBank old aux a i).2 (obs i)
        (mixtureVectorBank_evidence_pos obs old hold aux a i)).support := by
  exact mixtureModel_posterior_support (mixtureGridWeight (a i))
    (mixtureGridWeight_lt_one (a i)) (old i).1 (old i).2
    (aux (a i) i).1 (aux (a i) i).2 (obs i) (hold i)

/-- The selected label minimizes the scalar complete CE at each unit. -/
theorem factorizedMixtureLabels_score_le {n : ℕ} {I X Y : Type} [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y))
    (i : I) (a : Option (Fin n)) :
    mixtureUnitScore obs old hold aux
        ⟨i, factorizedMixtureLabels obs old hold aux i⟩ ≤
      mixtureUnitScore obs old hold aux ⟨i, a⟩ := by
  let c : Option (Fin n) → PMF X × (X → PMF Y) :=
    fun b => mixtureVectorBank old aux (fun _ => b) i
  have hE : ∀ b, 0 < observationEvidence (c b).1 (c b).2 (obs i) := by
    intro b
    exact mixtureVectorBank_evidence_pos obs old hold aux (fun _ => b) i
  have hS : ∀ b, (mixtureCurrentPosterior obs old hold i).support ⊆
      (posterior (c b).1 (c b).2 (obs i) (hE b)).support := by
    intro b
    exact mixtureVectorBank_posterior_support obs old hold aux (fun _ => b) i
  exact (mStep_spec (mixtureCurrentPosterior obs old hold i) (obs i) c hE hS).2 a

/-- The independent selections minimize the total over the full Cartesian
vector domain, including the genuine empty sum when the unit type is empty. -/
theorem factorizedMixture_total_le {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y))
    (alternative : I → Option (Fin n)) :
    (∑ i, mixtureUnitScore obs old hold aux
        ⟨i, factorizedMixtureLabels obs old hold aux i⟩) ≤
      ∑ i, mixtureUnitScore obs old hold aux ⟨i, alternative i⟩ := by
  apply Finset.sum_le_sum
  intro i _hi
  exact factorizedMixtureLabels_score_le obs old hold aux i (alternative i)

open Classical in
/-- The per-unit selected objective equals the objective of the actual global
vector `batchMStep`; equality of selected labels or models is not asserted. -/
theorem factorizedMixture_eq_batchMStep_objective
    {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) :
    (∑ i, mixtureUnitScore obs old hold aux
        ⟨i, factorizedMixtureLabels obs old hold aux i⟩) =
      ∑ i, ceDef (fromPMF (mixtureCurrentPosterior obs old hold i))
        (jointMass
          (mixtureVectorBank old aux
            (batchMStep (mixtureCurrentPosterior obs old hold) obs
              (mixtureVectorBank old aux)) i).1
          (mixtureVectorBank old aux
            (batchMStep (mixtureCurrentPosterior obs old hold) obs
              (mixtureVectorBank old aux)) i).2 (obs i)) := by
  let q := mixtureCurrentPosterior obs old hold
  let c := mixtureVectorBank old aux
  have hE : ∀ a i, 0 < observationEvidence (c a i).1 (c a i).2 (obs i) := by
    intro a i
    exact mixtureVectorBank_evidence_pos obs old hold aux a i
  have hS : ∀ a i, (q i).support ⊆
      (posterior (c a i).1 (c a i).2 (obs i) (hE a i)).support := by
    intro a i
    exact mixtureVectorBank_posterior_support obs old hold aux a i
  apply le_antisymm
  · exact factorizedMixture_total_le obs old hold aux (batchMStep q obs c)
  · exact (batchMStep_spec q obs c hE hS).2
      (factorizedMixtureLabels obs old hold aux)

/-- The factorized total is bounded by every common-label diagonal score. -/
theorem factorizedMixture_shared_le {n : ℕ} {I X Y : Type} [Fintype I] [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y))
    (a : Option (Fin n)) :
    (∑ i, mixtureUnitScore obs old hold aux
        ⟨i, factorizedMixtureLabels obs old hold aux i⟩) ≤
      ∑ i, mixtureUnitScore obs old hold aux ⟨i, a⟩ := by
  exact factorizedMixture_total_le obs old hold aux (fun _ => a)

/-- Aggregate observation NLL of the directly selected vector bank is no larger
than that of the old vector. No unitwise or changing-path bound is asserted. -/
theorem factorizedMixture_nll_le_old {n : ℕ} {I X Y : Type}
    [Fintype I] [Fintype X]
    (obs : I → Y) (old : I → PMF X × (X → PMF Y))
    (hold : ∀ i, 0 < observationEvidence (old i).1 (old i).2 (obs i))
    (aux : Option (Fin n) → I → PMF X × (X → PMF Y)) :
    (∑ i, -Real.log (observationEvidence
        (mixtureVectorBank old aux (factorizedMixtureLabels obs old hold aux) i).1
        (mixtureVectorBank old aux (factorizedMixtureLabels obs old hold aux) i).2
        (obs i)).toReal) ≤
      ∑ i, -Real.log (observationEvidence (old i).1 (old i).2 (obs i)).toReal := by
  let selectedLabels := factorizedMixtureLabels obs old hold aux
  let selected := mixtureVectorBank old aux selectedLabels
  have hbase : mixtureVectorBank old aux (fun _ => none) = old := by
    funext i
    exact mixtureModel_zero _ _ _ _
  have hmin : (∑ i, ceDef
        (fromPMF (posterior (old i).1 (old i).2 (obs i) (hold i)))
        (jointMass (selected i).1 (selected i).2 (obs i))) ≤
      ∑ i, ceDef (fromPMF (posterior (old i).1 (old i).2 (obs i) (hold i)))
        (jointMass (old i).1 (old i).2 (obs i)) := by
    have h := factorizedMixture_total_le obs old hold aux (fun _ => none)
    simp only [mixtureUnitScore, mixtureCurrentPosterior, hbase] at h
    simpa only [mixtureVectorBank, selected, selectedLabels] using h
  have hE : ∀ i, 0 < observationEvidence (selected i).1 (selected i).2 (obs i) := by
    intro i
    exact mixtureVectorBank_evidence_pos obs old hold aux selectedLabels i
  have hS : ∀ i, (posterior (old i).1 (old i).2 (obs i) (hold i)).support ⊆
      (posterior (selected i).1 (selected i).2 (obs i) (hE i)).support := by
    intro i
    exact mixtureVectorBank_posterior_support obs old hold aux selectedLabels i
  exact total_negativeLogEvidence_le_of_total_completeCE_le
    old selected obs hold hE hS hmin

/-- Transparent cardinality of the scalar unit/label table. -/
theorem mixtureUnitQuery_card {I : Type} [Fintype I] (n : ℕ) :
    Fintype.card (Σ _ : I, Option (Fin n)) = Fintype.card I * (n + 1) := by
  classical
  simp only [Fintype.card_sigma, mixtureGrid_card]
  simp

open Classical in
/-- Transparent cardinality of the full vector-label candidate domain. -/
theorem mixtureVectorCandidate_card {I : Type} [Fintype I] (n : ℕ) :
    Fintype.card (I → Option (Fin n)) = (n + 1) ^ Fintype.card I := by
  simp only [Fintype.card_fun, mixtureGrid_card]

end Hagi.Contracts.FactorizedMixtureEM
