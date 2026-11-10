/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.FiniteMultiEM
import Hagi.Contracts.ObjectiveTrajectory

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
  have hs : Summable F := summable_of_sum_range_le hF hbound
  exact ⟨hbound, hs, hs.tendsto_atTop_zero, hs.tsum_le_of_sum_range_le hbound⟩

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
