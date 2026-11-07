/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.FiniteEM

/-!
Finite multi-unit generalized expectation-maximization.

The additive negative log observation evidence drop decomposes exactly
into the total expected complete cross-entropy drop and the per-unit
posterior KL residuals. The finite selector chooses one global candidate
for the entire indexed assignment. Results require explicit positive
evidence and old-to-new posterior support; they do not assert unitwise
evidence improvement, stochastic independence or a joint likelihood.
-/


set_option relaxedAutoImplicit false

open Hagi.Prelude
open Hagi.Probability
open Hagi.Probability.FiniteBayes
open Hagi.Probability.FiniteLogScore
open Hagi.Probability.FiniteEM
open scoped BigOperators ENNReal


namespace Hagi.Probability.FiniteMultiEM

/-- The exact additive residual identity for a finite indexed family of
positive-evidence unit transitions. -/
theorem total_negativeLogEvidence_drop_eq {I X Y : Type} [Fintype I] [Fintype X]
    (m₀ m₁ : I → PMF X × (X → PMF Y)) (y : I → Y)
    (hobs₀ : ∀ i, 0 < observationEvidence (m₀ i).1 (m₀ i).2 (y i))
    (hobs₁ : ∀ i, 0 < observationEvidence (m₁ i).1 (m₁ i).2 (y i))
    (hS : ∀ i, (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)).support ⊆
      (posterior (m₁ i).1 (m₁ i).2 (y i) (hobs₁ i)).support) :
    (∑ i, ((-Real.log (observationEvidence (m₀ i).1 (m₀ i).2 (y i)).toReal) -
      (-Real.log (observationEvidence (m₁ i).1 (m₁ i).2 (y i)).toReal))) =
      ((∑ i, ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
        (jointMass (m₀ i).1 (m₀ i).2 (y i))) -
      (∑ i, ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
        (jointMass (m₁ i).1 (m₁ i).2 (y i)))) +
      ∑ i, klDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
        (fromPMF (posterior (m₁ i).1 (m₁ i).2 (y i) (hobs₁ i))) := by
  have hpoint : ∀ i,
      ((-Real.log (observationEvidence (m₀ i).1 (m₀ i).2 (y i)).toReal) -
        (-Real.log (observationEvidence (m₁ i).1 (m₁ i).2 (y i)).toReal)) =
      (ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
          (jointMass (m₀ i).1 (m₀ i).2 (y i)) -
        ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
          (jointMass (m₁ i).1 (m₁ i).2 (y i))) +
        klDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
          (fromPMF (posterior (m₁ i).1 (m₁ i).2 (y i) (hobs₁ i))) := by
    intro i
    have hold := ceDef_posterior_jointMass_sub_entDef_eq
      (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)
    have hnew := ceDef_jointMass_sub_entDef_eq (m₁ i).1 (m₁ i).2 (y i)
      (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)) (hobs₁ i) (hS i)
    linarith
  calc
    _ = ∑ i, ((ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
          (jointMass (m₀ i).1 (m₀ i).2 (y i)) -
        ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
          (jointMass (m₁ i).1 (m₁ i).2 (y i))) +
        klDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
          (fromPMF (posterior (m₁ i).1 (m₁ i).2 (y i) (hobs₁ i)))) :=
      Finset.sum_congr rfl (fun i _ => hpoint i)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Total generalized-M nonincrease bounds the next total log evidence by the
old total log evidence plus all retained posterior residuals. -/
theorem total_logEvidence_add_kl_le_of_total_completeCE_le
    {I X Y : Type} [Fintype I] [Fintype X]
    (m₀ m₁ : I → PMF X × (X → PMF Y)) (y : I → Y)
    (hobs₀ : ∀ i, 0 < observationEvidence (m₀ i).1 (m₀ i).2 (y i))
    (hobs₁ : ∀ i, 0 < observationEvidence (m₁ i).1 (m₁ i).2 (y i))
    (hS : ∀ i, (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)).support ⊆
      (posterior (m₁ i).1 (m₁ i).2 (y i) (hobs₁ i)).support)
    (hM : (∑ i, ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
        (jointMass (m₁ i).1 (m₁ i).2 (y i))) ≤
      ∑ i, ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
        (jointMass (m₀ i).1 (m₀ i).2 (y i))) :
    (∑ i, Real.log (observationEvidence (m₀ i).1 (m₀ i).2 (y i)).toReal) +
      (∑ i, klDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
        (fromPMF (posterior (m₁ i).1 (m₁ i).2 (y i) (hobs₁ i)))) ≤
      ∑ i, Real.log (observationEvidence (m₁ i).1 (m₁ i).2 (y i)).toReal := by
  have hdrop := total_negativeLogEvidence_drop_eq m₀ m₁ y hobs₀ hobs₁ hS
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_neg_distrib] at hdrop
  linarith

/-- Total generalized-M nonincrease implies aggregate additive negative log
evidence nonincrease, without any unitwise evidence claim. -/
theorem total_negativeLogEvidence_le_of_total_completeCE_le
    {I X Y : Type} [Fintype I] [Fintype X]
    (m₀ m₁ : I → PMF X × (X → PMF Y)) (y : I → Y)
    (hobs₀ : ∀ i, 0 < observationEvidence (m₀ i).1 (m₀ i).2 (y i))
    (hobs₁ : ∀ i, 0 < observationEvidence (m₁ i).1 (m₁ i).2 (y i))
    (hS : ∀ i, (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)).support ⊆
      (posterior (m₁ i).1 (m₁ i).2 (y i) (hobs₁ i)).support)
    (hM : (∑ i, ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
        (jointMass (m₁ i).1 (m₁ i).2 (y i))) ≤
      ∑ i, ceDef (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
        (jointMass (m₀ i).1 (m₀ i).2 (y i))) :
    (∑ i, -Real.log (observationEvidence (m₁ i).1 (m₁ i).2 (y i)).toReal) ≤
      ∑ i, -Real.log (observationEvidence (m₀ i).1 (m₀ i).2 (y i)).toReal := by
  have hdrop := total_negativeLogEvidence_drop_eq m₀ m₁ y hobs₀ hobs₁ hS
  have hkl : 0 ≤ ∑ i, klDef
      (fromPMF (posterior (m₀ i).1 (m₀ i).2 (y i) (hobs₀ i)))
      (fromPMF (posterior (m₁ i).1 (m₁ i).2 (y i) (hobs₁ i))) := by
    apply Finset.sum_nonneg
    intro i _
    exact fromPMF_kl_nonneg _ _ (hS i)
  rw [Finset.sum_sub_distrib] at hdrop
  linarith

/-- Every aggregate additive negative log evidence value is nonnegative,
including the totalized zero-evidence numerical boundary. -/
theorem total_negativeLogEvidence_nonneg {I X Y : Type} [Fintype I] [Fintype X]
    (m : I → PMF X × (X → PMF Y)) (y : I → Y) :
    0 ≤ ∑ i, -Real.log (observationEvidence (m i).1 (m i).2 (y i)).toReal := by
  apply Finset.sum_nonneg
  intro i _
  have hle : observationEvidence (m i).1 (m i).2 (y i) ≤ 1 :=
    PMF.coe_le_one ((m i).1.bind (m i).2) (y i)
  have hne : observationEvidence (m i).1 (m i).2 (y i) ≠ ⊤ :=
    ((m i).1.bind (m i).2).apply_ne_top (y i)
  have htoReal : (observationEvidence (m i).1 (m i).2 (y i)).toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hne ENNReal.one_ne_top).mpr hle
  exact neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg htoReal)

/-- One global finite-family minimizer of the total expected complete CE. -/
noncomputable def batchMStep {A I X Y : Type} [Fintype I] [Fintype X]
    [Fintype A] [Nonempty A] (q : I → PMF X) (y : I → Y)
    (c : A → I → PMF X × (X → PMF Y)) : A := by
  classical
  exact Classical.choose (Finite.exists_min (fun a =>
    ∑ i, ceDef (fromPMF (q i)) (jointMass (c a i).1 (c a i).2 (y i))))

/-- Selected admissibility and the full-family minimum for the global batch
selector, with no uniqueness assertion. -/
theorem batchMStep_spec {A I X Y : Type} [Fintype I] [Fintype X]
    [Fintype A] [Nonempty A] (q : I → PMF X) (y : I → Y)
    (c : A → I → PMF X × (X → PMF Y))
    (hE : ∀ a i, 0 < observationEvidence (c a i).1 (c a i).2 (y i))
    (hS : ∀ a i, (q i).support ⊆
      (posterior (c a i).1 (c a i).2 (y i) (hE a i)).support) :
    (((∀ i, 0 < observationEvidence (c (batchMStep q y c) i).1
        (c (batchMStep q y c) i).2 (y i)) ∧
      (∀ i, (q i).support ⊆ (posterior (c (batchMStep q y c) i).1
        (c (batchMStep q y c) i).2 (y i) (hE (batchMStep q y c) i)).support)) ∧
      (∀ a, (∑ i, ceDef (fromPMF (q i))
        (jointMass (c (batchMStep q y c) i).1 (c (batchMStep q y c) i).2 (y i))) ≤
        ∑ i, ceDef (fromPMF (q i)) (jointMass (c a i).1 (c a i).2 (y i)))) := by
  refine ⟨⟨hE (batchMStep q y c), hS (batchMStep q y c)⟩, ?_⟩
  exact Classical.choose_spec (Finite.exists_min (fun a =>
    ∑ i, ceDef (fromPMF (q i)) (jointMass (c a i).1 (c a i).2 (y i))))

/-- At the exact current posteriors, the selected global candidate has no
larger aggregate additive negative log evidence than the current candidate. -/
theorem current_totalNegativeLogEvidence_le_batchMStep
    {A I X Y : Type} [Fintype I] [Fintype X] [Fintype A] [Nonempty A]
    (q : I → PMF X) (y : I → Y)
    (c : A → I → PMF X × (X → PMF Y))
    (hE : ∀ a i, 0 < observationEvidence (c a i).1 (c a i).2 (y i))
    (hS : ∀ a i, (q i).support ⊆
      (posterior (c a i).1 (c a i).2 (y i) (hE a i)).support)
    (a₀ : A) (hq : ∀ i, q i = posterior (c a₀ i).1 (c a₀ i).2 (y i) (hE a₀ i)) :
    (∑ i, -Real.log (observationEvidence (c (batchMStep q y c) i).1
        (c (batchMStep q y c) i).2 (y i)).toReal) ≤
      ∑ i, -Real.log (observationEvidence (c a₀ i).1 (c a₀ i).2 (y i)).toReal := by
  have hqfun : q = fun i => posterior (c a₀ i).1 (c a₀ i).2 (y i) (hE a₀ i) :=
    funext hq
  subst q
  have hmin := (batchMStep_spec
    (fun i => posterior (c a₀ i).1 (c a₀ i).2 (y i) (hE a₀ i)) y c hE hS).2 a₀
  exact total_negativeLogEvidence_le_of_total_completeCE_le
    (c a₀) (c (batchMStep _ y c)) y (hE a₀) (hE _) (hS _) hmin

end Hagi.Probability.FiniteMultiEM
