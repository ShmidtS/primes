/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.MixtureEMTrajectory

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
