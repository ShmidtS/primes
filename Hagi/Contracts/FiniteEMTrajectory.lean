/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.FiniteMultiEM
import Hagi.Contracts.ObjectiveTrajectory

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
