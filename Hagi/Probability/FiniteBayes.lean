/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.LinkedFlip
import Hagi.Probability.PMFBridge

/-!
Finite categorical Bayesian conditioning and sequence-zero-one decisions.
The latent carrier is finite, but an observation need not belong to a
finite carrier. Positive evidence is an explicit premise.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability.FiniteBayes

open scoped BigOperators ENNReal

open Hagi.Probability.LinkedFlip

/-- Joint evidence at one supplied observation. -/
noncomputable def observationEvidence {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y) : ENNReal :=
  (p₀.bind K) y

theorem observationEvidence_eq_sum {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y) :
    observationEvidence p₀ K y = ∑ x, p₀ x * K x y := by
  simp only [observationEvidence, PMF.bind_apply, tsum_fintype]

/-- Positive evidence supplies a latent support witness, including when
some other latent states have zero posterior mass. -/
theorem observationEvidence_pos_nonempty {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) : Nonempty X := by
  have hy : y ∈ (p₀.bind K).support := by
    apply (PMF.apply_pos_iff (p₀.bind K) y).mp
    simpa only [observationEvidence] using hobs
  obtain ⟨x, _, _⟩ := (PMF.mem_support_bind_iff p₀ K y).mp hy
  exact ⟨x⟩

/-- Exact normalized posterior; there is no zero-evidence fallback. -/
noncomputable def posterior {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) : PMF X := by
  classical
  refine PMF.ofFintype
    (fun x => p₀ x * K x y / observationEvidence p₀ K y) ?_
  simp only [ENNReal.div_eq_inv_mul]
  rw [← Finset.mul_sum, ← observationEvidence_eq_sum, mul_comm]
  exact ENNReal.mul_inv_cancel (ne_of_gt hobs) ((p₀.bind K).apply_ne_top y)

@[simp] theorem posterior_apply {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) (x : X) :
    posterior p₀ K y hobs x =
      p₀ x * K x y / observationEvidence p₀ K y := by
  rfl

/-- The normalized posterior depends only on the model, not on the chosen
positive-evidence proofs. -/
theorem posterior_congr_of_model_eq {X Y : Type} [Fintype X]
    (m₀ m₁ : PMF X × (X → PMF Y)) (obs : Y)
    (h₀ : 0 < observationEvidence m₀.1 m₀.2 obs)
    (h₁ : 0 < observationEvidence m₁.1 m₁.2 obs) (h : m₀ = m₁) :
    posterior m₀.1 m₀.2 obs h₀ = posterior m₁.1 m₁.2 obs h₁ := by
  subst m₁
  rfl

/-- Real posterior masses sum to one on the nonempty finite carrier. -/
theorem posterior_sum_toReal {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) :
    ∑ x, (posterior p₀ K y hobs x).toReal = 1 := by
  let _ : Nonempty X := observationEvidence_pos_nonempty p₀ K y hobs
  exact Hagi.Probability.fromPMF_sum (posterior p₀ K y hobs)

/-- Linked-noise posterior, with all equal-mask events coalesced in the
induced mask law rather than treated as independent coordinate events. -/
theorem linkedPosterior_apply {I : Type} [Fintype I] [DecidableEq I]
    (neighbors : I → Finset I) (ν : PMF (Option I)) (p₀ : PMF (Plane I))
    (y : Plane I)
    (hobs : 0 < observationEvidence p₀ (linkedChannel neighbors ν) y)
    (x : Plane I) :
    posterior p₀ (linkedChannel neighbors ν) y hobs x =
      p₀ x * (ν.map (eventMask neighbors)) (flip x y) /
        observationEvidence p₀ (linkedChannel neighbors ν) y := by
  have hmask : linkedChannel neighbors ν x y =
      (ν.map (eventMask neighbors)) (flip x y) := by
    rw [linkedChannel_apply]
    congr 1
  rw [posterior_apply, hmask]

/-- Expected loss for erring on any part of the reconstruction. -/
noncomputable def zeroOneLoss {X : Type} [Fintype X]
    (q : PMF X) (d : X) : ℝ := by
  classical
  exact ∑ x, (q x).toReal * if x = d then 0 else 1

/-- Exact posterior risk for whole-latent zero-one loss. -/
theorem zeroOneLoss_eq_one_sub {X : Type} [Fintype X] [Nonempty X]
    (q : PMF X) (d : X) : zeroOneLoss q d = 1 - (q d).toReal := by
  classical
  have hsplit : (∑ x, (q x).toReal * if x = d then 0 else 1) =
      (∑ x, (q x).toReal) - ∑ x, if x = d then (q d).toReal else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = d <;> simp [hx]
  rw [zeroOneLoss, hsplit, Hagi.Probability.fromPMF_sum]
  simp

/-- One classical posterior maximizer over the full finite carrier. -/
noncomputable def mode {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) : X :=
  let _ : Nonempty X := observationEvidence_pos_nonempty p₀ K y hobs
  Classical.choose (Finite.exists_max (posterior p₀ K y hobs))

theorem mode_posterior_le {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) (x : X) :
    posterior p₀ K y hobs x ≤ posterior p₀ K y hobs (mode p₀ K y hobs) := by
  let _ : Nonempty X := observationEvidence_pos_nonempty p₀ K y hobs
  exact Classical.choose_spec
    (Finite.exists_max (posterior p₀ K y hobs)) x

/-- A posterior mode minimizes whole-sequence zero-one risk on the full
finite family; this distinct objective is not coordinate-Hamming risk. -/
theorem mode_zeroOneLoss_le {X Y : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) (d : X) :
    zeroOneLoss (posterior p₀ K y hobs) (mode p₀ K y hobs) ≤
      zeroOneLoss (posterior p₀ K y hobs) d := by
  let _ : Nonempty X := observationEvidence_pos_nonempty p₀ K y hobs
  rw [zeroOneLoss_eq_one_sub, zeroOneLoss_eq_one_sub]
  apply sub_le_sub_left _ 1
  exact ENNReal.toReal_mono
    ((posterior p₀ K y hobs).apply_ne_top (mode p₀ K y hobs))
    (mode_posterior_le p₀ K y hobs d)

/-- The supplied-posterior optimum is at most as risky as returning the
observation itself, without any strict or empirical improvement claim. -/
theorem mode_zeroOneLoss_le_observation {X : Type} [Fintype X]
    (p₀ : PMF X) (K : X → PMF X) (y : X)
    (hobs : 0 < observationEvidence p₀ K y) :
    zeroOneLoss (posterior p₀ K y hobs) (mode p₀ K y hobs) ≤
      zeroOneLoss (posterior p₀ K y hobs) y :=
  mode_zeroOneLoss_le p₀ K y hobs y

end Hagi.Probability.FiniteBayes
