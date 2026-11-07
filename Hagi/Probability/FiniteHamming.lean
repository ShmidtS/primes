/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Probability.FiniteBayes
import Hagi.Probability.FreedmanTwoSided

/-!
Exact coordinatewise decisions for finite Boolean posterior laws.
The objective is expected changed-bit count, distinct from whole-plane
zero-one loss. Enumeration and runtime efficiency are not asserted.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Probability.FiniteHamming

open scoped BigOperators ENNReal
open Hagi.Probability.LinkedFlip
open Hagi.Probability.FiniteBayes

/-- The PMF of one Boolean coordinate under a supplied plane law. -/
noncomputable def coordinateLaw {I : Type*} (q : PMF (Plane I)) (i : I) : PMF Bool :=
  q.map (fun x => x i)

/-- One ordinary posterior-mass maximum on a Boolean coordinate. -/
noncomputable def coordinateMode {I : Type*} (q : PMF (Plane I)) (i : I) : Bool :=
  Classical.choose (Finite.exists_max (coordinateLaw q i))

/-- Coordinatewise posterior-marginal decoder. -/
noncomputable def coordinateDecoder {I : Type*} (q : PMF (Plane I)) : Plane I :=
  fun i => coordinateMode q i

/-- Expected number of changed coordinates under the supplied plane PMF. -/
noncomputable def hammingRisk {I : Type*} [Fintype I] [DecidableEq I]
    (q : PMF (Plane I)) (d : Plane I) : ℝ := by
  classical
  exact pmfMean q (fun x => (changedCount x d : ℝ))

/-- Changed count is the finite sum of Boolean-coordinate mismatches. -/
theorem changedCount_eq_sum {I : Type*} [Fintype I]
    (x d : Plane I) :
    (changedCount x d : ℝ) = ∑ i, if x i = d i then 0 else 1 := by
  classical
  simp only [changedCount, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : x i = d i <;> simp [h, bne_iff_ne]

/-- Exact marginal mass domination for the selected coordinate mode. -/
theorem coordinateLaw_le_coordinateMode {I : Type*} (q : PMF (Plane I)) (i : I)
    (b : Bool) :
    coordinateLaw q i b ≤ coordinateLaw q i (coordinateMode q i) := by
  exact Classical.choose_spec (Finite.exists_max (coordinateLaw q i)) b

/-- Coordinate risk is exactly the corresponding Bool zero-one loss. -/
theorem coordinateLoss_eq_pmfMean {I : Type*} [Fintype I] [DecidableEq I]
    (q : PMF (Plane I)) (i : I) (b : Bool) :
    zeroOneLoss (coordinateLaw q i) b =
      pmfMean q (fun x => if x i = b then 0 else 1) := by
  have hzero : zeroOneLoss (coordinateLaw q i) b =
      pmfMean (coordinateLaw q i) (fun c => if c = b then 0 else 1) := by
    simp only [zeroOneLoss, pmfMean]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> rfl
  rw [hzero, coordinateLaw, pmfMean_map]

/-- Expected changed-bit count decomposes into coordinatewise zero-one
risk. No independence or factorization of the plane PMF is assumed. -/
theorem hammingRisk_eq_sum_coordinateLoss {I : Type*} [Fintype I]
    [DecidableEq I] (q : PMF (Plane I)) (d : Plane I) :
    hammingRisk q d = ∑ i, zeroOneLoss (coordinateLaw q i) (d i) := by
  classical
  unfold hammingRisk
  simp_rw [changedCount_eq_sum]
  rw [pmfMean_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (coordinateLoss_eq_pmfMean q i (d i)).symm

/-- The selected coordinate minimizes Boolean zero-one loss. -/
theorem coordinateMode_zeroOneLoss_le {I : Type*} (q : PMF (Plane I)) (i : I)
    (b : Bool) :
    zeroOneLoss (coordinateLaw q i) (coordinateMode q i) ≤
      zeroOneLoss (coordinateLaw q i) b := by
  rw [zeroOneLoss_eq_one_sub, zeroOneLoss_eq_one_sub]
  apply sub_le_sub_left _ 1
  exact ENNReal.toReal_mono
    ((coordinateLaw q i).apply_ne_top (coordinateMode q i))
    (coordinateLaw_le_coordinateMode q i b)

/-- Coordinate posterior-marginal decoding minimizes expected changed-bit
risk over the full finite plane carrier; this is not sequence-MAP optimality. -/
theorem hammingRisk_coordinateDecoder_le {I : Type*} [Fintype I]
    [DecidableEq I] (q : PMF (Plane I)) (d : Plane I) :
    hammingRisk q (coordinateDecoder q) ≤ hammingRisk q d := by
  rw [hammingRisk_eq_sum_coordinateLoss, hammingRisk_eq_sum_coordinateLoss]
  apply Finset.sum_le_sum
  intro i _
  exact coordinateMode_zeroOneLoss_le q i (d i)

/-- The same exact risk optimum applies to any Cycle143 finite posterior. -/
theorem posterior_coordinateDecoder_le {I Y : Type} [Fintype I]
    [DecidableEq I] (p₀ : PMF (Plane I)) (K : Plane I → PMF Y) (y : Y)
    (hobs : 0 < observationEvidence p₀ K y) (d : Plane I) :
    hammingRisk (posterior p₀ K y hobs) (coordinateDecoder (posterior p₀ K y hobs)) ≤
      hammingRisk (posterior p₀ K y hobs) d := by
  exact hammingRisk_coordinateDecoder_le (posterior p₀ K y hobs) d

/-- In a same-carrier observation, returning the observed plane is only a
non-strict baseline for the marginalized Hamming-risk optimum. -/
theorem posterior_coordinateDecoder_le_observation {I : Type} [Fintype I]
    [DecidableEq I] (p₀ : PMF (Plane I)) (K : Plane I → PMF (Plane I))
    (y : Plane I) (hobs : 0 < observationEvidence p₀ K y) :
    hammingRisk (posterior p₀ K y hobs) (coordinateDecoder (posterior p₀ K y hobs)) ≤
      hammingRisk (posterior p₀ K y hobs) y := by
  exact posterior_coordinateDecoder_le p₀ K y hobs y

end Hagi.Probability.FiniteHamming
