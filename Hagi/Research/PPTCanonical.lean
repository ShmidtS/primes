/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Research.PPT
import Hagi.Probability.PMFBridge

/-!
# A canonical finite carrier for `discovery_prob_stationary`

Given an actual finite probability vector, identity sampling is measured
by its singleton masses. The two empirical inputs of the general theorem
therefore become proved facts on this constructed carrier. This says
nothing about how a runtime PPT chain is initialized or how it mixes.
-/

namespace Hagi.Discovery

open Finset Real MeasureTheory

/-- For a finite normalized law, the identity sampler from the
corresponding PMF has exactly the stated good-set probability. The
proof discharges the general theorem's fiber and distribution premises
rather than postulating them. -/
theorem discovery_prob_stationary_identity
    {Seq : Type} [Fintype Seq] [Nonempty Seq]
    [MeasurableSpace Seq] [MeasurableSingletonClass Seq]
    (V : Seq → ℝ) (gamma : ℝ) (pi : Seq → ℝ)
    (hnn : ∀ x, 0 ≤ pi x) (hsum : ∑ x, pi x = 1) :
    (Hagi.Probability.toPMF pi hnn hsum).toMeasure.real
        {ω | gamma ≤ V (id ω)}
      = ∑ x ∈ goodSet V gamma, pi x := by
  classical
  have hfiber : ∀ x : Seq, MeasurableSet {ω : Seq | id ω = x} := by
    intro x
    simpa only [id_eq, Set.ofPred_eq_eq_singleton] using
      measurableSet_singleton x
  have hdist : ∀ x : Seq,
      (Hagi.Probability.toPMF pi hnn hsum).toMeasure.real
        {ω : Seq | id ω = x} = pi x := by
    intro x
    have hset : {ω : Seq | id ω = x} = {x} := by
      ext ω
      simp only [Set.mem_ofPred_eq, id_eq, Set.mem_singleton_iff]
    rw [hset, MeasureTheory.Measure.real,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x),
      Hagi.Probability.toPMF_apply]
    exact ENNReal.toReal_ofReal (hnn x)
  exact discovery_prob_stationary
    (Hagi.Probability.toPMF pi hnn hsum).toMeasure
    V gamma pi id hfiber hdist

end Hagi.Discovery
