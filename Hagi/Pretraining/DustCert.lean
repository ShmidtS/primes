/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Pretraining.Dust
import Hagi.Probability.KLSBridge

set_option linter.style.header false

/-!
# DustCert: the batch-noise chain closes on the zeroth-order
estimator

The KLS batch-noise theorem (`klsBatchNoise`) takes two
statistical hypotheses: centeredness and pairwise
uncorrelatedness of the per-sample gradient fields. For the
Dust zeroth-order estimator on the quadratic model the
relevant pieces are THEOREMS:

* `pairQ_isProb`/`pairQ_nonneg`: the uniform pair measure is
  a probability.
* `pairExpFirst`: finite Fubini — a first-component function
  has the pair expectation equal to its hypercube average.
* `pairExpProd`: the pair expectation of a product of
  one-component factors factorizes into the product of the
  hypercube averages.
* `dustUncorrPair`: any CENTERED error fields are
  uncorrelated under the pair measure — the huncorr
  hypothesis of `klsBatchNoise` promoted to a theorem (the
  centeredness of the estimator error is `esUnbiased`).

Honest boundary: the Poincaré premise and the sensitivity
bound of the KLS interface remain hypotheses; the
quadratic-model restriction is inherited from `esUnbiased`.
-/

namespace Hagi.Dust

open Finset

/-- The uniform measure on draw pairs. -/
noncomputable def pairQ (d : ℕ) : HC d × HC d → ℝ := fun _ => 1 / (2 ^ d * 2 ^ d)

/-- The pair measure sums to one. -/
theorem pairQ_isProb (d : ℕ) : ∑ p : HC d × HC d, pairQ d p = 1 := by
  simp only [pairQ, Finset.sum_const, smul_eq_mul]
  rw [show ((Finset.univ : Finset (HC d × HC d))).card = 2 ^ d * 2 ^ d from by
    simp [Fintype.card_prod, hcCard]]
  norm_num
  field_simp

/-- PairQ is nonnegative. -/
theorem pairQ_nonneg (d : ℕ) : ∀ p, 0 ≤ pairQ d p := by
  intro p
  unfold pairQ
  positivity

/-- **Finite Fubini (first component)**: a function depending
only on the first component has the pair expectation equal to
its hypercube average. -/
theorem pairExpFirst (d : ℕ) (F : HC d → ℝ) :
    KLS.expQ (pairQ d) (fun p => F p.1)
      = (∑ u ∈ (Finset.univ : Finset (HC d)), F u) / 2 ^ d := by
  unfold KLS.expQ pairQ
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) =>
    ((Finset.mul_sum (Finset.univ : Finset (HC d)) F
      (1 / (2 ^ d * 2 ^ d))).symm : (∑ x : HC d, (1 / (2 ^ d * 2 ^ d)) * F x)
      = (1 / (2 ^ d * 2 ^ d)) * ∑ x : HC d, F x))]
  rw [Finset.sum_const,
    show ((Finset.univ : Finset (HC d))).card = 2 ^ d from by
      simp [hcCard]]
  norm_num
  field_simp

/-- **Pair factorization**: the pair expectation of a product
of one-component factors equals the product of the hypercube
averages (finite Fubini on the product space). -/
theorem pairExpProd (d : ℕ) (φ ψ : HC d → ℝ) :
    KLS.expQ (pairQ d) (fun p => φ p.1 * ψ p.2)
      = ((∑ u ∈ (Finset.univ : Finset (HC d)), φ u) / 2 ^ d)
        * ((∑ v ∈ (Finset.univ : Finset (HC d)), ψ v) / 2 ^ d) := by
  unfold KLS.expQ pairQ
  rw [Fintype.sum_prod_type]
  -- regroup and factor over y
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    ((Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) =>
        (by ring : (1 / (2 ^ d * 2 ^ d)) * (φ x * ψ y)
          = ((1 / (2 ^ d * 2 ^ d)) * φ x) * ψ y))).trans
      (Finset.mul_sum (Finset.univ : Finset (HC d)) (fun y => ψ y)
        ((1 / (2 ^ d * 2 ^ d)) * φ x)).symm))]
  -- factor over x
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      (by ring : ((1 / (2 ^ d * 2 ^ d)) * φ x) * (∑ y : HC d, ψ y)
        = ((1 / (2 ^ d * 2 ^ d)) * (∑ y : HC d, ψ y)) * φ x)),
    (Finset.mul_sum (Finset.univ : Finset (HC d)) (fun x => φ x)
      ((1 / (2 ^ d * 2 ^ d)) * (∑ y : HC d, ψ y))).symm]
  rw [show ((1 / (2 ^ d * 2 ^ d)) * (∑ y : HC d, ψ y)) * (∑ x : HC d, φ x)
      = ((∑ x : HC d, φ x) / 2 ^ d) * ((∑ y : HC d, ψ y) / 2 ^ d) from by
    field_simp]

/-- **Draws are uncorrelated in the pair expectation**: any
centered error field is uncorrelated with ANY second field
under the pair measure — E[φ(u)·ψ(v)] = 0 whenever Σφ = 0.
For the zeroth-order estimator the centeredness of the
coordinate error is `esUnbiased`; this is the huncorr
hypothesis of `klsBatchNoise` promoted to a theorem. -/
theorem dustUncorrPair (d : ℕ) (φ ψ : HC d → ℝ)
    (hφ : ∑ u ∈ (Finset.univ : Finset (HC d)), φ u = 0) :
    KLS.expQ (pairQ d) (fun p => φ p.1 * ψ p.2) = 0 := by
  rw [pairExpProd, hφ]
  simp

end Hagi.Dust
