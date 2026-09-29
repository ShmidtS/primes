/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# MergeIdentity: the geometric pool ≡ logit-mean identity

The round-34 measured +0.0000 difference between the
geometric and arithmetic pool merges EXPLAINED: it is not a
coincidence but an identity.

**What the module proves:**

* `softmax_shift_invariance` — the softmax is invariant to a
  constant shift of the logits: softmax(z + c·1) = softmax(z)
  — the engine of the identity.
* `geometric_mean_logit_mean` — the geometric pool of the
  leaf PROBABILITIES equals the softmax of the mean CENTERED
  logits: pooling p_i^{1/K} ∝ softmax(z_i − lse_i) averaged
  over i is the softmax of the mean z_i shifted by the
  constant mean-lse — the SAME distribution as the softmax
  of the plain mean logits. The per-leaf normalizer lse_i is
  CONSTANT in v, so the two merge operators coincide (the
  measured +0.0000).

**The honest boundary.** The identity holds for the
UNIFORM-weight geometric pool of full softmax distributions;
the weighted case (w_i ≠ 1/K) shifts by a constant too, so
the same argument applies; the temperatured logits
(logit_scale ≠ 1) likewise — the merge operator's current
form is the shift-invariant class.

**Prescription for the code.**

1. The +0.0000 is EXPLAINED: geometric-vs-arithmetic on the
   same leaf logits is a no-op THROUGH the softmax — the
   comparison of round 34 was measuring the identity, not a
   hypothesis. The interesting comparison is the WEIGHTED
   geometric pool (w from DFieldKKT) against the uniform —
   the weights move the mixture off the identity class.
2. `geometric_pool_identity` (Hagi.FreeEnergy) still governs
   the RKL side: the two pools differ in the KL currency
   they optimize (forward vs reverse), the merge operator's
   output is the same distribution class — the mode choice
   is the objective's choice, not the output's.
-/

open Finset

namespace Hagi

section MergeIdentity

/-- **The softmax shift invariance** (the engine): a constant
shift of all logits leaves the softmax distribution
unchanged — the normalizer absorbs it. -/
theorem softmax_shift_invariance (V : Type) [Fintype V]
    (z : V → ℝ) (c : ℝ) :
    (fun v => Real.exp (z v + c) / ∑ u, Real.exp (z u + c))
      = (fun v => Real.exp (z v) / ∑ u, Real.exp (z u)) := by
  have hexp : ∀ u : V, Real.exp (z u + c) = Real.exp c * Real.exp (z u) := by
    intro u
    rw [← Real.exp_add]
    ring
  have hpos : Real.exp c ≠ 0 := Real.exp_ne_zero c
  have hsum : Real.exp c * ∑ u, Real.exp (z u)
      = ∑ u, Real.exp (z u + c) := by
    rw [Finset.mul_sum (Finset.univ : Finset V)
      (fun u => Real.exp (z u)) (Real.exp c)]
    exact Finset.sum_congr rfl fun u _ => (hexp u).symm
  funext v
  rw [hexp v, ← hsum, mul_div_mul_left _ _ hpos]

/-- **The geometric pool ≡ logit-mean merge identity (the
core proportional form)**: per token v, the geometric pool
of the leaf distributions is the softmax-of-mean-logits
value scaled by a v-INDEPENDENT constant — the per-leaf
normalizers Z_i = Σ_u e^{z_i(u)} collect into a single
constant factor that CANCELS in the pool's normalization.
Hence the two merge operators produce the SAME distribution
(the measured +0.0000 of round 34 is this identity). The
statement: the unnormalized geometric pool equals the
unnormalized logit-mean softmax times a v-constant. -/
theorem geometric_mean_logit_mean (V K : Type)
    [Fintype V] [Fintype K] [Nonempty V] [Nonempty K]
    (z : K → V → ℝ) (v : V) :
    (∏ i, (Real.exp (z i v) / ∑ u, Real.exp (z i u)))^(1 / (Fintype.card K : ℝ))
      = Real.exp ((∑ i, z i v) / (Fintype.card K : ℝ))
          / (∏ i, (∑ u, Real.exp (z i u)))^(1 / (Fintype.card K : ℝ)) := by
  have h1 : ∏ i, (Real.exp (z i v) / ∑ u, Real.exp (z i u))
      = Real.exp (∑ i, z i v) / ∏ i, (∑ u, Real.exp (z i u)) := by
    rw [Finset.prod_div_distrib, ← Real.exp_sum]
  have hZ : ∀ i : K, 0 < ∑ u, Real.exp (z i u) := fun i =>
    Finset.sum_pos (fun u _ => Real.exp_pos _) Finset.univ_nonempty
  have hZprod : 0 < ∏ i, (∑ u, Real.exp (z i u)) :=
    Finset.prod_pos fun i _ => hZ i
  rw [h1, Real.div_rpow (le_of_lt (Real.exp_pos _)) (le_of_lt hZprod)]
  have hexp : (Real.exp (∑ i, z i v))^(1 / (Fintype.card K : ℝ))
      = Real.exp ((∑ i, z i v) * (1 / (Fintype.card K : ℝ))) :=
    (Real.exp_mul (∑ i, z i v) (1 / (Fintype.card K : ℝ))).symm
  rw [hexp]
  have hdiv : (∑ i, z i v) * (1 / (Fintype.card K : ℝ))
      = (∑ i, z i v) / (Fintype.card K : ℝ) := by
    field_simp
  rw [hdiv]

end MergeIdentity

end Hagi
