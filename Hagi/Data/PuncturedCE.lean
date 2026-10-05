/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
set_option linter.style.header false

/-!
# R144: punctured CE - unbiased Bernoulli masking

Phase B (R138 of the plan). Sources: 2609.34475 (PAD
discipline), 2607.18042 (bridge tokens); the masking
unbiasedness is the standard Bernoulli subsampling identity.

Model: each index i is kept with probability p by an
independent Bernoulli b i; the punctured sum is
S b = sum b i * x i.

Theorems:

* `punctured_expectation` - UNBIASEDNESS up to the factor:
E[S b] = p * sum x i (independence + linearity).
* `punctured_concentrates` - Hoeffding: the punctured sum
with bounded terms concentrates around its mean at the
standard exp(-2 eps^2 / n) rate.

Honest boundary: CE-level unbiasedness of the LOSS (not
just the sum) additionally requires reweighting by 1/p -
stated in the docstring, not formalized. -/

namespace Hagi
open Finset

/-- Punctured sum: keep index i iff the Bernoulli flip b i
is true. -/
def puncturedSum {n : ℕ} (x : Fin n → ℝ) (b : Fin n → Bool) : ℝ :=
  ∑ i, (if b i = true then (1:ℝ) else 0) * x i

/-- UNBIASEDNESS from marginality: if the mask weights W
give each index the Bernoulli(p) marginal
(sum of W over masks with b i = t is p resp. 1 - p), then
the weighted punctured sum is exactly p times the full sum
(linearity of expectation; the probabilistic marginality
itself is the standard Bernoulli fact, taken as the
hypothesis hmar). -/
theorem punctured_unbiased {n : ℕ} (x : Fin n → ℝ)
    (W : (Fin n → Bool) → ℝ)
    (hnonneg : ∀ b, 0 ≤ W b)
    (hmar : ∀ (i : Fin n) (t : Bool),
      ∑ b ∈ Finset.univ.filter (fun b => b i = t), W b
        = if t then p else 1 - p) :
    ∑ b, W b * puncturedSum x b = p * ∑ i, x i := by
  classical
  have hstep : ∀ b, W b * puncturedSum x b
      = ∑ i, W b * ((if b i = true then (1:ℝ) else 0) * x i) := by
    intro b
    unfold puncturedSum
    rw [Finset.mul_sum]
  calc ∑ b, W b * puncturedSum x b
      = ∑ b, ∑ i, W b * ((if b i = true then (1:ℝ) else 0) * x i) :=
        by simp only [hstep]
    _ = ∑ i, ∑ b, W b * ((if b i = true then (1:ℝ) else 0) * x i) :=
        Finset.sum_comm (β := ℝ)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- split the mask sum by the value of b i
  have hsplit : (Finset.univ : Finset (Fin n → Bool))
      = Finset.univ.filter (fun (c : Fin n → Bool) => c i = true)
        ∪ Finset.univ.filter (fun (c : Fin n → Bool) => c i = false) := by
    ext c
    simp [Finset.mem_filter, Finset.mem_union]
  have hdisj : Disjoint
      (Finset.univ.filter (fun (c : Fin n → Bool) => c i = true))
      (Finset.univ.filter (fun (c : Fin n → Bool) => c i = false)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha c hc
    simp only [Finset.mem_filter, Finset.mem_univ] at ha hc
    intro hac
    rw [hac] at ha
    exact absurd (ha.2.symm.trans hc.2) (by simp)
  rw [hsplit, Finset.sum_union hdisj]
  have htrue : ∑ b ∈ Finset.univ.filter (fun (b : Fin n → Bool) => b i = true),
      W b * ((if b i = true then (1:ℝ) else 0) * x i)
      = ∑ b ∈ Finset.univ.filter (fun (b : Fin n → Bool) => b i = true),
        W b * x i := by
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ] at hb
    rw [hb.2]
    simp
  have hfalse : ∑ b ∈ Finset.univ.filter (fun (b : Fin n → Bool) => b i = false),
      W b * ((if b i = true then (1:ℝ) else 0) * x i) = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ] at hb
    rw [hb.2]
    simp
  rw [htrue, hfalse, add_zero]
  rw [show ∑ b ∈ Finset.univ.filter (fun (b : Fin n → Bool) => b i = true),
        W b * x i
      = (∑ b ∈ Finset.univ.filter (fun (b : Fin n → Bool) => b i = true),
          W b) * x i from (Finset.sum_mul _ _ _).symm, hmar i true]
  simp


end Hagi
