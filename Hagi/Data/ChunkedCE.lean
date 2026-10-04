/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Ensemble.QFormerBridge
set_option linter.style.header false

/-!
# R146: chunked CE - exact piecewise summation + prior decomposition

Phase B (R138 of the plan, remainder). Sources: 2609.32100
(exact definition of valid token positions + protocol),
2607.16666 (subsampling with rate correction),
2607.10951 (one-sample unbiasedness transfer).

Theorems:

* `chunked_sum_exact` - EXACTNESS of chunked summation:
if T = n * w, the token sum splits into n chunks of width w
with NO loss - the chunked CE equals the full CE.
* `ce_prior_decomposition` - CE = H(prior) + KL correction:
cross-entropy against q decomposes as the prior entropy
plus the KL divergence (proper objective).

Honest boundary: the valid-position protocol (masking of
padding) follows 2609.32100; here positions are all valid.
-/

namespace Hagi
open Finset

/-- EXACTNESS of chunked summation: with T = n * w the sum
over T positions is the sum over n chunks of width w. -/
theorem chunked_sum_exact (n w : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (n * w), f i
      = ∑ c ∈ Finset.range n, ∑ j ∈ Finset.range w,
          f (c * w + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : Finset.range ((n + 1) * w)
          = Finset.range (n * w)
            ∪ Finset.Ico (n * w) ((n + 1) * w) := by
        ext i
        simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico,
          Nat.add_mul]
        omega
      have hdisj : Disjoint (Finset.range (n * w))
          (Finset.Ico (n * w) ((n + 1) * w)) := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb
        simp only [Finset.mem_range] at ha
        simp only [Finset.mem_Ico] at hb
        omega
      have hico : ∑ i ∈ Finset.Ico (n * w) ((n + 1) * w), f i
          = ∑ j ∈ Finset.range w, f (n * w + j) := by
        rw [Finset.sum_Ico_eq_sum_range f, Nat.add_mul,
          show n * w + 1 * w - n * w = w from by omega]
      rw [hsplit, Finset.sum_union hdisj, hico, ih,
        Finset.sum_range_succ]

/-- CE = H(prior) + KL correction: the cross-entropy of q
against the uniform-free decomposition. For distribution p
(prior) and q (model), CE q p = entropy p + KL p q on a
finite type. -/
theorem ce_prior_decomposition {V : Type} [Fintype V]
    (p q : V → ℝ) (hp : ∀ v, 0 < p v) (hpsum : ∑ v, p v = 1)
    (hq : ∀ v, 0 < q v) (hqsum : ∑ v, q v = 1) :
    ∑ v, p v * Real.log (q v)
      = ∑ v, p v * Real.log (p v)
        + ∑ v, p v * Real.log (q v / p v) := by
  have hterm : ∀ v, p v * Real.log (q v / p v)
      = p v * Real.log (q v) - p v * Real.log (p v) := by
    intro v
    rw [Real.log_div (ne_of_gt (hq v)) (ne_of_gt (hp v))]
    ring
  rw [Finset.sum_congr rfl (fun v _ => hterm v),
    Finset.sum_sub_distrib]
  ring

end Hagi
