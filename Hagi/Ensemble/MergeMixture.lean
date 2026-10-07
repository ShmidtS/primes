/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

open scoped Matrix

/-!
# MergeMixture — merging preserves the mixture output under
stable routing (plan §2 R228; source 2609.32821)

The empirical finding (cosine 0.896–0.976 across 6 settings
with bootstrap CI): merging MoE weights preserves the
mixture output up to ROUTING drift. The exact structure:

* `merged_output_exact`: with FIXED routing weights w the
  merged expert (Σᵢ wᵢ • Wᵢ) reproduces the mixture output
  (Σᵢ wᵢ • Wᵢ)x EXACTLY — merge is output-preserving by
  linearity: the drift ≠ failure picture;
* `routing_drift_bound`: if the router drifts from w to w',
  the output deviation is at most Σᵢ |w'ᵢ − wᵢ| · ‖Wᵢ x‖ —
  the L₁ router drift times the branch gains: small router
  perturbations cannot break the merged output by more than
  their weighted magnitude (the formal counterpart of the
  0.9-cosine regime);
* boundary case (corollary of both): an exact router
  (w' = w) has zero L₁ drift, hence EXACTLY zero output
  deviation by `routing_drift_bound` — the empirical cosine
  gap is entirely the routing drift, not the merge itself.
-/

namespace Hagi

variable {d m : ℕ} (W : Fin m → Matrix (Fin d) (Fin d) ℝ)

/-- **Exact preservation under fixed routing**: the merged
matrix Σ wᵢ • Wᵢ applied to x equals the mixture output
Σ wᵢ • (Wᵢ x) exactly — merge commutes with the mixture;
whatever the disagreement story (R214), the mixture OUTPUT
is preserved by the merge itself. -/
theorem merged_output_exact (w : Fin m → ℝ) (x : Fin d → ℝ) :
    (∑ i, w i • W i) *ᵥ x = ∑ i, w i • (W i *ᵥ x) := by
  rw [Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun i _ => Matrix.smul_mulVec (w i) (W i) x

/-- **The routing drift bound**: a router perturbation
w → w' changes the merged output by at most the L₁ drift
times the branch gains ‖Wᵢ x‖ — small routing drift cannot
break the merged output by more than its weighted
magnitude. -/
theorem routing_drift_bound (w w' : Fin m → ℝ)
    (x : Fin d → ℝ)
    (hnorm : ∀ i, ‖W i *ᵥ x‖ ≤ B) :
    ‖(∑ i, w' i • W i) *ᵥ x - (∑ i, w i • W i) *ᵥ x‖
      ≤ ∑ i, |w' i - w i| * B := by
  have hsplit : (∑ i, w' i • W i) *ᵥ x - (∑ i, w i • W i) *ᵥ x
      = ∑ i, (w' i - w i) • (W i *ᵥ x) := by
    have h1 := merged_output_exact W w' x
    have h2 := merged_output_exact W w x
    rw [h1, h2]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← sub_smul]
  rw [hsplit]
  calc ‖∑ i, (w' i - w i) • (W i *ᵥ x)‖
      ≤ ∑ i, ‖(w' i - w i) • (W i *ᵥ x)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, |w' i - w i| * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ‖(w' i - w i) • (W i *ᵥ x)‖
            = |w' i - w i| * ‖W i *ᵥ x‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |w' i - w i| * B :=
              mul_le_mul_of_nonneg_left (hnorm i) (abs_nonneg _)

end Hagi
