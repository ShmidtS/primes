/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# FactorizedMerge: shared core + routed residuals

Structural principle (source: arXiv 2609.38597): decompose each
expert as `W i = C + R i` — a shared core `C` plus a specialist
residual `R i` — and evaluate by routing: serve
`factorizedEval C (R i)` instead of the average `fullMerge W`.

* `routed_eval_exact` — under the exact decomposition
  `W i = C + R i`, the factorized route reproduces the expert.
* `merge_core_residual_identity`, `factorized_merge_exact` —
  the averaging merge equals `C + meanResidual (fun i => W i - C)`
  for any core; with an exact decomposition it equals
  `C + meanResidual R`.
* `mean_norm_le` — the norm of a mean is at most the mean of
  the norms.
* `routed_approx_bound` — if the stored residual fits the true
  shift to within `δ i`, the route is `δ i`-close to the expert.
* `factorized_error_bound` — the merge error is bounded by the
  mean of the decomposition gaps.
* `factorized_budget` — parameter accounting of the shared-core
  factorization.
* `unified_error_budget` — five-term triangle composition
  (shared-core fit, spectral tail, rank gap, quant rounding,
  routing switch) with no cross terms.

All statements are normed-space arithmetic; no routing-policy
theorem is claimed (`e_routing` is a hypothesis).
-/

open Finset

namespace Hagi

section Factorized

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable (W R : ι → X) (C : X)

/-- The full (averaging) merge of N experts: the collapsed model
`(1/N) Σ W_i` — what the factorized form is compared against. -/
noncomputable def fullMerge : X :=
  ∑ i, (Fintype.card ι : ℝ)⁻¹ • W i

/-- The mean of the residuals: the factorized counterpart of the
merge's averaging operation. -/
noncomputable def meanResidual : X :=
  ∑ i, (Fintype.card ι : ℝ)⁻¹ • R i

variable {W R C}

/-- The factorized (routed) evaluation: shared core + the
residual of the selected route. -/
def factorizedEval (C R : X) : X := C + R

/-! ### Exact decomposition: the definitional invariants -/

omit [NormedSpace ℝ X] [Fintype ι] [Nonempty ι] in
/-- If `W i = C + R i` for every `i` (exact decomposition),
then `factorizedEval C (R i) = W i`. -/
theorem routed_eval_exact (hdec : ∀ i, W i = C + R i) (i : ι) :
    factorizedEval C (R i) = W i := (hdec i).symm

/-- For any core `C` (no decomposition hypothesis),
`fullMerge W = C + meanResidual (fun i => W i - C)`. -/
theorem merge_core_residual_identity : fullMerge W
    = C + meanResidual (fun i => W i - C) := by
  have hcard : (0:ℝ) < (Fintype.card ι : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hsumC : ∑ i : ι, (Fintype.card ι : ℝ)⁻¹ • C = C := by
    have h0 : ∑ i : ι, (Fintype.card ι : ℝ)⁻¹ • C
        = (Fintype.card ι : ℝ)⁻¹ • ∑ i : ι, C := Finset.smul_sum.symm
    rw [h0, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul,
      inv_mul_cancel₀ (ne_of_gt hcard), one_smul]
  calc fullMerge W
      = ∑ i, (Fintype.card ι : ℝ)⁻¹ • (C + (W i - C)) := by
        unfold fullMerge
        exact Finset.sum_congr rfl fun i _ => by
          rw [add_comm C (W i - C), sub_add_cancel]
    _ = (∑ i : ι, (Fintype.card ι : ℝ)⁻¹ • C)
        + ∑ i, (Fintype.card ι : ℝ)⁻¹ • (W i - C) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => smul_add _ _ _
    _ = C + meanResidual (fun i => W i - C) := by
        unfold meanResidual
        rw [hsumC]

/-- With the exact decomposition `W i = C + R i` for every
`i`, `fullMerge W = C + meanResidual R`. -/
theorem factorized_merge_exact (hdec : ∀ i, W i = C + R i) :
    fullMerge W = C + meanResidual R := by
  rw [merge_core_residual_identity (W := W) (C := C)]
  unfold meanResidual
  exact congrArg (Add.add C)
    (Finset.sum_congr rfl fun i _ => by
      have h : W i - C = R i := by rw [hdec i, add_sub_cancel_left]
      simp only
      rw [h])

/-! ### Approximate core: the honest bounds -/

omit [Nonempty ι] in
/-- The norm of a mean is at most the mean of the norms:
`‖meanResidual f‖ ≤ ∑ i, (Fintype.card ι)⁻¹ * ‖f i‖`. -/
theorem mean_norm_le (f : ι → X) :
    ‖meanResidual f‖ ≤ ∑ i, (Fintype.card ι : ℝ)⁻¹ * ‖f i‖ := by
  have h1 : meanResidual f = ∑ i, (Fintype.card ι : ℝ)⁻¹ • f i := rfl
  rw [h1]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]

omit [NormedSpace ℝ X] [Fintype ι] [Nonempty ι] in
/-- If `‖R i - (W i - C)‖ ≤ δ i`, then
`‖W i - factorizedEval C (R i)‖ ≤ δ i`. -/
theorem routed_approx_bound {δ : ι → ℝ}
    (hres : ∀ i, ‖R i - (W i - C)‖ ≤ δ i) (i : ι) :
    ‖W i - factorizedEval C (R i)‖ ≤ δ i := by
  have hEq : W i - factorizedEval C (R i) = -(R i - (W i - C)) := by
    unfold factorizedEval
    module
  rw [hEq, norm_neg]
  exact hres i

/-- If `‖R i - (W i - C)‖ ≤ δ i` for every `i`, then
`‖fullMerge W - (C + meanResidual R)‖ ≤
∑ i, (Fintype.card ι)⁻¹ * δ i`: the merge error is bounded by
the mean of the decomposition gaps. -/
theorem factorized_error_bound {δ : ι → ℝ}
    (hres : ∀ i, ‖R i - (W i - C)‖ ≤ δ i) :
    ‖fullMerge W - (C + meanResidual R)‖
      ≤ ∑ i, (Fintype.card ι : ℝ)⁻¹ * δ i := by
  have hmean : meanResidual (fun i => W i - C) - meanResidual R
      = meanResidual (fun i => (W i - C) - R i) := by
    unfold meanResidual
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [smul_sub]
  have hsplit :
      fullMerge W - (C + meanResidual R)
        = meanResidual (fun i => (W i - C) - R i) :=
    calc fullMerge W - (C + meanResidual R)
        = C + meanResidual (fun i => W i - C) - (C + meanResidual R) := by
          rw [merge_core_residual_identity (W := W) (C := C)]
      _ = meanResidual (fun i => W i - C) - meanResidual R := by abel
      _ = meanResidual (fun i => (W i - C) - R i) := hmean
  have hnn : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    le_of_lt (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  rw [hsplit]
  calc ‖meanResidual (fun i => (W i - C) - R i)‖
      ≤ ∑ i, (Fintype.card ι : ℝ)⁻¹ * ‖(W i - C) - R i‖ :=
        mean_norm_le _
    _ ≤ ∑ i, (Fintype.card ι : ℝ)⁻¹ * δ i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (by rw [norm_sub_rev]; exact hres i) hnn

end Factorized

/-! ### Parameter budget -/

section Budget

/-- If `2 ≤ N` and the residuals fit in the saved tables
(`hsave`), then the shared-core pool `V * d + N * (r * (V + d))`
costs at most `N * (V * d)` of independent tables. -/
theorem factorized_budget (N V d r : ℕ) (hN : 2 ≤ N)
    (hsave : N * (r * (V + d)) ≤ (N - 1) * (V * d)) :
    V * d + N * (r * (V + d)) ≤ N * (V * d) := by
  obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  subst hk
  rw [Nat.add_sub_cancel] at hsave
  have hZ : V * d + k * (V * d) = (k + 1) * (V * d) := by ring
  have h1 : V * d + (k + 1) * (r * (V + d))
      ≤ V * d + k * (V * d) := by linarith
  linarith

end Budget

/-! ### The unified five-term budget -/

section Unified

variable {X : Type*} [NormedAddCommGroup X]

/-- Five-term triangle budget: given bounds on the shared-core
fit `‖W - (C + R)‖`, the spectral tail `‖R - P R‖`, the rank
gap `‖P R - A‖`, the quantization `‖A - QA‖`, and the routing
switch `‖(C + QA) - S‖`, the served error satisfies
`‖W - S‖ ≤ e_shared + e_spectral + e_rank + e_quant + e_routing`. -/
theorem unified_error_budget (W C R A QA S : X) (P : X → X)
    (e_shared e_spectral e_rank e_quant e_routing : ℝ)
    (hshared : ‖W - (C + R)‖ ≤ e_shared)
    (hspectral : ‖R - P R‖ ≤ e_spectral)
    (hrank : ‖P R - A‖ ≤ e_rank)
    (hquant : ‖A - QA‖ ≤ e_quant)
    (hrouting : ‖(C + QA) - S‖ ≤ e_routing) :
    ‖W - S‖ ≤ e_shared + e_spectral + e_rank + e_quant + e_routing := by
  have hterm : ‖R - QA‖ ≤ e_spectral + e_rank + e_quant := by
    have h1 : dist R QA ≤ dist R (P R) + dist (P R) QA :=
      dist_triangle R (P R) QA
    have h2 : dist (P R) QA ≤ dist (P R) A + dist A QA :=
      dist_triangle (P R) A QA
    simp only [dist_eq_norm] at h1 h2
    linarith [h1, h2, hspectral, hrank, hquant]
  have hmid : ‖(C + R) - (C + QA)‖ ≤ e_spectral + e_rank + e_quant := by
    have hEq : (C + R) - (C + QA) = R - QA := by abel
    rw [hEq]
    exact hterm
  have h1 : dist W S ≤ dist W (C + R) + dist (C + R) S :=
    dist_triangle W (C + R) S
  have h2 : dist (C + R) S
      ≤ dist (C + R) (C + QA) + dist (C + QA) S :=
    dist_triangle (C + R) (C + QA) S
  simp only [dist_eq_norm] at h1 h2
  linarith

end Unified

end Hagi
