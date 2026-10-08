/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

set_option linter.style.header false

/-!
# FactorizedMerge: shared core + routed residuals (arXiv 2609.38597 structural principle)

Motivation (arXiv 2609.38597, PixelUMM): a shared multimodal
backbone with route-specific parameters and token routing. The
STRUCTURAL principle taken here (not the multimodality): instead
of collapsing N experts into one averaged model, decompose each
expert's weights as

`W_i = C + R_i`

— a SHARED CORE C plus a SPECIALIST RESIDUAL R_i, and evaluate
by ROUTING: the factorized model serves `C + R_{r(x)}` on route
r(x) instead of the average `(1/N) Σ W_i`.

What this module proves:

* the EXACT-DECOMPOSITION invariants (labeled as such, the
  `Core/Merge` step-0-exactness style): routed evaluation is
  EXACT (`routed_eval_exact`: the factorized form loses nothing
  per route), and the full averaging merge coincides with the
  factorized mean form (`merge_core_residual_identity`,
  `factorized_merge_exact`);
* the APPROXIMATE-core bounds (the honest content): if the
  measured core C fits the stored residuals only up to
  representation gaps δ_i, the distance between the full merge
  and `C + mean R` is bounded by the MEAN of the gaps
  (`factorized_error_bound`, via `mean_norm_le` — the norm of a
  mean is at most the mean of the norms), and the per-route gap
  is bounded by the same residual (`routed_approx_bound`);
* `factorized_budget` — the parameter accounting: with rank-r
  residuals (`Core/Element` `delta_rank_le` style: a factorized
  residual `A_i * B_i` has rank ≤ r) the factorized pool
  `V·d + N·(r·(V+d))` undercuts `N·(V·d)` of independent tables
  exactly when `N·r·(V+d) ≤ (N−1)·V·d`;
* `unified_error_budget` — the five-term triangle composition
  mirroring `Spectral/SpectralProjector.three_stage_error_budget`:
  shared-core fit + spectral tail + rank gap + quant rounding +
  routing switch compose with no cross terms.

**HONEST BOUNDARY (stated up front, not hidden):** PixelUMM
itself is NOT formalized here — no attention, no tokens, no
vision/audio streams. All merge-equivalence claims are
LINEAR-ALGEBRA level (normed-space arithmetic). The routing map
`r(x)` is a CARRIER only: there is NO routing-policy theorem
(no claim that any routing rule selects a good route, no bound
on routing mistakes — e_routing in the unified budget is an
input hypothesis about the switch, not a derived quantity).
The exact-decomposition lemmas are definitional invariants and
labeled as such; the approximate-core bounds carry the content.
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
/-- **Routed evaluation is EXACT (definitional invariant).**
Under the exact decomposition hypothesis `W i = C + R i`, the
factorized route reproduces the expert verbatim:
`factorizedEval C (R i) = W i`. The factorization loses NOTHING
per route — the counterpart of `Core/Merge`'s step-0 exactness:
this is the definitional invariant of the decomposition, not a
derived depth. -/
theorem routed_eval_exact (hdec : ∀ i, W i = C + R i) (i : ι) :
    factorizedEval C (R i) = W i := (hdec i).symm

/-- **The merge splits into core + mean residual (identity,
always true).** For ANY core C — no decomposition hypothesis —
the averaging merge is exactly `C + meanResidual (fun i => W i − C)`:
averaging `C + (W i − C)` returns C plus the mean of the shifted
residuals. This is the algebraic backbone of the error bounds:
the only gap between the merge and a stored factorized form is
the gap in the stored residuals. -/
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

/-- **Exact decomposition merges exactly (definitional
invariant).** With `W i = C + R i` for every i, the full
averaging merge IS the core plus the mean residual:
`fullMerge W = C + meanResidual R` — the averaged model and the
factorized representation coincide, no approximation anywhere.
The content is the sum manipulation (N copies of C average to
exactly C); the hypothesis is the decomposition itself. -/
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
/-- **The norm of a mean is at most the mean of the norms.**
`‖meanResidual f‖ ≤ Σ (1/N)·‖f i‖` — convexity of the norm at
the uniform average: smul scaling (`norm_smul`) plus the
triangle inequality over the index (`Finset.norm_sum_le`). This
is the engine of every averaging error bound below. -/
theorem mean_norm_le (f : ι → X) :
    ‖meanResidual f‖ ≤ ∑ i, (Fintype.card ι : ℝ)⁻¹ * ‖f i‖ := by
  have h1 : meanResidual f = ∑ i, (Fintype.card ι : ℝ)⁻¹ • f i := rfl
  rw [h1]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]

omit [NormedSpace ℝ X] [Fintype ι] [Nonempty ι] in
/-- **The per-route approximate-core bound.** If the STORED
residual `R i` represents the true shift `W i − C` only up to
δ_i, then the factorized route is δ_i-close to the expert:
`‖W i − (C + R i)‖ ≤ δ_i`. Routed evaluation with an imperfect
residual costs exactly the residual's representation gap. -/
theorem routed_approx_bound {δ : ι → ℝ}
    (hres : ∀ i, ‖R i - (W i - C)‖ ≤ δ i) (i : ι) :
    ‖W i - factorizedEval C (R i)‖ ≤ δ i := by
  have hEq : W i - factorizedEval C (R i) = -(R i - (W i - C)) := by
    unfold factorizedEval
    module
  rw [hEq, norm_neg]
  exact hres i

/-- **The factorized merge error is the MEAN of the
decomposition gaps.** With the core C and stored residuals R i
fitting the experts up to gaps `‖R i − (W i − C)‖ ≤ δ_i`, the
averaged model and the factorized representation satisfy

`‖fullMerge W − (C + meanResidual R)‖ ≤ (1/N) Σ δ_i`.

By `merge_core_residual_identity` the difference is EXACTLY the
mean of the gap vectors `(W i − C) − R i`, so the bound is
`mean_norm_le` applied pointwise — the factorization error is
controlled by Φ(δ) = mean of the measured decomposition
residuals, nothing else enters. -/
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

/-- **The factorized parameter budget.** N independent experts
cost `N·(V·d)` table parameters; the shared-core factorization
costs one core plus N rank-r residuals,
`V·d + N·(r·(V+d))` (per `Core/Element.params_count` /
`delta_rank_le`: a residual factorized as `A_i * B_i` with inner
dimension r has rank ≤ r and r·(V+d) parameters). The
factorized pool is CHEAPER exactly when the residuals fit in the
saved tables: `N·r·(V+d) ≤ (N−1)·V·d` (with N ≥ 2, so that a
saving is possible at all). -/
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

/-- **The five-term error budget of the quantized factorized
merge.** Target expert weight `W`; factorized representation
`C + R`; spectral projector `P` inserted into the residual
(R100 `SpectralProjector.spectralProj` — hard selection of the
informative subspace); low-rank approximation `A` of `P R`
(`Core/Element` factorization); quantized factors `QA`
(`Budget/ElementQuant` grid rounding); served output `S`. Then

`‖W − S‖ ≤ e_shared + e_spectral + e_rank + e_quant + e_routing`

with each term NAMED by its hypothesis and its source:

* `e_shared` — the factorization/decomposition fit
  `‖W − (C + R)‖` (this module, `factorized_error_bound` /
  `routed_approx_bound` supply it from measured per-expert gaps);
* `e_spectral` — the spectral tail `‖R − P R‖` (R100
  `spectral_tail_energy` evaluates it exactly);
* `e_rank` — the low-rank gap of the selected residual `‖P R − A‖`
  (`Core/Element` `delta_rank_le` style);
* `e_quant` — the grid rounding of the factors `‖A − QA‖`
  (`Budget/ElementQuant.factor_quant_error`);
* e_routing — the routing switch cost `‖(C + QA) − S‖` (an
  INPUT: no routing-policy theorem exists here — see the honest
  boundary).

The chain is a triangle composition mirroring
`three_stage_error_budget` (Grow→select→compress) extended by
the shared-core and routing terms: five named budget sources
compose with NO cross terms. -/
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
