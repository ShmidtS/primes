/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.SafeQP

set_option linter.style.header false

/-!
# Spectral selection: orthogonal projectors, tail energy, budget chains

Motivation (source: arXiv 2609.39440): hard selection of
informative spectral subspaces. The paper's dominance theorem is
NOT formalized here; only the selection primitives:

* `OrthProjPair` — the abstract orthogonal projector
  (self-adjoint idempotent), with the residual identity
  `proj_residual_identity`, `proj_residual_nonneg`,
  `proj_monotone`.
* `spectralProj` — the projector onto a subset of an
  orthonormal family (hard selection, no shrinkage):
  idempotent, self-adjoint, and the exact tail-energy identity
  `spectral_tail_energy` (dropped energy = sum of squared
  coefficients outside the kept set).
* `three_stage_error_budget` — selection tail + rank error +
  quantization error compose by the triangle inequality.
* `filtered_step_cost` / `spectral_safeQP_target` — a safe
  step from the spectrally filtered target costs the
  projection residual plus the filtering tail `‖g0 − P g0‖`.
-/

open Finset InnerProductSpace

namespace Hagi

section OrthProj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (P : E → E)

/-- The two defining properties of an orthogonal projector as
a hypothesis pair: idempotence and self-adjointness. -/
structure OrthProjPair where
  hProj : ∀ x, P (P x) = P x
  hSelfAdj : ∀ x y, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ

/-- For a self-adjoint idempotent `P`:
`‖x - P x‖ ^ 2 = ‖x‖ ^ 2 - ‖P x‖ ^ 2` — the energy splits
into kept and residual parts with no cross term. -/
theorem proj_residual_identity (h : OrthProjPair P) (x : E) :
    ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 - ‖P x‖ ^ 2 := by
  have hexp := norm_sub_sq_real x (P x)
  -- the cross term collapses: ⟪x, P x⟫ = ⟪P x, P x⟫ by
  -- self-adjointness applied at (P x, x) plus real symmetry
  have hcross : ⟪x, P x⟫_ℝ = ‖P x‖ ^ 2 := by
    have h1 : ⟪P (P x), x⟫_ℝ = ⟪P x, P x⟫_ℝ := h.hSelfAdj (P x) x
    rw [h.hProj x] at h1
    rw [real_inner_comm (P x) x, h1, real_inner_self_eq_norm_sq]
  rw [hcross] at hexp
  linarith

/-- The kept energy is at most the total energy:
`0 ≤ ‖x‖ ^ 2 - ‖P x‖ ^ 2`. -/
theorem proj_residual_nonneg (h : OrthProjPair P) (x : E) :
    0 ≤ ‖x‖ ^ 2 - ‖P x‖ ^ 2 := by
  have hid := proj_residual_identity P h x
  have hnn : 0 ≤ ‖x - P x‖ ^ 2 := sq_nonneg _
  linarith

/-- The projector is a contraction: `‖P x‖ ≤ ‖x‖`. -/
theorem proj_monotone (h : OrthProjPair P) (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  have hdef : ‖P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    linarith [proj_residual_nonneg P h x]
  calc ‖P x‖ = Real.sqrt (‖P x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hdef
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

end OrthProj

section SpectralTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → E}

/-- The spectral projector onto the kept subset `s` of the
orthonormal family `v`: keep coordinate i iff i ∈ s — HARD
selection, no shrinkage factors. -/
def spectralProj (s : Finset ι) (x : E) : E :=
  ∑ i ∈ s, ⟪x, v i⟫_ℝ • v i

variable {s : Finset ι}

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The spectral projector is idempotent.** Projecting twice
keeps the same coordinates — the coefficients of P x at kept
directions are unchanged (the family is orthonormal). -/
theorem spectralProj_idempotent (hv : Orthonormal ℝ v) (x : E) :
    spectralProj (v := v) s (spectralProj (v := v) s x)
      = spectralProj (v := v) s x := by
  unfold spectralProj
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [real_inner_comm (v i) (∑ j ∈ s, ⟪x, v j⟫_ℝ • v j),
    hv.inner_right_sum (fun j => ⟪x, v j⟫_ℝ) hi]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The spectral projector is self-adjoint** — the finitary
sum interchange of the two coefficient inner products. -/
theorem spectralProj_selfAdj (_hv : Orthonormal ℝ v) (x y : E) :
    ⟪spectralProj (v := v) s x, y⟫_ℝ = ⟪x, spectralProj (v := v) s y⟫_ℝ := by
  unfold spectralProj
  rw [sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm (v i) y]
  ring

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- The spectral projector carries the `OrthProjPair` structure
(idempotent + self-adjoint) — the abstract residual lemmas apply
to it verbatim. -/
theorem spectralProj_orth (hv : Orthonormal ℝ v) :
    OrthProjPair (spectralProj (v := v) s) where
  hProj := spectralProj_idempotent hv
  hSelfAdj := spectralProj_selfAdj hv

/-- If `x` lies in the span of the orthonormal family
(`hfull`), the energy left after hard selection of `s` is
exactly the sum of squared coefficients outside `s`:
`‖x - spectralProj s x‖ ^ 2 = ∑ i ∈ sᶜ, ⟪x, v i⟫_ℝ ^ 2`. -/
theorem spectral_tail_energy (hv : Orthonormal ℝ v) (x : E)
    (hfull : ∑ i : ι, ⟪x, v i⟫_ℝ • v i = x) :
    ‖x - spectralProj (v := v) s x‖ ^ 2
      = ∑ i ∈ sᶜ, ⟪x, v i⟫_ℝ ^ 2 := by
  -- the coefficient-split core: x − P_s x = the complementary sum
  have hcore : ∀ c : ι → ℝ, ∑ i : ι, c i • v i = x →
      x - ∑ i ∈ s, c i • v i = ∑ i ∈ sᶜ, c i • v i := by
    intro c hc
    rw [← hc, ← Finset.sum_add_sum_compl s (fun i => c i • v i),
      add_sub_cancel_left]
  -- norm squared of the complementary sum = sum of squared coefficients
  have hnorm : ∀ c : ι → ℝ,
      ‖∑ i ∈ sᶜ, c i • v i‖ ^ 2 = ∑ i ∈ sᶜ, c i ^ 2 := by
    intro c
    rw [← real_inner_self_eq_norm_sq,
      Orthonormal.inner_sum hv c c sᶜ]
    exact Finset.sum_congr rfl fun i _ => by simp; ring
  calc ‖x - spectralProj (v := v) s x‖ ^ 2
      = ‖∑ i ∈ sᶜ, ⟪x, v i⟫_ℝ • v i‖ ^ 2 := by
        rw [show x - spectralProj (v := v) s x
          = ∑ i ∈ sᶜ, ⟪x, v i⟫_ℝ • v i from
          hcore (fun i => ⟪x, v i⟫_ℝ) hfull]
    _ = ∑ i ∈ sᶜ, ⟪x, v i⟫_ℝ ^ 2 := hnorm (fun i => ⟪x, v i⟫_ℝ)

end SpectralTail

section Budget

variable {X : Type*} [NormedAddCommGroup X]

/-- The three-stage budget chain: given rank and quantization
error bounds, `‖W - QA‖ ≤ ‖W - P W‖ + eps_rank + eps_quant`
(selection tail + rank error + quantization error, triangle
inequality). -/
theorem three_stage_error_budget (W A QA : X) (P : X → X)
    (eps_rank eps_quant : ℝ)
    (hrank : ‖P W - A‖ ≤ eps_rank)
    (hquant : ‖A - QA‖ ≤ eps_quant) :
    ‖W - QA‖ ≤ ‖W - P W‖ + eps_rank + eps_quant := by
  have h1 : dist W QA ≤ dist W (P W) + dist (P W) QA :=
    dist_triangle W (P W) QA
  have h2 : dist (P W) QA ≤ dist (P W) A + dist A QA :=
    dist_triangle (P W) A QA
  simp only [dist_eq_norm] at h1 h2
  calc ‖W - QA‖ ≤ ‖W - P W‖ + ‖P W - QA‖ := h1
    _ ≤ ‖W - P W‖ + (‖P W - A‖ + ‖A - QA‖) := add_le_add le_rfl h2
    _ ≤ ‖W - P W‖ + eps_rank + eps_quant := by
        have : ‖P W - A‖ + ‖A - QA‖ ≤ eps_rank + eps_quant :=
          add_le_add hrank hquant
        linarith

end Budget

section SafeQPComposition

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K]

/-- For any `dstar`, `g0` and filter `P`:
`‖dstar - g0‖ ≤ ‖dstar - P g0‖ + ‖g0 - P g0‖` — acting from
the filtered target pays the filtering tail additively. -/
theorem filtered_step_cost (dstar g0 : X) (P : X → X) :
    ‖dstar - g0‖ ≤ ‖dstar - P g0‖ + ‖g0 - P g0‖ := by
  have hsplit : dstar - g0 = (dstar - P g0) + (P g0 - g0) := by abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_rev _ _).le)

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- There exists a step `dstar` in the safe set `safeSet g eps`
that is the projection (in the `safeQP_exists_unique` sense) of
the filtered target `P g0`, and its distance to the raw `g0` is
at most `‖dstar - P g0‖ + ‖g0 - P g0‖`. -/
theorem spectral_safeQP_target (g : K → X) (g0 : X) (eps : K → ℝ)
    (heps : ∀ i, 0 ≤ eps i) (P : X → X) (_h : OrthProjPair P)
    [FiniteDimensional ℝ X] :
    ∃ dstar : X, dstar ∈ safeSet g eps ∧
      (∀ c ∈ safeSet g eps, ‖dstar - P g0‖ ≤ ‖c - P g0‖) ∧
      ‖dstar - g0‖ ≤ ‖dstar - P g0‖ + ‖g0 - P g0‖ := by
  obtain ⟨dstar, ⟨hdmem, hdmin⟩, -⟩ :=
    safeQP_exists_unique g (P g0) eps heps
  refine ⟨dstar, hdmem, ?_, filtered_step_cost dstar g0 P⟩
  intro c hc
  have hle := hdmin c hc
  simpa only [dist_eq_norm] using hle

end SafeQPComposition

end Hagi
