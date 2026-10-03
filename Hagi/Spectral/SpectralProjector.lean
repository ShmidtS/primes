/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Step.SafeQP

set_option linter.style.header false

/-!
# Spectral selection: orthogonal projectors, tail energy, budget chains

Motivation (arXiv 2609.39440): PCR — hard selection of informative
spectral subspaces — *dominates* monotone spectral filters
(ridge/shrinkage families): the principle that keeping a subspace
exactly and discarding the rest can beat smoothly shrinking
everything.

**HONEST BOUNDARY (stated up front, not hidden):** the paper's
dominance theorem itself is NOT formalized here. That theorem is
linear-regression-specific (minimax risk over coefficient classes
against a monotone-filter competitor class) and out of scope for
HAGI's primitive layer. What this module builds is the *selection
primitive* layer:

* the abstract orthogonal projector (self-adjoint idempotent) and
  its residual identity (`proj_residual_identity` — Pythagoras for
  the selected/dropped complementary subspaces);
* the concrete finite spectral projector `spectralProj` onto a
  subset of an orthonormal family, with the exact TAIL-ENERGY
  identity `spectral_tail_energy` (the dropped energy is the sum
  of squared coefficients outside the kept set — the exact form
  of which `RecursiveGrowth.gating_tail_bound` is the norm bound
  and `topk_routing_optimal` the optimality statement);
* the three-stage error budget `three_stage_error_budget`
  (Grow→select→compress): selection tail + rank error
  (`RankBudget` waterfilling residue) + quantization error
  (`ElementQuant` grid rounding) compose by the triangle
  inequality — each term NAMED, matching the existing budget
  modules;
* the spectral SafeQP target `spectral_safeQP_target` +
  `filtered_step_cost`: projecting the step onto the safe set
  `SafeQP.safeSet` from the *denoised* (spectrally filtered)
  target P g costs at most the projection residual plus the
  filtering tail ‖g − P g‖.

The claim "hard selection beats shrinkage" stays EMPIRICAL /
external to this module: nothing here asserts any dominance — the
primitives are dominance-agnostic.
-/

open Finset InnerProductSpace

namespace Hagi

section OrthProj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (P : E → E)

/-- The two defining properties of an orthogonal projector,
packaged as a hypothesis pair: idempotence (P ∘ P = P) and
self-adjointness. A self-adjoint idempotent map is the orthogonal
projector onto its fixed subspace; we keep the properties as an
explicit hypothesis pair (the `Core/Element` low-rank-residual
style: hypotheses, not a new structure). -/
structure OrthProjPair where
  hProj : ∀ x, P (P x) = P x
  hSelfAdj : ∀ x y, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ

/-- **The residual identity (Pythagoras for the selected and
dropped subspaces).** For a self-adjoint idempotent P,
`‖x − P x‖² = ‖x‖² − ‖P x‖²`: the total energy splits exactly
into the kept part and the residual, with NO cross term —
self-adjointness plus idempotence kill it
(`⟪x, P x⟫ = ⟪P x, P x⟫ = ‖P x‖²`). This is the abstraction
level at which spectral selection operates: whatever the
subspace, the residual energy is the complement of the kept
energy. -/
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

/-- **The kept energy is at most the total energy** (the
nonnegativity of the tail). Equivalent to `0 ≤ ‖x − P x‖²` by
the residual identity; stated as a deficit inequality because
that is the form the budget chain consumes
(`ElementQuant` tail style). -/
theorem proj_residual_nonneg (h : OrthProjPair P) (x : E) :
    0 ≤ ‖x‖ ^ 2 - ‖P x‖ ^ 2 := by
  have hid := proj_residual_identity P h x
  have hnn : 0 ≤ ‖x - P x‖ ^ 2 := sq_nonneg _
  linarith

/-- **Monotonicity: selecting cannot amplify.** `‖P x‖ ≤ ‖x‖`:
the projector is a contraction — from the residual identity by
squaring-monotonicity (both norms nonnegative). -/
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

/-- **The exact tail-energy identity.** With the full-family
expansion hypothesis `hfull : ∑ i, ⟪x, v i⟫ • v i = x` (x lies
in the span of the orthonormal family — Parseval holds; for a
general x in an infinite-dimensional space this is the honest
finite-span restriction, stated as a hypothesis, not derived),
the energy left after HARD selection of `s` is exactly the sum
of squared coefficients OUTSIDE `s`:

`‖x − P_s x‖² = ∑_{i ∉ s} ⟪x, v i⟫²`.

This is the exact form underlying `gating_tail_bound` (the norm
bound on dropped branches) and `topk_routing_optimal` (top-k
optimality) in `Unified/RecursiveGrowth`: the tail is the
COMPLEMENT of the kept coordinates, not a shrunk version of
them — hard selection, no leakage. -/
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

/-- **The three-stage Grow→select→compress budget chain.**
For a target `W` (the grown element / tensor), a spectral
selection `P` (any map; only its residual enters the bound), a
rank approximation `A` of the selected part with error
`ε_rank`, and a quantizer output `Q A` with error `ε_quant`:

`‖W − Q A‖ ≤ ‖W − P W‖ + ε_rank + ε_quant`

— the SELECTION TAIL (the spectral residual, evaluated exactly
by `spectral_tail_energy` / bounded by the `RankBudget`
waterfilling residue), the RANK ERROR (the low-rank
factorization gap of the selected part, `Core/Element`
`delta_rank_le` style), and the QUANT ERROR (`ElementQuant`
grid rounding) add up by the triangle inequality. Each term is
NAMED in the hypotheses; the chain is the composition
certificate: the three budget modules' bounds compose without
cross terms. -/
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

/-- **The filtered-step cost (triangle at the denoised target).**
For any step `dstar` and any target `g0` with spectral filter
`P`: `‖dstar − g0‖ ≤ ‖dstar − P g0‖ + ‖g0 − P g0‖` — acting
from the filtered target pays the filtering tail `‖g0 − P g0‖`
additively on top of the distance to the filtered target. The
residual cost of the spectral SafeQP composition. -/
theorem filtered_step_cost (dstar g0 : X) (P : X → X) :
    ‖dstar - g0‖ ≤ ‖dstar - P g0‖ + ‖g0 - P g0‖ := by
  have hsplit : dstar - g0 = (dstar - P g0) + (P g0 - g0) := by abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_rev _ _).le)

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- **The spectral SafeQP target (composition theorem).**
Given the closed-convex safe set `safeSet g eps` of `SafeQP.lean`
and the spectrally filtered target `P g0` (P a self-adjoint
idempotent — e.g. `spectralProj` by `spectralProj_orth`), there
EXISTS a step d* that (1) lies in the safe set, (2) is the
projection of the FILTERED target: its distance `‖d* − P g0‖`
dominates every safe alternative c, and (3) by
`filtered_step_cost` its distance to the RAW gradient g0 is at
most the projection residual plus the filtering tail
`‖g0 − P g0‖` (which `spectral_tail_energy` evaluates exactly
for a spectral P). Existence/uniqueness of the projection is
SafeQP's own `safeQP_exists_unique` applied to the denoised
target; the content here is the composition: a SAFE STEP from
a DENOISED target, with the additive tail cost. -/
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
