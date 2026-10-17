/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.Ortho
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
  step from the spectrally filtered target costs the
  projection residual plus the filtering tail `‖g0 − P g0‖`.
-/

open Finset InnerProductSpace

namespace Hagi.Spectral

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
      ‖∑ i ∈ sᶜ, c i • v i‖ ^ 2 = ∑ i ∈ sᶜ, c i ^ 2 :=
    fun c => Hagi.Foundations.ortho_norm_sq_finset hv c sᶜ
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
end Hagi.Spectral

namespace Hagi
export Hagi.Spectral (OrthProjPair proj_residual_identity proj_residual_nonneg proj_monotone spectralProj spectralProj_idempotent spectralProj_selfAdj spectralProj_orth spectral_tail_energy three_stage_error_budget)
end Hagi


set_option linter.style.header false

/-!
# SafeQP — линеаризованная проекция доменной безопасности для joint-шага

Направление joint-шага — проекция градиента смеси g на
пересечение полупространств безопасности
`K_safe = {d | ⟪g i, d⟫ ≥ −ε i для всех i}`.

* `safeQP_exists_unique`: при `0 ≤ ε i` и конечномерном X
  проекция на `safeSet` существует и единственна;
* `safeqp_inactive`: при `g0 ∈ safeSet` любой минимизатор ds
  равен g0.

Вспомогательные: `safeSet`, `halfspace_convex`,
`safeSet_nonempty`, `convex_min_unique`, `halfspace_closed`,
`safeSet_closed`.
-/

open Finset InnerProductSpace Metric

namespace Hagi.Step

section SafeQP

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K]

/-- Множество безопасности: направления, уважающие каждое
линеаризованное ограничение корпуса. -/
def safeSet (g : K → X) (eps : K → ℝ) : Set X :=
  {d : X | ∀ i, ⟪g i, d⟫_ℝ ≥ -eps i}

/-- `{d | ⟪g, d⟫_ℝ ≥ −eps}` выпукло (пересечение
полупространств). -/
theorem halfspace_convex (g : X) (eps : ℝ) :
    Convex ℝ {d : X | ⟪g, d⟫_ℝ ≥ -eps} := by
  intro x hx y hy a b ha hb hab
  change ⟪g, a • x + b • y⟫_ℝ ≥ -eps
  have hlin : ⟪g, a • x + b • y⟫_ℝ
      = a * ⟪g, x⟫_ℝ + b * ⟪g, y⟫_ℝ := by
    rw [show ⟪g, a • x + b • y⟫_ℝ
        = ⟪g, a • x⟫_ℝ + ⟪g, b • y⟫_ℝ from inner_add_right g (a • x) (b • y),
      inner_smul_right g x a, inner_smul_right g y b]
  rw [hlin]
  have h1 : a * ⟪g, x⟫_ℝ + b * ⟪g, y⟫_ℝ
      ≥ a * (-eps) + b * (-eps) :=
    add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
  have h2 : a * (-eps) + b * (-eps) = -eps := by
    have h3 : a * (-eps) + b * (-eps) = (a + b) * (-eps) := by ring
    rw [h3, hab, one_mul]
  linarith [h1, h2]

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- При `0 ≤ eps i` для всех i: `0 ∈ safeSet g eps`. -/
theorem safeSet_nonempty (g : K → X) (eps : K → ℝ)
    (heps : ∀ i, 0 ≤ eps i) :
    (0:X) ∈ safeSet g eps := by
  intro i
  show ⟪g i, (0:X)⟫_ℝ ≥ -eps i
  rw [inner_zero_right]
  linarith [heps i]

/-- Два различных минимизатора расстояния до g0 над
выпуклым S дают противоречие (строгая выпуклость нормы,
параллелограммное тождество). -/
theorem convex_min_unique (S : Set X) (hS : Convex ℝ S)
    (g0 x1 x2 : X) (h1 : x1 ∈ S) (h2 : x2 ∈ S) (hne : x1 ≠ x2)
    (r1 : ∀ d ∈ S, dist x1 g0 ≤ dist d g0)
    (r2 : ∀ d ∈ S, dist x2 g0 ≤ dist d g0) :
    False := by
  have hmid : (1/2 : ℝ) • x1 + (1/2 : ℝ) • x2 ∈ S := by
    refine hS h1 h2 (by norm_num) (by norm_num) (by norm_num)
  have hEq : ‖x1 - g0‖ = ‖x2 - g0‖ := by
    have e1 : dist x1 g0 ≤ dist x2 g0 := r1 x2 h2
    have e2 : dist x2 g0 ≤ dist x1 g0 := r2 x1 h1
    rw [dist_eq_norm x1 g0, dist_eq_norm x2 g0] at e1 e2
    exact le_antisymm e1 e2
  set u := x1 - g0 with hu
  set v := x2 - g0 with hv
  have hm : (1/2 : ℝ) • x1 + (1/2 : ℝ) • x2 - g0
      = (1/2 : ℝ) • (u + v) := by module
  have hnormm : ‖(1/2 : ℝ) • x1 + (1/2 : ℝ) • x2 - g0‖
      = (1/2) * ‖u + v‖ := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hpar : ‖u + v‖^2 + ‖u - v‖^2
      = 2 * ‖u‖^2 + 2 * ‖v‖^2 := by
    have ha := norm_add_pow_two (𝕜 := ℝ) u v
    have hb := norm_sub_pow_two (𝕜 := ℝ) u v
    simp only [ha, hb]
    ring
  have huvne : u - v ≠ 0 := by
    rw [hu, hv]
    have : x1 - g0 - (x2 - g0) = x1 - x2 := by abel
    rw [this]
    exact sub_ne_zero_of_ne hne
  have hpos : 0 < ‖u - v‖^2 := by
    have h2 : u ≠ v := by
      intro he
      apply huvne
      rw [he]
      exact sub_self v
    have hnn : 0 < ‖u - v‖ := norm_sub_pos_iff.mpr h2
    nlinarith [hnn]
  have hstrict : (1/4) * ‖u + v‖^2 < ‖u‖^2 := by
    have hrw : ‖u + v‖^2
        = 2 * ‖u‖^2 + 2 * ‖v‖^2 - ‖u - v‖^2 := by
      linarith [hpar]
    have huv : ‖u‖ = ‖v‖ := hEq
    rw [hrw, ← huv]
    nlinarith [hpos]
  have hfin : ‖x1 - g0‖
      ≤ ‖(1/2 : ℝ) • x1 + (1/2 : ℝ) • x2 - g0‖ := by
    have h := r1 _ hmid
    rwa [dist_eq_norm x1 g0, dist_eq_norm _ g0] at h
  rw [hnormm] at hfin
  have hfin2 : ‖u‖ ≤ (1/2) * ‖u + v‖ := hfin
  have hsq : ‖u‖^2 ≤ (1/4) * ‖u + v‖^2 := by
    have h := mul_self_le_mul_self (norm_nonneg u) hfin2
    nlinarith [h]
  linarith [hstrict, hsq]

/-- `{d | ⟪g, d⟫_ℝ ≥ −eps}` замкнуто (прообраз замкнутого
луча под непрерывным функционалом). -/
theorem halfspace_closed (g : X) (eps : ℝ) :
    IsClosed {d : X | ⟪g, d⟫_ℝ ≥ -eps} := by
  have hcont : Continuous fun d => ⟪g, d⟫_ℝ :=
    (continuous_const : Continuous fun _ : X => g).inner
      (continuous_id : Continuous fun d : X => d)
  have hpre : {d : X | ⟪g, d⟫_ℝ ≥ -eps}
      = (fun d => ⟪g, d⟫_ℝ) ⁻¹' (Set.Ici (-eps)) := rfl
  rw [hpre]
  exact IsClosed.preimage hcont (isClosed_Ici : IsClosed (Set.Ici (-eps)))

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- `safeSet g eps` замкнуто (конечное пересечение
замкнутых полупространств). -/
theorem safeSet_closed (g : K → X) (eps : K → ℝ) :
    IsClosed (safeSet g eps) := by
  have hEq : safeSet g eps
      = ⋂ i, {d : X | ⟪g i, d⟫_ℝ ≥ -eps i} := by
    ext d
    constructor <;> simp [safeSet]
  rw [hEq]
  exact isClosed_iInter
    (fun i => halfspace_closed (g i) (eps i))

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- При `0 ≤ eps i` и конечномерном X существует
единственный `ds ∈ safeSet g eps`, минимизирующий
расстояние до g0 (существование — компактификация,
единственность — `convex_min_unique`). -/
theorem safeQP_exists_unique (g : K → X) (g0 : X) (eps : K → ℝ)
    (heps : ∀ i, 0 ≤ eps i) [FiniteDimensional ℝ X] :
    ∃! ds : X, ds ∈ safeSet g eps ∧
      ∀ d ∈ safeSet g eps,
        dist ds g0 ≤ dist d g0 := by
  -- existence: compact minimization over S ∩ ball
  have hs0 : (0:X) ∈ safeSet g eps := safeSet_nonempty g eps heps
  set R := dist (0:X) g0 with hR
  have hTne : (safeSet g eps ∩ Metric.closedBall g0 R).Nonempty :=
    ⟨(0:X), hs0, Metric.mem_closedBall.mpr le_rfl⟩
  have hTcl : IsClosed (safeSet g eps ∩ Metric.closedBall g0 R) :=
    (safeSet_closed g eps).inter Metric.isClosed_closedBall
  have hTb : Bornology.IsBounded
      (safeSet g eps ∩ Metric.closedBall g0 R) :=
    Bornology.IsBounded.subset (Metric.isBounded_closedBall)
      (fun x hx => hx.2)
  have hTc : IsCompact (safeSet g eps ∩ Metric.closedBall g0 R) :=
    isCompact_of_isClosed_isBounded hTcl hTb
  obtain ⟨m, hmT, hmin⟩ := hTc.exists_isMinOn hTne
    ((continuous_dist.comp
      (continuous_id.prodMk continuous_const)).continuousOn)
  have helim : ∀ b ∈ (safeSet g eps ∩ Metric.closedBall g0 R),
      dist m g0 ≤ dist b g0 := hmin
  -- m is the global minimizer over the safe set
  have hglobal : ∀ d ∈ safeSet g eps, dist m g0 ≤ dist d g0 := by
    intro d hd
    by_cases hdR : dist d g0 ≤ R
    · exact helim d ⟨hd, Metric.mem_closedBall.mpr hdR⟩
    · have hmR : dist m g0 ≤ R :=
        helim (0:X) ⟨hs0, Metric.mem_closedBall.mpr le_rfl⟩
      exact le_trans hmR (by linarith)
  -- uniqueness: the convex_min_unique engine
  have hconv : Convex ℝ (safeSet g eps) := by
    intro x hx y hy a b ha hb hab
    intro i
    show ⟪g i, a • x + b • y⟫_ℝ ≥ -eps i
    exact halfspace_convex (g i) (eps i) (x := x) (hx i) (y := y) (hy i)
      (a := a) ha (b := b) hb hab
  refine ⟨m, ⟨hmT.1, hglobal⟩, ?_⟩
  intro d2 ⟨hd2mem, hd2min⟩
  by_contra hne2
  exact convex_min_unique (safeSet g eps) hconv g0 m d2
    hmT.1 hd2mem (fun h => hne2 h.symm) hglobal hd2min

end SafeQP

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- Если `ds` — минимизатор проекции и `g0 ∈ safeSet g eps`,
то `ds = g0` (расстояние 0 — абсолютный минимум). -/
theorem safeqp_inactive {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {K : Type} [Fintype K]
    (g : K → X) (g0 : X) (eps : K → ℝ)
    (_heps : ∀ i, 0 ≤ eps i)
    (ds : X)
    (hds : ds ∈ safeSet g eps ∧ ∀ d ∈ safeSet g eps, dist ds g0 ≤ dist d g0)
    (hsafe : g0 ∈ safeSet g eps) :
    ds = g0 := by
  obtain ⟨hs_mem, hmin⟩ := hds
  have h0min : dist ds g0 ≤ dist g0 g0 := hmin g0 hsafe
  rw [dist_self] at h0min
  have hdseq0 : dist ds g0 = 0 := le_antisymm h0min dist_nonneg
  exact eq_of_dist_eq_zero hdseq0
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

end Hagi.Step

namespace Hagi
export Hagi.Step (safeSet halfspace_convex safeSet_nonempty convex_min_unique halfspace_closed safeSet_closed safeQP_exists_unique safeqp_inactive filtered_step_cost spectral_safeQP_target)
end Hagi
