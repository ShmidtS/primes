/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Math.Foundations.Ortho
import Hagi.Probability.Concentration
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Probability.KLSBridge
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

namespace Hagi
export Hagi.Spectral (OrthProjPair proj_residual_identity proj_residual_nonneg proj_monotone spectralProj spectralProj_idempotent spectralProj_selfAdj spectralProj_orth spectral_tail_energy three_stage_error_budget)
end Hagi


set_option linter.style.header false

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
export Hagi.Step (safeSet safeQP_exists_unique)
end Hagi

set_option linter.style.header false

/-!
# StochasticSafeQP — минибатч-градиенты и допустимость с высокой вероятностью

Минибатч-оценка `ĝ_i = g_i + (1/m)·Σⱼ ξ_{i,j}`; шум входит в
ограничения только через проекции `⟪ξ_{i,j}, d⟫`.
Явная константа:
`ε_noise = σ·‖d‖·√(2·log(|K|/δ)/m)`.

* `minibatch_inner_tail`: односторонний хвост Hoeffding —
  `μ{m·ε ≤ Σⱼ (−Nⱼ)} ≤ exp(−m·ε²/(2R²))` для измеримых,
  средне-нулевых независимых `|Nⱼ| ≤ R`;
* `minibatch_inner_concentration` (нижний хвост) и
  `minibatch_inner_concentration_upper` (верхний): с
  вероятностью ≥ 1 − δ для всех i
  `⟪g i, d⟫ − ε_noise ≤ ⟪ĝ i, d⟫ ≤ ⟪g i, d⟫ + ε_noise`;
* `stochastic_safeQP_feasibility`: с вероятностью ≥ 1 − δ
  из стохастической сертификации d по ĝ_i с бюджетами
  `eps i` следует `⟪g i, d⟫ ≥ −(eps i + ε_noise)` для всех i.

d — фиксированное направление (адаптивный выбор — в
`Hagi.Step.AdaptiveSafeQP`); среднее-нулевость, ограниченность
`‖ξ‖ ≤ σ` и поштучная независимость — эмпирические
посылки; двусторонние/sub-Gaussian режимы — открыто.
-/

open Finset Real MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal

namespace Hagi.Step

section StochasticSafeQP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- Явный шумовой порог минибатча:
`noiseEps K sigma d m delta = σ·‖d‖·√(2·log(|K|/δ)/m)`. -/
noncomputable def noiseEps (K : Type*) [Fintype K] (sigma : ℝ) (d : X) (m : ℕ) (delta : ℝ) : ℝ :=
  sigma * ‖d‖ * Real.sqrt (2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ))

/-- Односторонний хвост Hoeffding: если `N j` измеримы,
независимы, средне-нулевые с `|N j ω| ≤ R` и `0 ≤ ε`, то
`μ.real {ω | m·ε ≤ Σⱼ −N j ω} ≤ exp(−m·ε²/(2R²))`. -/
theorem minibatch_inner_tail {m : ℕ} (hm : 0 < m)
    (N : Fin m → Ω → ℝ) (R : ℝ) (hR : 0 < R)
    (h_meas : ∀ j, Measurable (N j))
    (h_indep : iIndepFun N μ)
    (h_zero : ∀ j, μ[N j] = 0)
    (h_bound : ∀ j ω, |N j ω| ≤ R)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
      ≤ Real.exp (- (m : ℝ) * ε ^ 2 / (2 * R ^ 2)) := by
  classical
  -- the negated family is still independent
  have hindep' : iIndepFun (fun j : Fin m => -N j) μ :=
    h_indep.comp _ (fun _ => measurable_id.neg)
  -- each -N_j is sub-Gaussian (Hoeffding's lemma), parameter (2R/2)² = R²
  have hc : ∀ j, HasSubgaussianMGF (-N j) ((‖R - (-R)‖₊ / 2) ^ 2) μ := by
    intro j
    have hmem : ∀ᵐ ω ∂μ, (-N j) ω ∈ Set.Icc (-R) R := by
      filter_upwards with ω
      have hb := abs_le.mp (h_bound j ω)
      simp only [Pi.neg_apply, Set.mem_Icc]
      constructor <;> linarith
    have hzero' : μ[-N j] = 0 := by
      change ∫ (x : Ω), -(N j x) ∂μ = 0
      rw [integral_neg, h_zero j]
      ring
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (a := -R) (b := R) (X := -N j)
      (hm := (h_meas j).neg.aemeasurable) (hb := hmem) (hc := hzero')
  -- the parameter simplifies to R^2
  have habs : |2 * R| = 2 * R := abs_of_nonneg (by linarith [hR])
  have h2 : ((‖R - (-R)‖₊ : ℝ)) = 2 * R := by
    have hrw : (R : ℝ) - (-R) = 2 * R := by ring
    rw [hrw]
    push_cast
    simp [hR.le]
  have hRabs : (((‖R - (-R)‖₊ : ℝ)) / 2) ^ 2 = R ^ 2 := by
    rw [h2]
    field_simp
  -- the Hoeffding inequality over the m independent terms, at level m·ε
  have hεm : 0 ≤ (m : ℝ) * ε := by positivity
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (ι := Fin m)
    (X := fun j => -N j) (c := fun _ => ((‖R - (-R)‖₊ / 2) ^ 2))
    hindep' (s := Finset.univ) (fun j _ => hc j) (ε := (m : ℝ) * ε) hεm
  -- per-term parameter cast: each c_j = R² (as a real)
  have hpt : ∀ j : Fin m, (((‖R - (-R)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = R ^ 2 := by
    intro j
    push_cast
    exact hRabs
  rw [NNReal.coe_sum, Finset.sum_congr rfl (fun j _ => hpt j),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin] at htail
  simp at htail
  -- exponent arithmetic: (m·ε)² / (2·(m·R²)) = m·ε²/(2·R²)
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htail' : μ.real {ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
      ≤ Real.exp (- ((m : ℝ) * ε) ^ 2 / (2 * ((m : ℝ) * R ^ 2))) := by
    have hset : {ω : Ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
        = {ω : Ω | (m : ℝ) * ε ≤ -∑ j, N j ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> simpa using h
    rw [hset]
    exact htail
  calc μ.real {ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
      ≤ Real.exp (- ((m : ℝ) * ε) ^ 2 / (2 * ((m : ℝ) * R ^ 2))) := htail'
    _ = Real.exp (- (m : ℝ) * ε ^ 2 / (2 * R ^ 2)) := by
        congr 1
        field_simp


/-- C365 общий ингредиент концентрационных доказательств: проекция
шума на направление ограничена `σ·‖d‖` (Коши–Шварц). Ранее
байт-в-байт дублировался в `minibatch_inner_concentration` и
`minibatch_inner_concentration_upper`. -/
theorem noise_proj_abs_le {m : ℕ} (d : X) (sigma : ℝ)
    (xi : K → Fin m → Ω → X)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (hsigma : 0 < sigma) (i j ω) :
    |⟪xi i j ω, d⟫_ℝ| ≤ sigma * ‖d‖ := by
  calc |⟪xi i j ω, d⟫_ℝ| = ‖⟪xi i j ω, d⟫_ℝ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖xi i j ω‖ * ‖d‖ := norm_inner_le_norm _ _
    _ ≤ sigma * ‖d‖ :=
        mul_le_mul_of_nonneg_right (h_emp_noise_bound i j ω) (norm_nonneg d)

/-- C365 общий ингредиент: тождество показателя хвоста
`m·noiseEps² = 2·(σ‖d‖)²·log(|K|/δ)`. Ранее дублировался
байт-в-байт в обоих концентрационных доказательствах. -/
theorem noiseEps_sq_identity {m : ℕ} [Nonempty K] (hm : 0 < m)
    (d : X) (hd : d ≠ 0) (sigma : ℝ) (hsigma : 0 < sigma)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) :
    m * (noiseEps K sigma d m delta) ^ 2
      = 2 * (sigma * ‖d‖) ^ 2 * Real.log ((Fintype.card K : ℝ) / delta) := by
  have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hd1, hd2⟩ := Set.mem_Ioo.mp hdelta
  have hcard : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hLpos : 0 < Real.log ((Fintype.card K : ℝ) / delta) := by
    have h1 : 1 < (Fintype.card K : ℝ) / delta :=
      (one_lt_div hd1).mpr (lt_of_lt_of_le hd2 hcard)
    exact Real.log_pos h1
  have hs2 : 0 ≤ 2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ) := by
    apply div_nonneg _ hmp.le
    linarith
  unfold noiseEps
  have hsqr : (Real.sqrt (2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ))) ^ 2
      = 2 * Real.log ((Fintype.card K : ℝ) / delta) / (m : ℝ) :=
    Real.sq_sqrt hs2
  rw [mul_pow, hsqr]
  field_simp

/-- При `d ≠ 0`, `0 < σ`, статистических посылках на
проекции шума (измеримость, среднее нулевое, поштучная
независимость, `‖ξ‖ ≤ σ`) и `δ ∈ (0,1)`:
с вероятностью ≥ 1 − δ для всех i
`⟪g i, d⟫ − noiseEps ≤ ⟪g i + (1/m)·Σⱼ ξ_{i,j}, d⟫`
(нижний хвост; |K| — через union bound). -/
theorem minibatch_inner_concentration {m : ℕ} (hm : 0 < m)
    (g : K → X) (d : X) (hd : d ≠ 0) (sigma : ℝ) (hsigma : 0 < sigma)
    (xi : K → Fin m → Ω → X)
    (h_emp_noise_meas : ∀ i j, Measurable (fun ω => ⟪xi i j ω, d⟫_ℝ))
    (h_emp_noise_zero : ∀ i j, μ[fun ω => ⟪xi i j ω, d⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i, iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, d⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) :
    μ.real {ω | ∀ i, ⟪g i, d⟫_ℝ - noiseEps K sigma d m delta
        ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ} ≥ 1 - delta := by
  classical
  set R := sigma * ‖d‖ with hRdef
  have hR : 0 < R := by
    rw [hRdef]
    exact mul_pos hsigma (norm_pos_iff.mpr hd)
  -- the noise projections are bounded by R = σ‖d‖ (Cauchy-Schwarz)
  have hB : ∀ i j ω, |⟪xi i j ω, d⟫_ℝ| ≤ R := by
    intro i j ω
    rw [hRdef]
    exact noise_proj_abs_le d sigma xi h_emp_noise_bound hsigma i j ω
  -- ε_noise ≥ 0 (the log is nonnegative: |K| ≥ 1 > δ)
  have hcard : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨hd1, hd2⟩ := Set.mem_Ioo.mp hdelta
  have hLpos : 0 < Real.log ((Fintype.card K : ℝ) / delta) := by
    have h1 : 1 < (Fintype.card K : ℝ) / delta :=
      (one_lt_div hd1).mpr (lt_of_lt_of_le hd2 hcard)
    exact Real.log_pos h1
  have heps : 0 ≤ noiseEps K sigma d m delta := by
    unfold noiseEps
    positivity
  -- the exponent identity: m·ε_noise² / (2R²) = log(|K|/δ)
  have hsq : m * (noiseEps K sigma d m delta) ^ 2
      = 2 * R ^ 2 * Real.log ((Fintype.card K : ℝ) / delta) := by
    rw [hRdef]
    exact noiseEps_sq_identity hm d hd sigma hsigma delta hdelta
  -- the per-domain tail equals exactly δ/|K|
  have htailval : ∀ i : K,
      μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
        ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)}
      ≤ delta / (Fintype.card K : ℝ) := by
    intro i
    have ht := minibatch_inner_tail hm
      (fun j ω => ⟪xi i j ω, d⟫_ℝ) R hR
      (h_emp_noise_meas i) (h_emp_noise_indep i) (h_emp_noise_zero i) (hB i) heps
    have hex : Real.exp (- (m : ℝ) * (noiseEps K sigma d m delta) ^ 2 / (2 * R ^ 2))
        = delta / (Fintype.card K : ℝ) := by
      have hrw : - (m : ℝ) * (noiseEps K sigma d m delta) ^ 2 / (2 * R ^ 2)
          = - Real.log ((Fintype.card K : ℝ) / delta) := by
        rw [neg_mul, hsq]
        field_simp
      have hcd : 0 < (Fintype.card K : ℝ) / delta :=
        div_pos (by exact_mod_cast Fintype.card_pos) hd1
      rw [hrw, Real.exp_neg, Real.exp_log hcd, inv_div]
    rw [hex] at ht
    exact ht
  -- the union bound over the K protected domains
  have hcardne : (Fintype.card K : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  have hsum : ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)} ≤ delta := by
    calc ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
          ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)}
        ≤ ∑ i, delta / (Fintype.card K : ℝ) :=
          Finset.sum_le_sum (fun i _ => htailval i)
      _ = delta := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
          field_simp
  have huni : μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)}) ≤ delta := by
    calc μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
          ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})
        ≤ ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
            ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)} :=
          measureReal_iUnion_fintype_le
            (fun i => {ω | (m : ℝ) * noiseEps K sigma d m delta
              ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})
      _ ≤ delta := hsum
  -- the failure events are measurable
  have hE : ∀ i : K, MeasurableSet {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)} := by
    intro i
    have hf : Measurable (fun ω => ∑ j, -(⟪xi i j ω, d⟫_ℝ)) := by fun_prop
    exact measurableSet_le measurable_const hf
  have huniMeas : MeasurableSet (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)}) :=
    MeasurableSet.iUnion hE
  have hcomp : 1 - delta ≤ μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})ᶜ := by
    rw [measureReal_compl huniMeas, probReal_univ]
    linarith
  -- the good event contains the complement of the failure event
  have hinner : ∀ (i : K) (ω : Ω),
      ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        = ⟪g i, d⟫_ℝ + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, d⟫_ℝ := by
    intro i ω
    rw [inner_add_left, inner_smul_left, sum_inner]
    simp
  have hsub : (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})ᶜ
      ⊆ {ω | ∀ i, ⟪g i, d⟫_ℝ - noiseEps K sigma d m delta
        ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hω
    intro i
    rw [hinner i]
    by_contra hcontra
    push Not at hcontra
    have hnot := hω i
    simp only [Set.mem_ofPred_eq] at hnot
    push Not at hnot
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hneg : ∑ j, -(⟪xi i j ω, d⟫_ℝ) = -∑ j, ⟪xi i j ω, d⟫_ℝ := by
      simp [Finset.sum_neg_distrib]
    have h1 : -((m : ℝ) * noiseEps K sigma d m delta)
        < ∑ j, ⟪xi i j ω, d⟫_ℝ := by linarith
    have h2 : -(noiseEps K sigma d m delta)
        < (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, d⟫_ℝ := by
      rw [inv_mul_eq_div, lt_div_iff₀ hmp]
      linarith
    linarith
  calc (1 : ℝ) - delta ≤ μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
        ≤ ∑ j, -(⟪xi i j ω, d⟫_ℝ)})ᶜ := hcomp
    _ ≤ μ.real {ω | ∀ i, ⟪g i, d⟫_ℝ - noiseEps K sigma d m delta
        ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ} := measureReal_mono hsub

theorem minibatch_inner_concentration_upper {m : ℕ} (hm : 0 < m)
    (g : K → X) (d : X) (hd : d ≠ 0) (sigma : ℝ) (hsigma : 0 < sigma)
    (xi : K → Fin m → Ω → X)
    (h_emp_noise_meas : ∀ i j, Measurable (fun ω => ⟪xi i j ω, d⟫_ℝ))
    (h_emp_noise_zero : ∀ i j, μ[fun ω => ⟪xi i j ω, d⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i, iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, d⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) :
    μ.real {ω | ∀ i, ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        ≤ ⟪g i, d⟫_ℝ + noiseEps K sigma d m delta} ≥ 1 - delta := by
  classical
  set R := sigma * ‖d‖ with hRdef
  have hR : 0 < R := by
    rw [hRdef]
    exact mul_pos hsigma (norm_pos_iff.mpr hd)
  -- the noise projections are bounded by R = σ‖d‖ (Cauchy-Schwarz)
  have hB : ∀ i j ω, |⟪xi i j ω, d⟫_ℝ| ≤ R := by
    intro i j ω
    rw [hRdef]
    exact noise_proj_abs_le d sigma xi h_emp_noise_bound hsigma i j ω
  -- ε_noise ≥ 0 (the log is nonnegative: |K| ≥ 1 > δ)
  have hcard : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨hd1, hd2⟩ := Set.mem_Ioo.mp hdelta
  have hLpos : 0 < Real.log ((Fintype.card K : ℝ) / delta) := by
    have h1 : 1 < (Fintype.card K : ℝ) / delta :=
      (one_lt_div hd1).mpr (lt_of_lt_of_le hd2 hcard)
    exact Real.log_pos h1
  have heps : 0 ≤ noiseEps K sigma d m delta := by
    unfold noiseEps
    positivity
  -- the exponent identity: m·ε_noise² / (2R²) = log(|K|/δ)
  have hsq : m * (noiseEps K sigma d m delta) ^ 2
      = 2 * R ^ 2 * Real.log ((Fintype.card K : ℝ) / delta) := by
    rw [hRdef]
    exact noiseEps_sq_identity hm d hd sigma hsigma delta hdelta
  -- the per-domain tail equals exactly δ/|K|
  have htailval : ∀ i : K,
      μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
        ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ}
      ≤ delta / (Fintype.card K : ℝ) := by
    intro i
    have ht := minibatch_inner_tail hm
      (fun j ω => -(⟪xi i j ω, d⟫_ℝ)) R hR
      (fun j => (h_emp_noise_meas i j).neg)
      ((h_emp_noise_indep i).comp _ (fun _ => measurable_id.neg))
      (fun j => by
        show ∫ (x : Ω), -(⟪xi i j x, d⟫_ℝ) ∂μ = 0
        rw [integral_neg, h_emp_noise_zero i j]
        ring)
      (fun j ω => by simpa using hB i j ω) heps
    simp only [neg_neg] at ht
    have hex : Real.exp (- (m : ℝ) * (noiseEps K sigma d m delta) ^ 2 / (2 * R ^ 2))
        = delta / (Fintype.card K : ℝ) := by
      have hrw : - (m : ℝ) * (noiseEps K sigma d m delta) ^ 2 / (2 * R ^ 2)
          = - Real.log ((Fintype.card K : ℝ) / delta) := by
        rw [neg_mul, hsq]
        field_simp
      have hcd : 0 < (Fintype.card K : ℝ) / delta :=
        div_pos (by exact_mod_cast Fintype.card_pos) hd1
      rw [hrw, Real.exp_neg, Real.exp_log hcd, inv_div]
    rw [hex] at ht
    exact ht
  -- the union bound over the K protected domains
  have hcardne : (Fintype.card K : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  have hsum : ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ} ≤ delta := by
    calc ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
          ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ}
        ≤ ∑ i, delta / (Fintype.card K : ℝ) :=
          Finset.sum_le_sum (fun i _ => htailval i)
      _ = delta := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
          field_simp
  have huni : μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ}) ≤ delta := by
    calc μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
          ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})
        ≤ ∑ i, μ.real {ω | (m : ℝ) * noiseEps K sigma d m delta
            ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ} :=
          measureReal_iUnion_fintype_le
            (fun i => {ω | (m : ℝ) * noiseEps K sigma d m delta
              ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})
      _ ≤ delta := hsum
  -- the failure events are measurable
  have hE : ∀ i : K, MeasurableSet {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ} := by
    intro i
    have hf : Measurable (fun ω => ∑ j, ⟪xi i j ω, d⟫_ℝ) := by fun_prop
    exact measurableSet_le measurable_const hf
  have huniMeas : MeasurableSet (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ}) :=
    MeasurableSet.iUnion hE
  have hcomp : 1 - delta ≤ μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})ᶜ := by
    rw [measureReal_compl huniMeas, probReal_univ]
    linarith
  -- the good event contains the complement of the failure event
  have hinner : ∀ (i : K) (ω : Ω),
      ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        = ⟪g i, d⟫_ℝ + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, d⟫_ℝ := by
    intro i ω
    rw [inner_add_left, inner_smul_left, sum_inner]
    simp
  have hsub : (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
      ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})ᶜ
      ⊆ {ω | ∀ i, ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        ≤ ⟪g i, d⟫_ℝ + noiseEps K sigma d m delta} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hω
    intro i
    rw [hinner i]
    by_contra hcontra
    push Not at hcontra
    have hnot := hω i
    simp only [Set.mem_ofPred_eq] at hnot
    push Not at hnot
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have h1 : ∑ j, ⟪xi i j ω, d⟫_ℝ
        < (m : ℝ) * noiseEps K sigma d m delta := by linarith
    have h2 : (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, d⟫_ℝ
        < noiseEps K sigma d m delta := by
      rw [inv_mul_eq_div, div_lt_iff₀ hmp]
      linarith
    linarith
  calc (1 : ℝ) - delta ≤ μ.real (⋃ i : K, {ω | (m : ℝ) * noiseEps K sigma d m delta
        ≤ ∑ j, ⟪xi i j ω, d⟫_ℝ})ᶜ := hcomp
    _ ≤ μ.real {ω | ∀ i, ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ
        ≤ ⟪g i, d⟫_ℝ + noiseEps K sigma d m delta} := measureReal_mono hsub

/-- При тех же посылках и бюджетах `eps`: с вероятностью
≥ 1 − δ, если `−eps i ≤ ⟪g i + (1/m)·Σⱼ ξ_{i,j}, d⟫` для
всех i, то
`−(eps i + noiseEps) ≤ ⟪g i, d⟫` для всех i`. -/
theorem stochastic_safeQP_feasibility {m : ℕ} (hm : 0 < m)
    (g : K → X) (d : X) (hd : d ≠ 0) (sigma : ℝ) (hsigma : 0 < sigma)
    (xi : K → Fin m → Ω → X)
    (h_emp_noise_meas : ∀ i j, Measurable (fun ω => ⟪xi i j ω, d⟫_ℝ))
    (h_emp_noise_zero : ∀ i j, μ[fun ω => ⟪xi i j ω, d⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i, iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, d⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) (eps : K → ℝ) :
    μ.real {ω | (∀ i, -eps i ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, d⟫_ℝ)
        → (∀ i, -(eps i + noiseEps K sigma d m delta) ≤ ⟪g i, d⟫_ℝ)} ≥ 1 - delta := by
  have hgood := minibatch_inner_concentration_upper hm g d hd sigma hsigma xi
    h_emp_noise_meas h_emp_noise_zero h_emp_noise_indep h_emp_noise_bound delta hdelta
  refine le_trans hgood (measureReal_mono ?_)
  rintro ω hω hcert i
  have h1 := hω i
  have h2 := hcert i
  linarith

/--
Вспомогательный закон извлечения квадрата из-под корня:
для вещественного `x` (в т.ч. отрицательного, где
`Real.sqrt = 0`) и `k > 0` выполнено `√(x/k²) = √x / k`.
-/
private theorem sqrt_div_sq (x k : ℝ) (hk : 0 < k) :
    Real.sqrt (x / k ^ 2) = Real.sqrt x / k := by
  have hk2 : (0:ℝ) < k ^ 2 := by positivity
  by_cases hx : x ≤ 0
  · have h1 : x / k ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hx hk2.le
    rw [Real.sqrt_eq_zero_of_nonpos h1,
      Real.sqrt_eq_zero_of_nonpos hx]
    simp
  · rw [Real.sqrt_div (by nlinarith : (0:ℝ) ≤ x) (k ^ 2),
      Real.sqrt_sq (le_of_lt hk)]

/--
`lr_batch_equivalence` — формальное ядро закона «не снижай
LR, увеличивай batch» (Smith et al., arXiv:1711.00489):
шумовой бюджет шага `η · noiseEps` инвариантен относительно
преобразования (η, m) → (k·η, k²·m): увеличение learning
rate в k раз при увеличении batch в k² раз сохраняет
шумовую границу шага (и, значит, все сертифицированные
гарантии `stochastic_safeQP_feasibility` на том же уровне
δ). Следствие: расписание LR можно заменить масштабированием
batch — тот же уровень шума (и те же сертификаты) при
большем параллелизме: на ту же кривую обучения нужно в k раз
меньше последовательных обновлений.

Инвариант — это в точности постоянство дисперсии шума на
обновление η²σ²/m (шумовая шкала SGD).

## References

[1] Smith, Kindermans, Ying, Le. Don't Decay the Learning
Rate, Increase the Batch Size. arXiv:1711.00489 (2017).
-/
theorem lr_batch_equivalence {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (eta sigma delta : ℝ) (d : X) :
    (k : ℝ) * eta * noiseEps K sigma d (k ^ 2 * m) delta
      = eta * noiseEps K sigma d m delta := by
  have hk' : (0:ℝ) < k := by positivity
  have hcast : ((k ^ 2 * m : ℕ) : ℝ) = (k:ℝ) ^ 2 * m := by
    push_cast
    ring
  simp only [noiseEps, hcast]
  have hfrac : (2 * Real.log ((Fintype.card K : ℝ) / delta) / ((k:ℝ) ^ 2 * m))
      = (2 * Real.log ((Fintype.card K : ℝ) / delta) / m) / (k:ℝ) ^ 2 := by
    field_simp
  rw [hfrac]
  rw [sqrt_div_sq
    (2 * Real.log ((Fintype.card K : ℝ) / delta) / m) (k:ℝ) hk']
  field_simp

/-! ### C287: мост к единому concentration API -/

/-- C287: единичный шумовой радиус R = 1/2 — частный случай
`minibatch_inner_tail`, инстанцирующий единый
`Hagi.Probability.concConfidence ε m` API: экспонента
`−m·ε²/(2·(1/2)²) = −2mε²` совпадает с канонической. -/
theorem minibatch_inner_tail_via_conc {m : ℕ} (hm : 0 < m)
    (N : Fin m → Ω → ℝ)
    (h_meas : ∀ j, Measurable (N j))
    (h_indep : iIndepFun N μ)
    (h_zero : ∀ j, μ[N j] = 0)
    (h_bound : ∀ j ω, |N j ω| ≤ 1/2)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | (m : ℝ) * ε ≤ ∑ j, -N j ω}
      ≤ Hagi.Probability.concConfidence ε m := by
  have h := minibatch_inner_tail hm N (1/2) (by norm_num) h_meas h_indep
    h_zero h_bound hε
  have hid : Real.exp (- (m : ℝ) * ε ^ 2 / (2 * ((1/2:ℝ)) ^ 2))
      = Hagi.Probability.concConfidence ε m := by
    simp only [Hagi.Probability.concConfidence]
    congr 1
    field_simp
  exact h.trans (le_of_eq hid)

end StochasticSafeQP

end Hagi.Step

namespace Hagi
export Hagi.Step (noiseEps minibatch_inner_tail stochastic_safeQP_feasibility)
end Hagi

set_option linter.style.header false

/-!
# AdaptiveSafeQP — концентрация для адаптивно выбранного направления d*(ω)

Концентрация минибатч-градиента (`StochasticSafeQP` — только
фиксированное направление d) обобщается на ω-зависимое
направление d*(ω) через явную решётчатую ε-сеть.

1. `latticeNet n D epsDir M` — конечная ε_dir-сеть шара
   `{‖x‖ ≤ D}` в `EuclideanSpace ℝ (Fin n)`: точки решётки с
   шагом `h = epsDir/√n`, нормы ≤ D + epsDir; покрывает шар
   (`latticeNet_covers`), размер ≤ `(2M+1)^n`
   (`latticeNet_card_le`) при `M ≥ D·√n/epsDir + 1`;
2. `adaptive_net_concentration` — равномерная по сети и всем
   доменам i концентрация с вероятностью ≥ 1−δ при пороге
   `ε_net = σ(D+epsDir)√(2 log(2|K|N_net/δ)/m)`;
3. `adaptive_direction_concentration` — перенос на любое
   `d* : Ω → X` с `‖d*ω‖ ≤ D` (без измеримости d*):
   `|(1/m)Σⱼ ⟪ξ_{i,j}, d*⟫| ≤ ε_net + σ·epsDir`;
4. `adaptive_safeQP_feasibility` — если стохастический QP
   сертифицировал d*(ω) по минибатч-градиентам с бюджетами
   `eps i`, то истинные градиенты удовлетворяют
   `⟪g i, d*⟫ ≥ −(eps i + ε_net + σ·epsDir)`.

Ограничения: конечномерность; статистические посылки требуются
на всём шаре `‖v‖ ≤ D + epsDir`; выбор оптимального epsDir и
бесконечномерный режим — открыто.
-/

open Finset Real MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal

namespace Hagi.Step

section AdaptiveSafeQP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {K : Type*} [Fintype K] [Nonempty K]

/-! ### The explicit lattice ε-net -/

/-- Шаг решётки `h = epsDir/√n` — разрешение сети по каждой
из n координат. -/
noncomputable def latticeStep (n : ℕ) (epsDir : ℝ) : ℝ := epsDir / Real.sqrt n

open Classical in
/-- Явная целочисленно-решётчатая ε_dir-сеть шара `{‖x‖ ≤ D}` в
`EuclideanSpace ℝ (Fin n)`: точки `h • z` с шагом
`h = epsDir/√n`, отфильтрованные условием
`∑ (h·z_k)² ≤ (D + epsDir)²`. -/
noncomputable def latticeNet (n : ℕ) (D epsDir : ℝ) (M : ℕ) :
    Finset (EuclideanSpace ℝ (Fin n)) :=
  ((Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : ℤ)) M).filter
      fun z => ∑ k, (latticeStep n epsDir * (z k : ℝ)) ^ 2 ≤ (D + epsDir) ^ 2).image
    fun z => WithLp.toLp 2 fun k => latticeStep n epsDir * (z k : ℝ)

/-- Точки сети лежат в шаре радиуса `D + epsDir`
(при `0 ≤ D + epsDir`). -/
theorem latticeNet_norm_le {n : ℕ} {D epsDir : ℝ} (hDE : 0 ≤ D + epsDir) {M : ℕ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ latticeNet n D epsDir M) :
    ‖v‖ ≤ D + epsDir := by
  classical
  simp only [latticeNet] at hv
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hpi, hsum⟩ := Finset.mem_filter.mp hz
  have hvk : ∀ k, (WithLp.toLp 2 (fun k => latticeStep n epsDir * (z k : ℝ)) :
      EuclideanSpace ℝ (Fin n)) k = latticeStep n epsDir * (z k : ℝ) := fun k => rfl
  have hs : ∑ k, (latticeStep n epsDir * (z k : ℝ)) ^ 2
      = ‖(WithLp.toLp 2 (fun k => latticeStep n epsDir * (z k : ℝ)) :
          EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [hs] at hsum
  have habs := abs_le_of_sq_le_sq hsum hDE
  rwa [abs_of_nonneg (norm_nonneg _)] at habs

/-- Покрытие: при `0 < n`, `0 ≤ D`, `0 < epsDir` и
`M ≥ D·√n/epsDir + 1` каждая точка x шара `‖x‖ ≤ D` лежит
в epsDir-окрестности некоторой точки сети (покоординатное
округление вниз). -/
theorem latticeNet_covers {n : ℕ} (hn : 0 < n) {D epsDir : ℝ} (hD : 0 ≤ D)
    (hepsDir : 0 < epsDir) {M : ℕ} (hM : D * Real.sqrt n / epsDir + 1 ≤ (M : ℝ))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ D) :
    ∃ v ∈ latticeNet n D epsDir M, ‖x - v‖ ≤ epsDir := by
  classical
  have hdef : latticeStep n epsDir = epsDir / Real.sqrt n := rfl
  have hnneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
  have hnne : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn.ne'
  have hnpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hh : 0 < epsDir / Real.sqrt n := div_pos hepsDir hnpos
  have hsqn : (epsDir / Real.sqrt n) ^ 2 * (n : ℝ) = epsDir ^ 2 := by
    rw [div_pow, Real.sq_sqrt hnneg, div_mul_cancel₀ (epsDir ^ 2) hnne]
  -- coordinate bound: |x k| ≤ ‖x‖ ≤ D (Euclidean norm dominates coordinates)
  have hxk : ∀ k, |x k| ≤ D := by
    intro k
    have h1 : (x k) ^ 2 ≤ ∑ i, (x i) ^ 2 :=
      Finset.single_le_sum (f := fun i => (x i) ^ 2) (fun i _ => sq_nonneg _) (mem_univ k)
    rw [← EuclideanSpace.real_norm_sq_eq] at h1
    exact le_trans (abs_le_of_sq_le_sq h1 (norm_nonneg x)) hx
  -- the rounded lattice vector
  set z : Fin n → ℤ := fun k => Int.floor (x k / (epsDir / Real.sqrt n)) with hzdef
  set v : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 fun k => (epsDir / Real.sqrt n) * (z k : ℝ) with hvdef
  have hvk : ∀ k, v k = (epsDir / Real.sqrt n) * (z k : ℝ) := fun k => rfl
  -- per-coordinate rounding error in [0, h]
  have hround : ∀ k, 0 ≤ x k - (epsDir / Real.sqrt n) * (z k : ℝ)
      ∧ x k - (epsDir / Real.sqrt n) * (z k : ℝ) ≤ epsDir / Real.sqrt n := by
    intro k
    have hfl : ((z k : ℤ) : ℝ) ≤ x k / (epsDir / Real.sqrt n) := Int.floor_le _
    have hfs : x k / (epsDir / Real.sqrt n) < ((z k : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hlow : (epsDir / Real.sqrt n) * ((z k : ℤ) : ℝ) ≤ x k := by
      have h1 := mul_le_mul_of_nonneg_right hfl hh.le
      rwa [mul_comm, div_mul_cancel₀ (x k) hh.ne'] at h1
    have hhigh : x k < (epsDir / Real.sqrt n) * ((z k : ℤ) : ℝ)
        + epsDir / Real.sqrt n := by
      have h2 := mul_lt_mul_of_pos_right hfs hh
      rw [div_mul_cancel₀ (x k) hh.ne'] at h2
      ring_nf at h2 ⊢
      linarith
    constructor <;> linarith
  -- ‖x - v‖ ≤ epsDir
  have hdist : ‖x - v‖ ≤ epsDir := by
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        (x k - v k) ^ 2 ≤ (epsDir / Real.sqrt n) ^ 2 := by
      intro k _
      have ⟨h0, h1⟩ := hround k
      rw [hvk k]
      nlinarith [hh.le]
    have hsumle : ∑ k, (x k - v k) ^ 2 ≤ epsDir ^ 2 := by
      calc ∑ k, (x k - v k) ^ 2 ≤ ∑ k, (epsDir / Real.sqrt n) ^ 2 :=
            Finset.sum_le_sum hterm
        _ = Finset.card (Finset.univ : Finset (Fin n)) * (epsDir / Real.sqrt n) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (n : ℝ) * (epsDir / Real.sqrt n) ^ 2 := by simp
        _ = epsDir ^ 2 := by rw [mul_comm]; exact hsqn
    have hsq : (‖x - v‖) ^ 2 ≤ epsDir ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact hsumle
    have habs := abs_le_of_sq_le_sq hsq hepsDir.le
    rwa [abs_of_nonneg (norm_nonneg _)] at habs
  -- ‖v‖ ≤ D + epsDir (triangle inequality)
  have hvnorm : ‖v‖ ≤ D + epsDir := by
    have hvx : ‖v‖ = ‖x - (x - v)‖ := by
      have : x - (x - v) = v := by abel
      rw [this]
    rw [hvx]
    have ht := norm_sub_le x (x - v)
    linarith [hx, hdist, ht]
  refine ⟨v, ?_, hdist⟩
  rw [latticeNet]
  refine Finset.mem_image.mpr ⟨z, ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · -- z in the integer box
    have hDh : D / (epsDir / Real.sqrt n) = D * Real.sqrt n / epsDir := by
      rw [div_eq_inv_mul, inv_div, mul_div_assoc, mul_comm]
    refine Fintype.mem_piFinset.mpr fun k => Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · -- -(M:ℤ) ≤ z k
      have hfu : x k / (epsDir / Real.sqrt n) - 1 < ((z k : ℤ) : ℝ) :=
        Int.sub_one_lt_floor _
      have hkabs : -(|x k| / (epsDir / Real.sqrt n)) ≤ x k / (epsDir / Real.sqrt n) := by
        rw [← neg_div]
        exact div_le_div_of_nonneg_right (neg_abs_le _) hh.le
      have hkD : |x k| / (epsDir / Real.sqrt n) ≤ D * Real.sqrt n / epsDir := by
        rw [← hDh]
        exact div_le_div_of_nonneg_right (hxk k) hh.le
      have hz : (-(M : ℤ) : ℝ) ≤ ((z k : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hz
    · -- z k ≤ M
      have hfl : ((z k : ℤ) : ℝ) ≤ x k / (epsDir / Real.sqrt n) :=
        Int.floor_le _
      have hkabs : x k / (epsDir / Real.sqrt n) ≤ |x k| / (epsDir / Real.sqrt n) :=
        div_le_div_of_nonneg_right (le_abs_self _) hh.le
      have hkD : |x k| / (epsDir / Real.sqrt n) ≤ D * Real.sqrt n / epsDir := by
        rw [← hDh]
        exact div_le_div_of_nonneg_right (hxk k) hh.le
      have hz : ((z k : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hz
  · -- filter predicate: ∑ (h·z_k)² ≤ (D + epsDir)²
    have hvv : ∀ k, (epsDir / Real.sqrt n) * (z k : ℝ) = v k := fun k => (hvk k).symm
    have hcalc : ∑ k, ((epsDir / Real.sqrt n) * (z k : ℝ)) ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    change ∑ k, ((epsDir / Real.sqrt n) * (z k : ℝ)) ^ 2 ≤ (D + epsDir) ^ 2
    rw [hcalc]
    exact sq_le_sq' (by linarith [norm_nonneg v]) hvnorm

/-- `(latticeNet n D epsDir M).card ≤ (2 * M + 1) ^ n`. -/
theorem latticeNet_card_le (n : ℕ) (D epsDir : ℝ) (M : ℕ) :
    (latticeNet n D epsDir M).card ≤ (2 * M + 1) ^ n := by
  classical
  have hbox : (Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : ℤ)) M).card
      = (2 * M + 1) ^ n := by
    rw [Fintype.piFinset, Finset.card_map, Finset.card_pi]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
    have hnat0 : (((M : ℤ) + 1 - (-(M : ℤ))).toNat : ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]
      push_cast
      omega
    have hnat : ((M : ℤ) + 1 - (-(M : ℤ))).toNat = 2 * M + 1 := by
      exact_mod_cast hnat0
    rw [hnat]
  calc (latticeNet n D epsDir M).card
      ≤ ((Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : ℤ)) M).filter
          fun z => ∑ k, (latticeStep n epsDir * (z k : ℝ)) ^ 2 ≤ (D + epsDir) ^ 2).card := by
        change Finset.card (Finset.image _ _) ≤ _
        exact Finset.card_image_le
    _ ≤ (Fintype.piFinset fun _ : Fin n => Finset.Icc (-(M : ℤ)) M).card := by
        show Finset.card (Finset.filter _ _) ≤ _
        exact Finset.card_filter_le _ _
    _ = (2 * M + 1) ^ n := hbox

/-! ### Uniform concentration over the net -/

/-- Явный сетевой шумовой порог
`ε_net = σ(D+epsDir)√(2·log(2|K|·(2M+1)^n/δ)/m)`. -/
noncomputable def adaptiveNoiseEps (K : Type*) [Fintype K] (n : ℕ) (D epsDir : ℝ) (M : ℕ)
    (sigma : ℝ) (m : ℕ) (delta : ℝ) : ℝ :=
  sigma * (D + epsDir) *
    Real.sqrt (2 * Real.log (2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ n : ℝ) / delta) / (m : ℝ))

/-- Равномерная по сети концентрация: при статистических
посылках на шаре `‖v‖ ≤ D + epsDir` (измеримость,
средние нулевые, независимость, `‖ξ‖ ≤ σ`) с вероятностью
`≥ 1 − δ` одновременно для всех i и всех точек сети v
выполнено `|(1/m)Σⱼ ⟪ξ_{i,j}, v⟫| ≤ adaptiveNoiseEps`.
Доказательство: пер-точечный Hoeffding (`minibatch_inner_tail`)
+ двусторонний union bound по |K| × |net| ≤ (2M+1)^n. -/
theorem adaptive_net_concentration {m : ℕ} (hm : 0 < m) {n : ℕ}
    (sigma : ℝ) (hsigma : 0 < sigma) (D : ℝ) (hD : 0 ≤ D) (epsDir : ℝ) (hepsDir : 0 < epsDir)
    {M : ℕ}
    (xi : K → Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (h_emp_noise_meas : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      Measurable fun ω => ⟪xi i j ω, v⟫_ℝ)
    (h_emp_noise_zero : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      μ[fun ω => ⟪xi i j ω, v⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, v⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) :
    μ.real {ω | ∀ i, ∀ v ∈ latticeNet n D epsDir M,
      |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|
        ≤ adaptiveNoiseEps K n D epsDir M sigma m delta} ≥ 1 - delta := by
  classical
  obtain ⟨hd1, hd2⟩ := Set.mem_Ioo.mp hdelta
  set N := ((2 * M + 1) ^ n : ℝ) with hN
  set L := 2 * Real.log (2 * (Fintype.card K : ℝ) * N / delta) with hL
  set A := adaptiveNoiseEps K n D epsDir M sigma m delta with hA
  set Rmax := sigma * (D + epsDir) with hRmax
  have hcardK : (1 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcardKne : (Fintype.card K : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
    linarith
  have hNpos : (1 : ℝ) ≤ N := by
    have h2 : (1 : ℕ) ≤ (2 * M + 1) ^ n := Nat.one_le_pow n (2 * M + 1) (by omega)
    have h3 : (1 : ℝ) ≤ ((2 * M + 1) ^ n : ℝ) := by exact_mod_cast h2
    exact h3
  have hNne : N ≠ 0 := by
    have : (0 : ℝ) < N := by linarith
    linarith
  have hDE : 0 ≤ D + epsDir := by linarith
  -- the log argument exceeds 1, so the log is positive and A ≥ 0
  have harg : (1 : ℝ) < 2 * (Fintype.card K : ℝ) * N / delta := by
    rw [lt_div_iff₀ hd1]
    nlinarith [hcardK, hNpos]
  have hLpos : 0 < L := by
    have := Real.log_pos harg
    linarith
  have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (mul_nonneg hsigma.le hDE) (Real.sqrt_nonneg _)
  -- the definition unfolds to σ(D+eps)·√(L/m)
  have hAdef : A = Rmax * Real.sqrt (L / (m : ℝ)) := rfl
  -- the exponent identity: m·A² = Rmax²·L
  have hsq : (m : ℝ) * A ^ 2 = Rmax ^ 2 * L := by
    rw [hAdef, hRmax, mul_pow, Real.sq_sqrt (div_nonneg hLpos.le hmp.le)]
    field_simp
  -- the exp identity: exp(−m·A²/(2·Rmax²)) = δ/(2|K|N)
  have hRne : Rmax ≠ 0 := by
    rw [hRmax]
    positivity
  have hLdef : L = 2 * Real.log (2 * (Fintype.card K : ℝ) * N / delta) := rfl
  have h2ne : (2 * Rmax ^ 2) ≠ 0 := by positivity
  have hexp : Real.exp (- (m : ℝ) * A ^ 2 / (2 * Rmax ^ 2))
      = delta / (2 * (Fintype.card K : ℝ) * N) := by
    have hpos : (0 : ℝ) < 2 * (Fintype.card K : ℝ) * N / delta :=
      div_pos (by positivity) hd1
    have hstep : -(m : ℝ) * A ^ 2 / (2 * Rmax ^ 2) = -L / 2 := by
      have h1 : -(m : ℝ) * A ^ 2 = -(Rmax ^ 2 * L) := by
        rw [← hsq, neg_mul]
      rw [h1, div_eq_div_iff h2ne two_ne_zero]
      ring
    have hL2 : -L / 2 = -Real.log (2 * (Fintype.card K : ℝ) * N / delta) := by
      rw [hLdef]
      ring
    rw [hstep, hL2, Real.exp_neg, Real.exp_log hpos, inv_div]
  -- the per-(i, v) two-sided tail bound: ≤ δ/(|K|·N)
  have hpair : ∀ (i : K) (v : EuclideanSpace ℝ (Fin n)), v ∈ latticeNet n D epsDir M →
      μ.real {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}
        ≤ delta / ((Fintype.card K : ℝ) * N) := by
    intro i v hv
    have hvnorm : ‖v‖ ≤ D + epsDir := latticeNet_norm_le hDE hv
    by_cases hv0 : v = 0
    · subst hv0
      have hset : {ω : Ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, 0⟫_ℝ|} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, inner_zero_right,
          Finset.sum_const_zero, mul_zero, abs_zero]
        exact ⟨fun h => absurd h (not_lt.2 hAnn), fun h => h.elim⟩
      rw [hset, measureReal_empty]
      have hdenpos : (0 : ℝ) < (Fintype.card K : ℝ) * N := by
        have : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
        have hNp : (0 : ℝ) < N := by rw [hN]; positivity
        positivity
      exact div_nonneg hd1.le hdenpos.le
    · set Rv := sigma * ‖v‖ with hRv
      have hRvpos : 0 < Rv := by rw [hRv]; exact mul_pos hsigma (norm_pos_iff.mpr hv0)
      have hRvle : Rv ≤ Rmax := by
        rw [hRv, hRmax]
        exact mul_le_mul_of_nonneg_left hvnorm hsigma.le
      -- the projections are bounded by Rv = σ‖v‖ (Cauchy–Schwarz)
      have hB : ∀ j ω, |⟪xi i j ω, v⟫_ℝ| ≤ Rv := by
        intro j ω
        calc |⟪xi i j ω, v⟫_ℝ| = ‖⟪xi i j ω, v⟫_ℝ‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖xi i j ω‖ * ‖v‖ := norm_inner_le_norm _ _
          _ ≤ Rv := by
              rw [hRv]
              exact mul_le_mul_of_nonneg_right (h_emp_noise_bound i j ω) (norm_nonneg v)
      -- both one-sided Hoeffding tails (R92's minibatch_inner_tail)
      have htail_down := minibatch_inner_tail hm (fun j ω => ⟪xi i j ω, v⟫_ℝ) Rv hRvpos
        (fun j => h_emp_noise_meas i j v hvnorm) (h_emp_noise_indep i v hvnorm)
        (fun j => h_emp_noise_zero i j v hvnorm) hB hAnn
      have htail_up0 := minibatch_inner_tail hm (fun j ω => -(⟪xi i j ω, v⟫_ℝ)) Rv hRvpos
        (fun j => (h_emp_noise_meas i j v hvnorm).neg)
        ((h_emp_noise_indep i v hvnorm).comp _ (fun _ => measurable_id.neg))
        (fun j => by
          show ∫ (x : Ω), -(⟪xi i j x, v⟫_ℝ) ∂μ = 0
          rw [integral_neg, h_emp_noise_zero i j v hvnorm]
          ring)
        (fun j ω => by simpa using hB j ω) hAnn
      have htail_up : μ.real {ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ}
          ≤ Real.exp (- (m : ℝ) * A ^ 2 / (2 * Rv ^ 2)) := by
        have hseteq : {ω : Ω | (m : ℝ) * A ≤ ∑ j, -(-(⟪xi i j ω, v⟫_ℝ))}
            = {ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ} := by
          ext ω
          simp only [Set.mem_ofPred_eq, neg_neg]
        rw [← hseteq]
        exact htail_up0
      -- weaken the exponent from Rv to Rmax (Rv ≤ Rmax)
      have hex : Real.exp (- (m : ℝ) * A ^ 2 / (2 * Rv ^ 2))
          ≤ delta / (2 * (Fintype.card K : ℝ) * N) := by
        have h2 : 2 * Rv ^ 2 ≤ 2 * Rmax ^ 2 := by nlinarith [hRvle, hRvpos.le]
        have hA2nn : (0 : ℝ) ≤ (m : ℝ) * A ^ 2 := by positivity
        have hfrac : (m : ℝ) * A ^ 2 / (2 * Rmax ^ 2) ≤ (m : ℝ) * A ^ 2 / (2 * Rv ^ 2) :=
          div_le_div_of_nonneg_left hA2nn (by positivity) h2
        refine le_trans (Real.exp_le_exp.mpr ?_) (le_of_eq hexp)
        have hnege : (-(m : ℝ)) * A ^ 2 = -((m : ℝ) * A ^ 2) := by ring
        rw [hnege, neg_div, neg_div]
        linarith [hfrac]
      -- the failure event is contained in the union of the two tails
      have hsub : {ω : Ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}
          ⊆ {ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ}
            ∪ {ω : Ω | (m : ℝ) * A ≤ ∑ j, -(⟪xi i j ω, v⟫_ℝ)} := by
        rintro ω hω
        simp only [Set.mem_ofPred_eq] at hω
        have hmp2 : (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ ≠ 0 := by
          intro h0
          rw [h0, abs_zero] at hω
          exact absurd hω (not_lt.2 hAnn)
        rcases lt_or_gt_of_ne hmp2 with hneg | hpos
        · refine Or.inr ?_
          have h1 : A < -((m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ) := by
            rwa [abs_of_neg hneg] at hω
          rw [inv_mul_eq_div, ← neg_div, lt_div_iff₀ hmp] at h1
          have hnegsum : ∑ j, -(⟪xi i j ω, v⟫_ℝ)
              = -∑ j, ⟪xi i j ω, v⟫_ℝ := by simp [Finset.sum_neg_distrib]
          rw [← hnegsum] at h1
          have h2 : (m : ℝ) * A < ∑ j, -(⟪xi i j ω, v⟫_ℝ) := by
            rw [mul_comm]; exact h1
          exact le_of_lt h2
        · refine Or.inl ?_
          have h1 : A < (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ := by
            rwa [abs_of_pos hpos] at hω
          rw [inv_mul_eq_div, lt_div_iff₀ hmp] at h1
          have h2 : (m : ℝ) * A < ∑ j, ⟪xi i j ω, v⟫_ℝ := by
            rw [mul_comm]; exact h1
          exact le_of_lt h2
      calc μ.real {ω : Ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}
          ≤ μ.real ({ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ}
            ∪ {ω : Ω | (m : ℝ) * A ≤ ∑ j, -(⟪xi i j ω, v⟫_ℝ)}) := measureReal_mono hsub
        _ ≤ μ.real {ω : Ω | (m : ℝ) * A ≤ ∑ j, ⟪xi i j ω, v⟫_ℝ}
            + μ.real {ω : Ω | (m : ℝ) * A ≤ ∑ j, -(⟪xi i j ω, v⟫_ℝ)} := measureReal_union_le _ _
        _ ≤ delta / ((Fintype.card K : ℝ) * N) := by
            have hsumle := add_le_add htail_up htail_down
            have hdivpos : (0 : ℝ) < delta / ((Fintype.card K : ℝ) * N) := by
              have hdenpos : (0 : ℝ) < (Fintype.card K : ℝ) * N := by
                have : (0 : ℝ) < (Fintype.card K : ℝ) := by
                  exact_mod_cast Fintype.card_pos
                have hNp : (0 : ℝ) < N := by rw [hN]; positivity
                positivity
              exact div_pos hd1 hdenpos
            have hEq : (2 : ℝ) * (delta / (2 * (Fintype.card K : ℝ) * N))
                = delta / ((Fintype.card K : ℝ) * N) := by ring
            nlinarith [hex, hsumle, hEq]
  -- the per-domain bad event over the net
  have hBadNet : ∀ i, μ.real (⋃ v ∈ latticeNet n D epsDir M,
      {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}) ≤ delta / ((Fintype.card K : ℝ)) := by
    intro i
    calc μ.real (⋃ v ∈ latticeNet n D epsDir M,
          {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|})
        ≤ ∑ v ∈ latticeNet n D epsDir M,
            μ.real {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ v ∈ latticeNet n D epsDir M, delta / ((Fintype.card K : ℝ) * N) :=
          Finset.sum_le_sum fun v hv => hpair i v hv
      _ = (latticeNet n D epsDir M).card * (delta / ((Fintype.card K : ℝ) * N)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (delta / ((Fintype.card K : ℝ) * N)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hN]
          exact_mod_cast latticeNet_card_le n D epsDir M
      _ = delta / ((Fintype.card K : ℝ)) := by field_simp
  -- the total bad event over all domains
  have hBad : μ.real (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
      {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}) ≤ delta := by
    calc μ.real (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
          {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|})
        ≤ ∑ i, μ.real (⋃ v ∈ latticeNet n D epsDir M,
            {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}) :=
          measureReal_iUnion_fintype_le _
      _ ≤ ∑ i, delta / ((Fintype.card K : ℝ)) := Finset.sum_le_sum fun i _ => hBadNet i
      _ = delta := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          exact mul_div_cancel₀ delta hcardKne
  -- measurability of the total bad event
  have hBadMeas : MeasurableSet (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
      {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|}) := by
    refine MeasurableSet.iUnion fun i => Finset.measurableSet_biUnion _ fun v hv => ?_
    have hvnorm : ‖v‖ ≤ D + epsDir := latticeNet_norm_le hDE hv
    have havg : Measurable fun ω => ∑ j, ⟪xi i j ω, v⟫_ℝ :=
      Finset.measurable_sum Finset.univ fun j _ => h_emp_noise_meas i j v hvnorm
    exact measurableSet_lt measurable_const
      (Measurable.abs (measurable_const.mul havg))
  -- the good event: complement of the bad, pointwise containment
  have hcomp : 1 - delta
      ≤ μ.real (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
          {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|})ᶜ := by
    rw [measureReal_compl hBadMeas, probReal_univ]
    linarith
  refine le_trans hcomp (measureReal_mono ?_)
  intro ω hω i v hv
  have hnot : ¬ (A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|) := by
    have h1 : ω ∈ (⋃ i : K, ⋃ v ∈ latticeNet n D epsDir M,
      {ω | A < |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|})ᶜ := hω
    simp only [Set.mem_compl_iff, Set.mem_iUnion] at h1
    push Not at h1
    exact h1 i v hv
  simpa using not_lt.mp hnot

/-- Для любого `dstar : Ω → EuclideanSpace ℝ (Fin n)` с
`‖dstar ω‖ ≤ D` (измеримость не требуется): при статистических
посылках `adaptive_net_concentration` с вероятностью `≥ 1 − δ`
одновременно для всех i выполнено
`|(1/m)Σⱼ ⟪ξ_{i,j}(ω), dstar ω⟫| ≤ adaptiveNoiseEps + σ·epsDir`
(покрытие d* точкой сети + σ-липшицевость ⟪ξ_avg, ·⟫). -/
theorem adaptive_direction_concentration {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : 0 < n)
    (sigma : ℝ) (hsigma : 0 < sigma) (D : ℝ) (hD : 0 ≤ D) (epsDir : ℝ) (hepsDir : 0 < epsDir)
    {M : ℕ} (hM : D * Real.sqrt n / epsDir + 1 ≤ (M : ℝ))
    (xi : K → Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (h_emp_noise_meas : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      Measurable fun ω => ⟪xi i j ω, v⟫_ℝ)
    (h_emp_noise_zero : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      μ[fun ω => ⟪xi i j ω, v⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, v⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (dstar : Ω → EuclideanSpace ℝ (Fin n)) (h_dstar_norm : ∀ ω, ‖dstar ω‖ ≤ D)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) :
    μ.real {ω | ∀ i, |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω⟫_ℝ|
        ≤ adaptiveNoiseEps K n D epsDir M sigma m delta + sigma * epsDir} ≥ 1 - delta := by
  classical
  have hDE : 0 ≤ D + epsDir := by linarith
  have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- the net event, with probability ≥ 1 − δ
  have hE := adaptive_net_concentration (M := M) hm sigma hsigma D hD epsDir hepsDir xi
    h_emp_noise_meas h_emp_noise_zero h_emp_noise_indep h_emp_noise_bound delta hdelta
  -- pointwise transfer: net uniformity + Lipschitz ⟪ξ_avg, ·⟫
  refine le_trans hE (measureReal_mono ?_)
  intro ω hω i
  -- cover d*(ω) by a net point
  obtain ⟨v, hvnet, hdist⟩ :=
    latticeNet_covers hn hD hepsDir hM (dstar ω) (h_dstar_norm ω)
  -- the net bound at v
  have hv := hω i v hvnet
  -- split off the transfer term
  have hsplit : (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω⟫_ℝ
      = (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ
        + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ := by
    have hterm : ∀ j, ⟪xi i j ω, dstar ω⟫_ℝ
        = ⟪xi i j ω, v⟫_ℝ + ⟪xi i j ω, dstar ω - v⟫_ℝ := by
      intro j
      have hvv : v + (dstar ω - v) = dstar ω := by abel
      rw [← inner_add_right, hvv]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hterm j]; ring
  -- |average of the transfer terms| ≤ σ·epsDir (σ-Lipschitz)
  have htransfer : |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ| ≤ sigma * epsDir := by
    have hbound : ∀ j, |⟪xi i j ω, dstar ω - v⟫_ℝ| ≤ sigma * epsDir := by
      intro j
      calc |⟪xi i j ω, dstar ω - v⟫_ℝ|
            = ‖⟪xi i j ω, dstar ω - v⟫_ℝ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖xi i j ω‖ * ‖dstar ω - v‖ := norm_inner_le_norm _ _
        _ ≤ sigma * epsDir :=
            mul_le_mul (h_emp_noise_bound i j ω) hdist (norm_nonneg _) hsigma.le
    have hsumbound : ∑ j, |⟪xi i j ω, dstar ω - v⟫_ℝ| ≤ (m : ℝ) * (sigma * epsDir) := by
      have hle : ∑ j, |⟪xi i j ω, dstar ω - v⟫_ℝ| ≤ ∑ j, sigma * epsDir :=
        Finset.sum_le_sum fun j _ => hbound j
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at hle
      exact hle
    calc |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ|
        ≤ (m : ℝ)⁻¹ * ∑ j, |⟪xi i j ω, dstar ω - v⟫_ℝ| := by
          have h1 := Finset.abs_sum_le_sum_abs (fun j => ⟪xi i j ω, dstar ω - v⟫_ℝ)
            Finset.univ
          have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hmp.le)
          simpa [← Finset.mul_sum] using h2
      _ ≤ (m : ℝ)⁻¹ * ((m : ℝ) * (sigma * epsDir)) :=
          mul_le_mul_of_nonneg_left hsumbound (inv_nonneg.mpr hmp.le)
      _ = sigma * epsDir := by field_simp
  rw [hsplit]
  calc |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ|
      ≤ |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, v⟫_ℝ|
          + |(m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω - v⟫_ℝ| :=
        abs_add_le _ _
    _ ≤ adaptiveNoiseEps K n D epsDir M sigma m delta + sigma * epsDir := by linarith

/-- При посылках `adaptive_direction_concentration`:
с вероятностью `≥ 1 − δ`, если стохастические ограничения
сертифицировали d*(ω) по минибатч-градиентам
(`−eps i ≤ ⟪g i + (1/m)Σⱼ ξ_{i,j}, d*⟫` для всех i),
то `⟪g i, dstar ω⟫ ≥ −(eps i + adaptiveNoiseEps + σ·epsDir)`
для всех i. -/
theorem adaptive_safeQP_feasibility {m : ℕ} (hm : 0 < m) {n : ℕ} (hn : 0 < n)
    (sigma : ℝ) (hsigma : 0 < sigma) (D : ℝ) (hD : 0 ≤ D) (epsDir : ℝ) (hepsDir : 0 < epsDir)
    {M : ℕ} (hM : D * Real.sqrt n / epsDir + 1 ≤ (M : ℝ))
    (g : K → EuclideanSpace ℝ (Fin n))
    (xi : K → Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (h_emp_noise_meas : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      Measurable fun ω => ⟪xi i j ω, v⟫_ℝ)
    (h_emp_noise_zero : ∀ i j (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      μ[fun ω => ⟪xi i j ω, v⟫_ℝ] = 0)
    (h_emp_noise_indep : ∀ i (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ D + epsDir →
      iIndepFun (fun j : Fin m => fun ω => ⟪xi i j ω, v⟫_ℝ) μ)
    (h_emp_noise_bound : ∀ i j ω, ‖xi i j ω‖ ≤ sigma)
    (dstar : Ω → EuclideanSpace ℝ (Fin n)) (h_dstar_norm : ∀ ω, ‖dstar ω‖ ≤ D)
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo 0 1) (eps : K → ℝ) :
    μ.real {ω | (∀ i, -eps i ≤ ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, dstar ω⟫_ℝ)
        → (∀ i, -(eps i + adaptiveNoiseEps K n D epsDir M sigma m delta + sigma * epsDir)
            ≤ ⟪g i, dstar ω⟫_ℝ)} ≥ 1 - delta := by
  classical
  -- the adaptive-direction concentration event
  have hG := adaptive_direction_concentration hm hn sigma hsigma D hD epsDir hepsDir hM xi
    h_emp_noise_meas h_emp_noise_zero h_emp_noise_indep h_emp_noise_bound dstar h_dstar_norm
    delta hdelta
  refine le_trans hG (measureReal_mono ?_)
  rintro ω hω hcert i
  -- split the stochastic inner product
  have hinner : ⟪g i + (m : ℝ)⁻¹ • ∑ j, xi i j ω, dstar ω⟫_ℝ
      = ⟪g i, dstar ω⟫_ℝ + (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω⟫_ℝ := by
    rw [inner_add_left, inner_smul_left, sum_inner]
    simp
  have hnoise := hω i
  obtain ⟨hn1, hn2⟩ := abs_le.mp hnoise
  have hcerti := hcert i
  rw [hinner] at hcerti
  have hbound : -(adaptiveNoiseEps K n D epsDir M sigma m delta + sigma * epsDir)
      ≤ (m : ℝ)⁻¹ * ∑ j, ⟪xi i j ω, dstar ω⟫_ℝ := by
    linarith
  linarith

end AdaptiveSafeQP

end Hagi.Step


set_option linter.style.header false

/-!
# SubspaceSafeQP — концентрация в подпространстве направлений (аудит TD-05)

Размерностный взрыв `adaptiveNoiseEps` = σ(D+ε)·√(2log(2|K|(2M+1)ⁿ/δ)/m)
делает равномерную концентрацию по ε-сети неприменимой к реальным
моделям: log|N| = O(n log M) при n ~ 10⁷ требует m ≫ n.

Лечение (по плану аудита, фаза 5): направление d* и защищённые
градиенты g₁..g_K лежат в r-мерном подпространстве
span{d₀, g₁,…,g_K}, r = K+1 ≪ n. Если ι : ℝ^r → ℝ^n —
линейная изометрия (сохраняет скалярные произведения), и весь
шум лежит в подпространстве (ξ = ιζ), то вся концентрация
переносится на r-мерную сеть: порог зависит от r = K+1,
а не от числа параметров n. Поскольку r ≤ n, подпространный
порог ≤ полноразмерного (`subspace_eps_le_full`).

Имплементационный вывод (докстринг, не теорема): численный
решатель SafeQP должен работать в базисе подпространства
(разложение Каргуена в span{d₀, gᵢ}) — полиномиальная
сложность O(poly(K, m)) вместо экспоненты по n.
-/

open Finset Real MeasureTheory ProbabilityTheory InnerProductSpace

namespace Hagi.Step.SubspaceSafeQP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {K : Type*} [Fintype K] [Nonempty K]

/-- Монотонность сетевого порога по размерности: при r ≤ n
r-мерная сеть не больше n-мерной (2M+1 ≥ 1, степень монотонна).
Это формализует «концентрация в подпространстве дешевле». -/
theorem subspace_eps_le_full {r n : ℕ} (hrn : r ≤ n) (D epsDir : ℝ)
    (hD : 0 ≤ D) (hepsDir : 0 ≤ epsDir) (M : ℕ) (sigma : ℝ)
    (hsigma : 0 ≤ sigma) (m : ℕ) (hm : 0 < m) (delta : ℝ)
    (hdelta : (0:ℝ) < delta)
    (hdle : (delta:ℝ) ≤ 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ)) :
    adaptiveNoiseEps K r D epsDir M sigma m delta
      ≤ adaptiveNoiseEps K n D epsDir M sigma m delta := by
  unfold adaptiveNoiseEps
  have hfac : 0 ≤ sigma * (D + epsDir) :=
    mul_nonneg hsigma (add_nonneg hD hepsDir)
  have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine mul_le_mul le_rfl (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _) hfac
  have h1r : (1:ℝ) ≤ 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ) / delta := by
    rw [le_div_iff₀ hdelta]
    linarith
  have hnum : 2 * Real.log (2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ) / delta)
      ≤ 2 * Real.log (2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ n : ℝ) / delta) := by
    have hrle : ((2 * M + 1) ^ r : ℝ) ≤ ((2 * M + 1) ^ n : ℝ) := by
      norm_cast
      exact Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le (2 * M))) hrn
    have hbase : (0:ℝ) < ((2 * M + 1) ^ r : ℝ) := by
      positivity
    have hcard : 0 < Fintype.card K := Fintype.card_pos (α := K)
    have h1 : (0:ℝ) < 2 := by norm_num
    have h2 : (0:ℝ) < (Fintype.card K : ℝ) := Nat.cast_pos.mpr hcard
    have h3 : (0:ℝ) < ((2 * M + 1) ^ r : ℝ) := hbase
    have hApos : 0 < 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ) / delta :=
      div_pos (mul_pos (mul_pos h1 h2) h3) hdelta
    have hAn : 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ r : ℝ) / delta
        ≤ 2 * (Fintype.card K : ℝ) * ((2 * M + 1) ^ n : ℝ) / delta := by
      have hc2 : (0:ℝ) ≤ 2 * (Fintype.card K : ℝ) := by
        have := mul_nonneg (le_of_lt h1) (le_of_lt h2)
        exact this
      rw [div_le_div_iff_of_pos_right hdelta]
      exact mul_le_mul_of_nonneg_left hrle hc2
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hApos hAn) (by norm_num)
  rw [div_le_div_iff_of_pos_right hmpos]
  exact hnum

end SubspaceSafeQP

end Hagi.Step

/-!
# Варианты SafeQP: метрический SafeQP и KLS-SafeQP

Разделы ниже слиты из отдельных модулей; имена деклараций
сохранены (политика слияний — C416, см. Hagi/Step/SafeQP.lean).

Проекция кандидата d₀ на допустимое множество
`⟪g_i, d⟫ ≥ −ε_i` в метрике d ↦ ‖A d‖ (симметричная
положительно определённая M = AᵀA при самосопряжённом
положительном A).

Существование и единственность сводятся к евклидову SafeQP
заменой координат y = A d: M-проекция d* = A⁻¹ y*, где y* —
евклидова проекция A d₀ на transported-множество с
градиентами (A⁻¹)† g_i.

Утверждений о спуске для исходной цели здесь нет:
метрическая геометрия и геометрия цели независимы —
условие спуска остаётся явной посылкой.
-/

open Real Finset InnerProductSpace InnerProduct

namespace Hagi.Step

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X]
variable {K : Type*} [Fintype K]

/-- M-метрика, заданная невырожденным носителем A:
‖d − e‖_M := ‖A (d − e)‖. -/
def mDist (A : X ≃L[ℝ] X) (d e : X) : ℝ := ‖A (d - e)‖

/-- Транспортированные градиенты: (A⁻¹)† g_i. -/
noncomputable def transportedGrad (A : X ≃L[ℝ] X) (g : K → X) : K → X :=
  fun i => ((A.symm : X →L[ℝ] X)†) (g i)

/-- Ключевой транспорт: в координатах y = A d допустимость
задаётся транспонированными градиентами (A⁻¹)† g_i:
y ∈ safeSet(transportedGrad) ↔ A⁻¹ y ∈ safeSet g. -/
theorem inner_transport (A : X ≃L[ℝ] X) (g : K → X) (eps : K → ℝ)
    (y : X) :
    y ∈ Hagi.safeSet (transportedGrad A g) eps ↔
      A.symm y ∈ Hagi.safeSet g eps := by
  unfold transportedGrad Hagi.safeSet
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i
    have h1 := h i
    have hid : ⟪((A.symm : X →L[ℝ] X)†) (g i), y⟫_ℝ
        = ⟪g i, A.symm y⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_left
        (A.symm : X →L[ℝ] X) y (g i)
    rwa [hid] at h1
  · intro h i
    have h1 := h i
    have hid : ⟪g i, A.symm y⟫_ℝ
        = ⟪((A.symm : X →L[ℝ] X)†) (g i), y⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_left
        (A.symm : X →L[ℝ] X) y (g i)).symm
    rwa [hid] at h1

/-- mDist в координатах y = A d — евклидово расстояние. -/
theorem mDist_eq (A : X ≃L[ℝ] X) (e d0 : X) :
    mDist A e d0 = dist (A e) (A d0) := by
  unfold mDist
  have h1 : e - d0 = A.symm (A e) - A.symm (A d0) := by
    rw [A.symm_apply_apply, A.symm_apply_apply]
  rw [h1, A.map_sub]
  simp only [A.apply_symm_apply, A.apply_symm_apply]
  simp [dist_eq_norm]

/-- Существование и единственность M-проекции: при
неотрицательных ε и невырожденном A M-проекция
существует и единственна — сведение к евклидову SafeQP
в координатах y = A d. -/
theorem mProject_exists_unique (A : X ≃L[ℝ] X)
    (g : K → X) (eps : K → ℝ) (heps : ∀ i, 0 ≤ eps i) (d0 : X) :
    ∃! d : X, d ∈ Hagi.safeSet g eps ∧
      ∀ e ∈ Hagi.safeSet g eps,
        mDist A d d0 ≤ mDist A e d0 := by
  obtain ⟨y, ⟨hy, hymin⟩, hyuni⟩ :=
    Hagi.safeQP_exists_unique (transportedGrad A g) (A d0) eps heps
  have hdy : mDist A (A.symm y) d0 = dist y (A d0) := by
    rw [mDist_eq A (A.symm y) d0, A.apply_symm_apply]
  refine ⟨A.symm y, ⟨?_, ?_⟩, ?_⟩
  · exact (inner_transport A g eps y).mp hy
  · intro e he
    have hAe : A e ∈ Hagi.safeSet (transportedGrad A g) eps := by
      have := (inner_transport A g eps (A e)).mpr
        (show A.symm (A e) ∈ Hagi.safeSet g eps by
          rwa [A.symm_apply_apply])
      exact this
    have hmin := hymin (A e) hAe
    have hde : mDist A e d0 = dist (A e) (A d0) := mDist_eq A e d0
    rw [hdy, hde]
    exact hmin
  · intro d ⟨hd, hdmin⟩
    have hAd : A d ∈ Hagi.safeSet (transportedGrad A g) eps := by
      have := (inner_transport A g eps (A d)).mpr
        (show A.symm (A d) ∈ Hagi.safeSet g eps by
          rwa [A.symm_apply_apply])
      exact this
    have hAmin : ∀ z ∈ Hagi.safeSet (transportedGrad A g) eps,
        dist (A d) (A d0) ≤ dist z (A d0) := by
      intro z hz
      have hz' : A.symm z ∈ Hagi.safeSet g eps :=
        (inner_transport A g eps z).mp hz
      have hmin := hdmin (A.symm z) hz'
      have hz1 : mDist A (A.symm z) d0 = dist z (A d0) := by
        rw [mDist_eq A (A.symm z) d0, A.apply_symm_apply]
      have hd1 : mDist A d d0 = dist (A d) (A d0) := mDist_eq A d d0
      rw [hd1, hz1] at hmin
      exact hmin
    have heq : A d = y := hyuni (A d) ⟨hAd, hAmin⟩
    calc d = A.symm (A d) := (A.symm_apply_apply d).symm
      _ = A.symm y := by rw [heq]

end Hagi.Step

set_option linter.style.header false

/-!
# KLSSafeQP — композиция KLS/Poincaré-шума с SafeQP-запасом

Цепочка: KLS/Poincaré ограничивает дисперсию проекции
минибатча `V = C·L²·‖a‖²/B`; Chebyshev даёт событие
q-вероятности ≥ 1 − V/t². Теорема `klsSafeQP_certified`:
при истинном запасе `ε + |gd|·t` и той же оценке V
зашумлённая проверка сертифицирует ε на событии
q-массы ≥ 1 − V/t².
-/

namespace Hagi.Step

open Finset

/-- При статистических посылках KLS (Poincaré,
чувствительность, некоррелированность батча), точной
девиации `estInner − trueInner` (hdev), `0 < t` и запасе
`ε + |gd|·t ≤ gd·trueInner x` для всех x —
множество `{x | ε ≤ gd·estInner x}` имеет q-массу
≥ 1 − (C·L²·‖a‖²/B)/t². -/
theorem klsSafeQP_certified {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (q : Ω → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (C L : ℝ) (hC : 0 ≤ C)
    (sens : (Fin n → ℝ) → Ω → ℝ)
    (hpoincare : ∀ (g : Ω → Fin n → ℝ) (a : Fin n → ℝ),
      Probability.gradVar q g a ≤ C * Probability.expQ q (fun x => (sens a x) ^ 2))
    (hop : ∀ (a : Fin n → ℝ) (x : Ω), (sens a x) ^ 2 ≤ L ^ 2 * Probability.sqN a)
    {B : ℕ} (hB : 0 < B) (g : Fin B → Ω → Fin n → ℝ) (a : Fin n → ℝ)
    (huncorr : ∀ i j, i ≠ j →
      Probability.expQ q (fun x => (Probability.proj a (g i x)
          - Probability.expQ q (fun y => Probability.proj a (g i y)))
        * (Probability.proj a (g j x)
          - Probability.expQ q (fun y => Probability.proj a (g j y)))) = 0)
    (trueInner : Ω → ℝ) (estInner : Ω → ℝ)
    (hdev : ∀ x, estInner x - trueInner x
      = (∑ i, Probability.proj a (g i x) / B
          - (∑ i, Probability.expQ q (fun y => Probability.proj a (g i y))) / B))
    (gd : ℝ) (eps t : ℝ) (ht : 0 < t)
    (htrue : ∀ x, eps + |gd| * t ≤ gd * trueInner x) :
    (∑ x ∈ Finset.univ.filter (fun x => eps ≤ gd * estInner x), q x)
      ≥ 1 - (C * L ^ 2 * Probability.sqN a / B) / t ^ 2 := by
  -- the deviation field
  set dev : Ω → ℝ := fun x => ∑ i, Probability.proj a (g i x) / B
    - (∑ i, Probability.expQ q (fun y => Probability.proj a (g i y))) / B with hdevdef
  -- the KLS chain bounds its second moment
  set V := C * L ^ 2 * Probability.sqN a / B with hVdef
  have hnoise : Probability.expQ q (fun x => (dev x) ^ 2) ≤ V :=
    Probability.klsBatchNoise q hq0 hq1 C L hC sens hpoincare hop hB g a huncorr
  -- Chebyshev: the bad set has q-mass at most V / t^2
  have hbad : (∑ x ∈ Finset.univ.filter (fun x => t ≤ |dev x|), q x)
      ≤ V / t ^ 2 :=
    Probability.klsChebyshev q hq0 V t ht dev hnoise
  -- the certified set contains the complement of the bad set
  have hmono : (Finset.univ.filter (fun x => ¬(t ≤ |dev x|)))
      ⊆ Finset.univ.filter (fun x => eps ≤ gd * estInner x) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ x, ?_⟩
    have hlt : |dev x| < t := by
      by_contra hcon
      exact absurd (le_of_not_gt hcon) hx.2
    have hest : estInner x = trueInner x + dev x := by
      have h1 := hdev x
      linarith [h1]
    -- |dev x| <= t (non-strict is enough with a strict margin)
    have habsdev : |dev x| ≤ t := le_of_lt hlt
    -- |gd| * |dev x| <= |gd| * t
    have hbnd : |gd| * |dev x| ≤ |gd| * t :=
      mul_le_mul_of_nonneg_left habsdev (abs_nonneg gd)
    -- chain
    rw [hest]
    have htr := htrue x
    have hkey : |gd| * |dev x| ≤ |gd| * t := hbnd
    have hsplit : gd * dev x ≥ -(|gd| * t) := by
      have hEq : |gd * dev x| = |gd| * |dev x| := abs_mul gd (dev x)
      have h0 := neg_le_abs (gd * dev x)
      linarith [hkey, h0, hEq]
    nlinarith [htr, hsplit, abs_nonneg gd]
  -- the two filters partition the mass
  have hpart : (∑ x ∈ Finset.univ.filter (fun x => t ≤ |dev x|), q x)
      + (∑ x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)), q x)
      = ∑ x, q x := by
    rw [Finset.sum_filter_add_sum_filter_not]
  -- the certified mass dominates the complement's mass
  have hdom : (∑ x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)), q x)
      ≤ (∑ x ∈ Finset.univ.filter (fun x => eps ≤ gd * estInner x), q x) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases h1 : ¬(t ≤ |dev x|)
    · have hmem : x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ x, h1⟩
      have hgood := hmono hmem
      rw [Finset.mem_filter] at hgood
      rw [ite_eq_left h1, ite_eq_left hgood.2]
    · by_cases h2 : eps ≤ gd * estInner x
      · rw [ite_eq_right h1, ite_eq_left h2]
        exact hq0 x
      · rw [ite_eq_right h1, ite_eq_right h2]
  -- assemble
  calc (∑ x ∈ Finset.univ.filter (fun x => eps ≤ gd * estInner x), q x)
      ≥ (∑ x ∈ Finset.univ.filter (fun x => ¬(t ≤ |dev x|)), q x) := hdom
    _ = 1 - (∑ x ∈ Finset.univ.filter (fun x => t ≤ |dev x|), q x) := by
        rw [hq1] at hpart
        linarith
    _ ≥ 1 - V / t ^ 2 := by
        linarith [hbad]
end Hagi.Step
