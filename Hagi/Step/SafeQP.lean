/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib

set_option linter.style.header false

/-!
# SafeQP — линеаризованная проекция доменной безопасности для joint-шага

Направление joint-шага — проекция градиента смеси g на
пересечение полупространств безопасности
`K_safe = {d | ⟪g i, d⟫ ≥ −ε i для всех i}`.

* `safeQP_exists_unique`: при `0 ≤ ε i` и конечномерном X
  проекция на `safeSet` существует и единственна;
* `safeQP_noconflict`: если `g0 ∈ safeSet`, то g0 минимизирует
  расстояние до себя (контроллер неактивен без конфликта);
* `safeqp_inactive`: при `g0 ∈ safeSet` любой минимизатор ds
  равен g0.

Вспомогательные: `safeSet`, `halfspace_convex`,
`safeSet_nonempty`, `convex_min_unique`, `halfspace_closed`,
`safeSet_closed`.
-/

open Finset InnerProductSpace Metric

namespace Hagi

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

set_option linter.unusedDecidableInType false in
-- hypothesis kept: documented API premise
/-- Для любых d из safeSet: `dist g0 g0 ≤ dist d g0`
(тривиально: g0 минимизирует расстояние до себя). -/
theorem safeQP_noconflict (g : K → X) (g0 : X) (eps : K → ℝ)
    (_heps : ∀ i, 0 ≤ eps i)
    (_hsafe : g0 ∈ safeSet g eps) :
    ∀ d ∈ safeSet g eps, dist g0 g0 ≤ dist d g0 := by
  intro d _
  simp

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

end Hagi
