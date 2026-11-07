/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Foundations.StageCalculus

/-!
# ProjectionDescent — канонический Step-слой вертикали спуска проекции

Канонический оптимизационный слой теории проекции (R321,
перенесено из Audit.Foundations/Exactness — аудит v3 §2.2):
Step больше не импортирует Audit.

Для выпуклого C и минимизатора расстояния ds до g0:

* `min_dist_to_vi`: `⟪g0 − ds, w − ds⟫ ≤ 0` для всех `w ∈ C`;
* `safeQP_descent`: при `0 ∈ C` — `‖ds‖² ≤ ⟪g0, ds⟫` и
  `‖g0 − ds‖ ≤ ‖g0‖`.
-/

open InnerProductSpace

namespace Hagi.Step

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- При выпуклом C, `ds ∈ C` и минимизирующем расстояние до
g0: `⟪g0 − ds, w − ds⟫_ℝ ≤ 0` для всех `w ∈ C`
(вариационное неравенство проекции). -/
theorem proj_descent_inner (C : Set X) (_hconv : Convex ℝ C)
    (h0 : (0:X) ∈ C) (g dstar : X)
    (hproj : ∀ w ∈ C, ⟪g - dstar, w - dstar⟫_ℝ ≤ 0)
    (_hd : dstar ∈ C) : ‖dstar‖^2 ≤ ⟪g, dstar⟫_ℝ := by
  have h0v : ⟪g - dstar, (0:X) - dstar⟫_ℝ ≤ 0 := hproj 0 h0
  have hexp : ⟪g - dstar, (0:X) - dstar⟫_ℝ = ⟪g - dstar, -dstar⟫_ℝ := by
    congr 1
    abel
  rw [hexp] at h0v
  rw [inner_sub_left, inner_neg_right, inner_neg_right] at h0v
  have hself : ⟪dstar, dstar⟫_ℝ = ‖dstar‖^2 := by
    have := inner_self_eq_norm_sq (𝕜 := ℝ) dstar
    simpa [RCLike.inner_apply, RCLike.re_to_real] using this
  rw [hself] at h0v
  linarith

theorem min_dist_to_vi (C : Set X) (hconv : Convex ℝ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0) :
    ∀ w ∈ C, ⟪g0 - ds, w - ds⟫_ℝ ≤ 0 := by
  have hkey : ‖g0 - ds‖ ≤ ⨅ w : C, ‖g0 - (w : X)‖ := by
    have hCne : Nonempty C := ⟨ds, hs⟩
    exact le_ciInf (f := fun w : C => ‖g0 - (w : X)‖)
      (fun w => by
        have hw := hmin (w : X) w.2
        rw [dist_eq_norm, dist_eq_norm] at hw
        rw [norm_sub_rev] at hw
        rw [norm_sub_rev g0 (w : X)]
        exact hw)
  have hkey2 : (⨅ w : C, ‖g0 - (w : X)‖) ≤ ‖g0 - ds‖ := by
    have hbdd : BddBelow (Set.range fun w : C => ‖g0 - (w : X)‖) :=
      ⟨(0:ℝ), by
        rintro y ⟨w, rfl⟩
        exact norm_nonneg _⟩
    exact ciInf_le hbdd (⟨ds, hs⟩ : C)
  have hkeyE : ‖g0 - ds‖ = ⨅ w : C, ‖g0 - (w : X)‖ :=
    le_antisymm hkey hkey2
  exact (norm_eq_iInf_iff_real_inner_le_zero hconv hs).mp hkeyE

/-! ## Exact minimum-norm point on a finite segment -/

/-- The ray coefficient of the minimum-norm point on the segment from
`g0` to `g1`.  When the endpoints coincide, their common point is the
minimum and the coefficient is zero. -/
noncomputable def segmentMinNormCoefficient (g0 g1 : X) : ℝ := by
  classical
  exact if g1 - g0 = 0 then 0
    else min 1 (max 0 (-⟪g0, g1 - g0⟫_ℝ / ‖g1 - g0‖ ^ 2))

/-- The exact minimum-norm point on the segment from `g0` to `g1`. -/
noncomputable def segmentMinNorm (g0 g1 : X) : X :=
  g0 + segmentMinNormCoefficient g0 g1 • (g1 - g0)

/-- The clamped ray coefficient lies between zero and one. -/
theorem segmentMinNormCoefficient_mem_Icc (g0 g1 : X) :
    segmentMinNormCoefficient g0 g1 ∈ Set.Icc (0 : ℝ) 1 := by
  unfold segmentMinNormCoefficient
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- Parametrize a point of a segment as `g0 + τ • (g1 - g0)`. -/
theorem eq_add_smul_sub_of_mem_segment {g0 g1 p : X}
    (hp : p ∈ segment ℝ g0 g1) :
    ∃ τ ∈ Set.Icc (0 : ℝ) 1, p = g0 + τ • (g1 - g0) := by
  rw [segment_eq_image' ℝ] at hp
  obtain ⟨τ, hτ, rfl⟩ := hp
  exact ⟨τ, hτ, rfl⟩

/-- The exact minimum-norm point belongs to its segment. -/
theorem segmentMinNorm_mem_segment (g0 g1 : X) :
    segmentMinNorm g0 g1 ∈ segment ℝ g0 g1 := by
  rw [segment_eq_image' ℝ]
  exact ⟨segmentMinNormCoefficient g0 g1,
    segmentMinNormCoefficient_mem_Icc g0 g1, rfl⟩

/-- Subtracting two points on one ray factors through their coefficients. -/
theorem inner_segment_ray_sub (g0 d : X) (τ r : ℝ) :
    ⟪g0 + τ • d - (g0 + r • d), g0 + r • d⟫_ℝ =
      (τ - r) * ⟪d, g0 + r • d⟫_ℝ := by
  have hvec : g0 + τ • d - (g0 + r • d) = (τ - r) • d := by
    rw [sub_smul]
    abel
  rw [hvec, real_inner_smul_left]

/-- Projection variational inequality for the exact segment minimizer:
the angle from the minimizer to every other segment point is non-obtuse. -/
theorem segmentMinNorm_inner_nonneg (g0 g1 p : X)
    (hp : p ∈ segment ℝ g0 g1) :
    0 ≤ ⟪p - segmentMinNorm g0 g1, segmentMinNorm g0 g1⟫_ℝ := by
  obtain ⟨τ, hτ, rfl⟩ := eq_add_smul_sub_of_mem_segment hp
  by_cases hd : g1 - g0 = 0
  · have hp0 : g0 + τ • (g1 - g0) = g0 := by
      rw [hd, smul_zero, add_zero]
    have hz : segmentMinNorm g0 g1 = g0 := by
      simp [segmentMinNorm, segmentMinNormCoefficient, hd]
    rw [hp0, hz, sub_self, inner_zero_left]
  · let d : X := g1 - g0
    let r : ℝ := -⟪g0, d⟫_ℝ / ‖d‖ ^ 2
    change d ≠ 0 at hd
    have hnormsq : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.mpr hd) 2
    have hcoef : segmentMinNormCoefficient g0 g1 = min 1 (max 0 r) := by
      simp only [segmentMinNormCoefficient, hd, ↓reduceIte, d, r]
    have hr_scaled : r * ‖d‖ ^ 2 = -⟪g0, d⟫_ℝ := by
      dsimp [r]
      field_simp [ne_of_gt hnormsq]
    by_cases hr0 : 0 < r
    · by_cases hr1 : r < 1
      · have hcoeff : segmentMinNormCoefficient g0 g1 = r := by
          rw [hcoef, max_eq_right hr0.le, min_eq_right hr1.le]
        have hz : segmentMinNorm g0 g1 = g0 + r • d := by
          simp only [segmentMinNorm, hcoeff, d]
        have hdz : ⟪d, g0 + r • d⟫_ℝ = 0 := by
          rw [inner_add_right, real_inner_smul_right, real_inner_comm g0 d,
            real_inner_self_eq_norm_sq]
          linarith
        rw [hz, inner_segment_ray_sub, hdz, mul_zero]
      · have h1r : 1 ≤ r := le_of_not_gt hr1
        have hr0' : 0 ≤ r := zero_le_one.trans h1r
        have hcoeff : segmentMinNormCoefficient g0 g1 = 1 := by
          rw [hcoef, max_eq_right hr0', min_eq_left h1r]
        have hz : segmentMinNorm g0 g1 = g0 + (1 : ℝ) • d := by
          simp only [segmentMinNorm, hcoeff, d]
        have hprod : ‖d‖ ^ 2 ≤ r * ‖d‖ ^ 2 := by
          simpa using mul_le_mul_of_nonneg_right h1r hnormsq.le
        rw [hr_scaled] at hprod
        have hdg1 : ⟪d, g0 + d⟫_ℝ ≤ 0 := by
          rw [inner_add_right, real_inner_comm g0 d, real_inner_self_eq_norm_sq]
          linarith
        rw [hz, inner_segment_ray_sub, one_smul]
        calc
          0 ≤ (1 - τ) * (-⟪d, g0 + d⟫_ℝ) :=
            mul_nonneg (sub_nonneg.mpr hτ.2) (neg_nonneg.mpr hdg1)
          _ = (τ - 1) * ⟪d, g0 + d⟫_ℝ := by ring
    · have hrle : r ≤ 0 := le_of_not_gt hr0
      have hcoeff : segmentMinNormCoefficient g0 g1 = 0 := by
        rw [hcoef, max_eq_left hrle, min_eq_right zero_le_one]
      have hz : segmentMinNorm g0 g1 = g0 + (0 : ℝ) • d := by
        simp only [segmentMinNorm, hcoeff, d]
      have hprod : r * ‖d‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hrle hnormsq.le
      rw [hr_scaled] at hprod
      have hg0d : 0 ≤ ⟪g0, d⟫_ℝ := by linarith
      have hdg : 0 ≤ ⟪d, g0⟫_ℝ := by
        rwa [real_inner_comm g0 d]
      rw [hz, inner_segment_ray_sub]
      simp only [zero_smul, add_zero, sub_zero]
      exact mul_nonneg hτ.1 hdg

/-- The exact segment projection minimizes norm over the whole segment. -/
theorem segmentMinNorm_norm_le (g0 g1 p : X)
    (hp : p ∈ segment ℝ g0 g1) : ‖segmentMinNorm g0 g1‖ ≤ ‖p‖ := by
  have hkkt := segmentMinNorm_inner_nonneg g0 g1 p hp
  have hp_eq : p = segmentMinNorm g0 g1 + (p - segmentMinNorm g0 g1) := by
    abel
  rw [← real_inner_comm (p - segmentMinNorm g0 g1)
    (segmentMinNorm g0 g1)] at hkkt
  have hsq : ‖segmentMinNorm g0 g1‖ ^ 2 ≤ ‖p‖ ^ 2 := by
    rw [hp_eq, norm_add_sq_real]
    nlinarith [sq_nonneg ‖p - segmentMinNorm g0 g1‖]
  nlinarith [norm_nonneg (segmentMinNorm g0 g1), norm_nonneg p]

/-- Two norm minimizers on a convex set coincide. -/
theorem eq_of_mem_of_forall_norm_le {C : Set X} (hC : Convex ℝ C)
    {x z : X} (hx : x ∈ C) (hz : z ∈ C)
    (hxmin : ∀ p ∈ C, ‖x‖ ≤ ‖p‖) (hzmin : ∀ p ∈ C, ‖z‖ ≤ ‖p‖) :
    x = z := by
  have hxdist : ∀ p ∈ C, dist x 0 ≤ dist p 0 := by
    intro p hp
    simpa only [dist_eq_norm, sub_zero] using hxmin p hp
  have hzdist : ∀ p ∈ C, dist z 0 ≤ dist p 0 := by
    intro p hp
    simpa only [dist_eq_norm, sub_zero] using hzmin p hp
  have hxvi := min_dist_to_vi C hC 0 x hx hxdist z hz
  have hzvi := min_dist_to_vi C hC 0 z hz hzdist x hx
  simp only [zero_sub, inner_neg_left, inner_sub_right,
    real_inner_self_eq_norm_sq] at hxvi hzvi
  rw [real_inner_comm x z] at hzvi
  have hsq : ‖x - z‖ ^ 2 = 0 := by
    apply le_antisymm
    · rw [norm_sub_sq_real]
      nlinarith
    · exact sq_nonneg _
  have hnorm : ‖x - z‖ = 0 := by
    nlinarith [norm_nonneg (x - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Any norm minimizer on a segment is its exact `segmentMinNorm` point. -/
theorem eq_segmentMinNorm_of_mem_of_forall_norm_le {g0 g1 x : X}
    (hx : x ∈ segment ℝ g0 g1)
    (hxmin : ∀ p ∈ segment ℝ g0 g1, ‖x‖ ≤ ‖p‖) :
    x = segmentMinNorm g0 g1 := by
  exact eq_of_mem_of_forall_norm_le (convex_segment g0 g1) hx
    (segmentMinNorm_mem_segment g0 g1) hxmin
    (fun p hp => segmentMinNorm_norm_le g0 g1 p hp)

/-- При выпуклом C с `0 ∈ C`, `ds ∈ C` и минимизирующем
расстояние до g0:
`‖ds‖² ≤ ⟪g0, ds⟫_ℝ` и `‖g0 − ds‖ ≤ ‖g0‖`. -/
theorem safeQP_descent (C : Set X) (hconv : Convex ℝ C)
    (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0) :
    ‖ds‖^2 ≤ ⟪g0, ds⟫_ℝ ∧ ‖g0 - ds‖ ≤ ‖g0‖ := by
  refine ⟨?_, ?_⟩
  · exact proj_descent_inner C hconv h0 g0 ds
      (min_dist_to_vi C hconv g0 ds hs hmin) hs
  · have h := hmin 0 h0
    rw [dist_eq_norm, dist_eq_norm] at h
    have h2 : ‖0 - g0‖ = ‖g0‖ := by rw [zero_sub, norm_neg]
    have h3 : ‖ds - g0‖ = ‖g0 - ds‖ := norm_sub_rev _ _
    rw [h2, h3] at h
    exact h

/-- With `ds` the minimizer of the distance to `g0` over a
convex set (so `‖ds‖² ≤ ⟪g0, ds⟫` by `safeQP_descent`),
`0 < L`, `0 ≤ eta ≤ 1/L`, and the smoothness premise
(h_emp_), `E2 ≤ E1 − eta * ‖ds‖² / 2`. -/
theorem joint_stage_linked {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (C : Set X) (hconv : Convex ℝ C) (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0)
    (L eta E1 E2 : ℝ) (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (h_emp_smooth : E2 ≤ E1 - eta * ⟪g0, ds⟫_ℝ + L * eta ^ 2 * ‖ds‖ ^ 2 / 2) :
    E2 ≤ E1 - eta * ‖ds‖ ^ 2 / 2 := by
  have hdescent' : ‖ds‖ ^ 2 ≤ ⟪g0, ds⟫_ℝ :=
    (safeQP_descent C hconv h0 g0 ds hs hmin).1
  exact Hagi.Foundations.joint_stage L eta ‖ds‖ (⟪g0, ds⟫_ℝ)
    E2 E1 hL heta heta0 hdescent' h_emp_smooth

/-! ## Orthogonal projection = zero interference (R348)

The GPM/EoupCT family (Saha et al. 2021, arXiv:2103.09762;
Wang et al. 2026, arXiv:2609.30935) constrains new-task
updates to be orthogonal to stored past-task gradients.
In the SafeQP frame this is the exact-interference-zero
limit: an update direction orthogonal to every protected
gradient satisfies every SafeQP constraint
`⟪g i, d⟫ ≥ −ε i` with ANY `ε i ≥ 0` — including the hard
budget `ε i = 0`. Orthogonal projection is thus the
`ε = 0` special case of SafeQP with zero risk spend. -/

/-- If `d` is orthogonal to every protected gradient `g i`,
then `d` lies in the SafeQP feasible set
`C = {w | ∀ i, ⟪g i, w⟫ ≥ −ε i}` for any `ε i ≥ 0`
— including `ε i = 0` (zero tolerated interference). -/
theorem orthogonal_zero_interference {K : Type*}
    (g : K → X) (eps : K → ℝ) (heps : ∀ i, 0 ≤ eps i)
    (d : X) (hortho : ∀ i, ⟪g i, d⟫_ℝ = 0) :
    ∀ i, -eps i ≤ ⟪g i, d⟫_ℝ := by
  intro i
  rw [hortho i]
  exact neg_nonpos.2 (heps i)

/-- Converse limit: orthogonality is exactly what the hard
SafeQP budget `ε = 0` demands when interference must be
non-positive on both sides — the `ε = 0` cap forces
`⟪g i, d⟫ = 0`. -/
theorem hard_budget_forces_orthogonal {K : Type*}
    (g : K → X) (d : X)
    (hd : ∀ i, ⟪g i, d⟫_ℝ ≥ 0 ∧ ⟪g i, d⟫_ℝ ≤ 0) :
    ∀ i, ⟪g i, d⟫_ℝ = 0 := by
  intro i
  exact le_antisymm (hd i).2 (hd i).1

end Hagi.Step

namespace Hagi
export Hagi.Step (min_dist_to_vi safeQP_descent joint_stage_linked)
end Hagi
