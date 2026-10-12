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
  exact Hagi.Foundations.joint_stage L eta ‖ds‖ (⟪g0, ds⟫_ℝ) E2 E1 hL heta heta0 hdescent' h_emp_smooth

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
export Hagi.Step (proj_descent_inner min_dist_to_vi safeQP_descent joint_stage_linked orthogonal_zero_interference hard_budget_forces_orthogonal)
end Hagi
