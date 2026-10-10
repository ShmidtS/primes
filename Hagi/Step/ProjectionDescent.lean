/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Audit.Exactness

/-!
# ProjectionDescent — канонический Step-слой вертикали спуска проекции

Пере-форматирование `min_dist_to_vi → safeQP_descent` из
`Audit.Exactness` (те же доказательства и сигнатуры), чтобы
потребители импортировали Step-слой, а не Audit.

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
theorem min_dist_to_vi (C : Set X) (hconv : Convex ℝ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0) :
    ∀ w ∈ C, ⟪g0 - ds, w - ds⟫_ℝ ≤ 0 :=
  Hagi.min_dist_to_vi C hconv g0 ds hs hmin

/-- При выпуклом C с `0 ∈ C`, `ds ∈ C` и минимизирующем
расстояние до g0:
`‖ds‖² ≤ ⟪g0, ds⟫_ℝ` и `‖g0 − ds‖ ≤ ‖g0‖`. -/
theorem safeQP_descent (C : Set X) (hconv : Convex ℝ C)
    (h0 : (0:X) ∈ C) (g0 ds : X)
    (hs : ds ∈ C) (hmin : ∀ d ∈ C, dist ds g0 ≤ dist d g0) :
    ‖ds‖^2 ≤ ⟪g0, ds⟫_ℝ ∧ ‖g0 - ds‖ ≤ ‖g0‖ :=
  Hagi.safeQP_descent C hconv h0 g0 ds hs hmin

end Hagi.Step
