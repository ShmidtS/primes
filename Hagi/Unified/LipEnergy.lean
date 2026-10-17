/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib

/-!
# LipEnergy — градиентная модель липшицевости (R563)

Вывод посылки h_emp_lip-семейства («энергия κ-Липшицева по
квантованию весов») из градиентной модели: если энергия
дифференцируема и ‖∇E(x)‖ ≤ κ всюду, то по MVT на сегменте
|E(w) − E(q)| ≤ κ·‖w − q‖. Это МОДЕЛЬ ВЫПУКЛОСТИ,
закрывающая открытый пункт STATUS (h_emp_lip) на уровне
согласованной посылки: измеренный κ = sup‖∇E‖.
-/

open scoped BigOperators

namespace Hagi.Unified

/-- **Градиентная липшицевость (R563)**: дифференцируемая
энергия с ограниченной производной κ-Липшицева на всём
пространстве (MVT на сегменте). Это модель h_emp_lip:
измеренный κ есть sup‖∇E‖. -/
theorem lip_energy_from_gradient {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W]
    (E : W → ℝ) (kappa : ℝ)
    (hdiff : ∀ w : W, HasFDerivAt E (fderiv ℝ E w) w)
    (hnorm : ∀ w : W, ‖fderiv ℝ E w‖ ≤ kappa)
    (w q : W) :
    |E w - E q| ≤ kappa * ‖w - q‖ := by
  rw [← Real.norm_eq_abs]
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hdiff x).hasFDerivWithinAt (s := segment (𝕜 := ℝ) q w))
    (fun x _ => hnorm x) (convex_segment q w)
    (left_mem_segment _ q w) (right_mem_segment _ _ _)

/-- Следствие для квантованных весов: h_emp_lip-форма
«dE ≤ κ·dist(w, q)» — искажения энергии от округления весов
ограничены κ-кратным расстоянием до квантованной точки. -/
theorem lip_energy_quantization {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W]
    (E : W → ℝ) (kappa : ℝ)
    (hdiff : ∀ w : W, HasFDerivAt E (fderiv ℝ E w) w)
    (hnorm : ∀ w : W, ‖fderiv ℝ E w‖ ≤ kappa)
    (w : W) (qTern : W → W) :
    |E w - E (qTern w)| ≤ kappa * ‖w - qTern w‖ :=
  lip_energy_from_gradient E kappa hdiff hnorm w (qTern w)

end Hagi.Unified
