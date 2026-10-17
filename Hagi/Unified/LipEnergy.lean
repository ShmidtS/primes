/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Foundations.StageCalculus

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


/-- **h_emp_grow из certified descent (R564)**: энергетический
учёт grow-стадии (growEnergy ≤ energy − growGain) — точная
форма joint_stage (StageCalculus): upper-quadratic модель
(h_emp_smooth) + certified descent (dnorm² ≤ inner) + SafeQP-
окно (0 < L, 0 ≤ η ≤ 1/L) ⟹ E2 ≤ E1 − η·dnorm²/2. Поле
 выигрыша growGain := η·dnorm²/2 — измеримая величина (шаг ×
квадрат нормы направления). -/
theorem grow_gain_from_smooth_descent (L eta dnorm inner E2 E1 : ℝ)
    (hL : 0 < L) (heta : eta ≤ 1 / L) (heta0 : 0 ≤ eta)
    (hdescent : dnorm ^ 2 ≤ inner)
    (h_emp_smooth : E2 ≤ E1 - eta * inner + L * eta ^ 2 * dnorm ^ 2 / 2) :
    E2 ≤ E1 - eta * dnorm ^ 2 / 2 :=
  Hagi.Foundations.joint_stage L eta dnorm inner E2 E1 hL heta
    heta0 hdescent h_emp_smooth


open Real intervalIntegral

/-- Производная энергии вдоль сегмента (chain rule; R565.2). -/
theorem hasDerivAt_along_segment {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (E : W → ℝ) (dir q : W)
    (hdiff : ∀ w : W, HasFDerivAt E (fderiv ℝ E w) w)
    (t : ℝ) :
    HasDerivAt (fun s => E (q + s • dir)) (fderiv ℝ E (q + t • dir) dir) t := by
  have h1 := hdiff (q + t • dir)
  have h2 : HasDerivAt (fun s : ℝ => q + s • dir) dir t := by
    simpa using HasDerivAt.fun_add (hasDerivAt_const t q)
      ((hasDerivAt_id t).smul_const dir)
  exact HasFDerivAt.comp_hasDerivAt (l := E) t h1 h2

/-- Интеграл производной вдоль сегмента = приращение (Newton-
Leibniz, R565.2). -/
theorem integral_deriv_segment {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] (E : W → ℝ) (dir q : W)
    (hdiff : ∀ w : W, HasFDerivAt E (fderiv ℝ E w) w)
    (hgcont : Continuous fun t : ℝ => fderiv ℝ E (q + t • dir) dir) :
    ∫ (t : ℝ) in (0:ℝ)..1, fderiv ℝ E (q + t • dir) dir
      = E (q + dir) - E q := by
  have hint := intervalIntegral.integral_deriv_eq_sub'
    (a := 0) (b := 1) (fun s => E (q + s • dir))
    (funext (fun t => (hasDerivAt_along_segment E dir q hdiff t).deriv))
    (fun t _ => (hasDerivAt_along_segment E dir q hdiff t).differentiableAt)
    (Continuous.continuousOn hgcont)
  simpa [one_smul] using hint

end Hagi.Unified
