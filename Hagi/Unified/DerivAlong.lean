/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Foundations.StageCalculus
import Hagi.Energy.Quantizer
import Hagi.System.GrowthState
import Mathlib
open InnerProductSpace
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

/-!
# DerivAlong — точечная оценка производной вдоль сегмента (R565.3)

Финальное звено h_emp_smooth-модели: g'(t) ≤ g'(0) + L·t·‖dir‖²
из L-гладкости (‖∇E(y) − ∇E(x)‖ ≤ L‖y − x‖) + Cauchy–Schwarz
для CLM.
-/

open Real

namespace Hagi.Unified

/-- **Точечная оценка (R565.3)**: производная вдоль сегмента
ограничена начальным направленным градиентом + L·t·‖dir‖². -/
theorem deriv_along_segment_le {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W]
    (E : W → ℝ) (dir q : W) (L : ℝ)
    (hsmooth : ∀ x y : W, ‖fderiv ℝ E y - fderiv ℝ E x‖ ≤ L * ‖y - x‖)
    (t : ℝ) (ht0 : 0 ≤ t) :
    fderiv ℝ E (q + t • dir) dir
      ≤ fderiv ℝ E q dir + L * t * ‖dir‖^2 := by
  have hsplit : fderiv ℝ E (q + t • dir) dir
      = fderiv ℝ E q dir
        + (fderiv ℝ E (q + t • dir) - fderiv ℝ E q) dir := by
    have hlin := sub_apply (fderiv ℝ E (q + t • dir))
      (fderiv ℝ E q) dir
    rw [hlin]; ring
  have hcs : ‖(fderiv ℝ E (q + t • dir) - fderiv ℝ E q) dir‖
      ≤ ‖fderiv ℝ E (q + t • dir) - fderiv ℝ E q‖ * ‖dir‖ :=
    ContinuousLinearMap.le_opNorm _ dir
  have hseg : ‖q + t • dir - q‖ = t * ‖dir‖ := by
    have hs : q + t • dir - q = t • dir := by simp
    rw [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hdelta : ‖fderiv ℝ E (q + t • dir) - fderiv ℝ E q‖
      ≤ L * (t * ‖dir‖) := by
    have h := hsmooth q (q + t • dir)
    rw [hseg] at h
    exact h
  -- ключевой скалярный факт: значение ≤ его норме
  have hval : (fderiv ℝ E (q + t • dir) - fderiv ℝ E q) dir
      ≤ ‖(fderiv ℝ E (q + t • dir) - fderiv ℝ E q) dir‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  calc fderiv ℝ E (q + t • dir) dir
      = fderiv ℝ E q dir
        + (fderiv ℝ E (q + t • dir) - fderiv ℝ E q) dir := by rw [hsplit]
    _ ≤ fderiv ℝ E q dir
        + ‖(fderiv ℝ E (q + t • dir) - fderiv ℝ E q) dir‖ :=
          add_le_add_right hval _
    _ ≤ fderiv ℝ E q dir
        + ‖fderiv ℝ E (q + t • dir) - fderiv ℝ E q‖ * ‖dir‖ :=
          add_le_add_right hcs _
    _ ≤ fderiv ℝ E q dir + L * (t * ‖dir‖) * ‖dir‖ :=
          add_le_add_right
            (mul_le_mul_of_nonneg_right hdelta (norm_nonneg dir)) _
    _ = fderiv ℝ E q dir + L * t * ‖dir‖^2 := by ring


open intervalIntegral in
/-- **Гладкость ⟹ верхняя квадратичная модель (R565, h_emp_smooth)**:
L-гладкость градиента даёт верхнюю квадратичную модель энергии:
E(q+dir) ≤ E(q) + ⟨∇E(q), dir⟩ + L·‖dir‖²/2.
Это точная форма h_emp_smooth (StageCalculus) при eta = 1,
dnorm² = ‖dir‖², inner = ⟨∇E(q), dir⟩. -/
theorem smooth_from_lipschitz_gradient {W : Type}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (E : W → ℝ) (dir q : W) (L : ℝ)
    (hdiff : ∀ w : W, HasFDerivAt E (fderiv ℝ E w) w)
    (hsmooth : ∀ x y : W, ‖fderiv ℝ E y - fderiv ℝ E x‖ ≤ L * ‖y - x‖)
    (hgcont : Continuous fun t : ℝ => fderiv ℝ E (q + t • dir) dir) :
    E (q + dir) ≤ E q + fderiv ℝ E q dir
      + L * ‖dir‖ ^ 2 / 2 := by
  -- (1) Newton–Leibniz вдоль сегмента
  have hint := integral_deriv_segment E dir q hdiff hgcont
  -- (2) точечная оценка подынтегральной производной
  have hLx : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
      fderiv ℝ E (q + t • dir) dir
        ≤ fderiv ℝ E q dir + L * t * ‖dir‖^2 := fun t ht =>
    deriv_along_segment_le E dir q L hsmooth t ht.1
  -- (3) монотонность интеграла
  have hc2 : Continuous fun t : ℝ => L * t * ‖dir‖^2 := by fun_prop
  have hmono : ∫ (t : ℝ) in (0:ℝ)..1, fderiv ℝ E (q + t • dir) dir
      ≤ ∫ (t : ℝ) in (0:ℝ)..1,
        (fderiv ℝ E q dir + L * t * ‖dir‖^2) :=
    intervalIntegral.integral_mono_on (by norm_num)
      (hgcont.intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun t : ℝ =>
        fderiv ℝ E q dir + L * t * ‖dir‖^2).intervalIntegrable 0 1)
      (fun t ht => hLx t ht)
  -- (4) интеграл полинома
  have hinteg : ∫ (t : ℝ) in (0:ℝ)..1,
      (fderiv ℝ E q dir + L * t * ‖dir‖^2)
      = fderiv ℝ E q dir + L * ‖dir‖^2 / 2 := by
    have hLx' : ∫ (x : ℝ) in (0:ℝ)..1, L * x
        = L * ∫ (x : ℝ) in (0:ℝ)..1, x := by
      rw [show (fun x : ℝ => L * x) = fun x : ℝ => (L:ℝ) • x from
        by funext x; simp [smul_eq_mul]]
      rw [intervalIntegral.integral_smul]
      rfl
    have hc : Continuous fun x : ℝ => L * x := by fun_prop
    rw [intervalIntegral.integral_add
      (intervalIntegrable_const
        (c := fderiv ℝ E q dir))
      ((by fun_prop : Continuous fun x : ℝ =>
        L * x * ‖dir‖^2).intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const, smul_eq_mul, one_mul,
      sub_zero]
    rw [intervalIntegral.integral_mul_const (‖dir‖^2)
      (fun x => L * x), hLx']
    have hxI : ∫ (x : ℝ) in (0:ℝ)..1, x = 1 / 2 := by
      have h1 : ∫ (x : ℝ) in (0:ℝ)..1, x
          = ∫ (x : ℝ) in (0:ℝ)..1, (1:ℝ) * x := by
        congr 1; funext x; ring
      rw [h1]
      norm_num [intervalIntegral.integral_const_mul]
    rw [hxI]
    ring
  -- (5) сборка
  have hsplit2 : E (q + dir) = E q
    + ∫ (t : ℝ) in (0:ℝ)..1, fderiv ℝ E (q + t • dir) dir := by
    linarith
  rw [hsplit2]
  linarith



/-- МОСТ: эмпирическое условие гладкости h_emp_smooth этапа
Joint ВЫВОДИТСЯ из реального свойства функции потерь
(L-липшицев градиент), а не постулируется:
E(w - η•d) ≤ E(w) - η·DE(w)d + L·η²·‖d‖²/2. -/
theorem joint_emp_smooth_derived {W : Type}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (E : W → ℝ) (w d : W) (L eta : ℝ) (heta : 0 ≤ eta)
    (hdiff : ∀ x : W, HasFDerivAt E (fderiv ℝ E x) x)
    (hsmooth : ∀ x y : W, ‖fderiv ℝ E y - fderiv ℝ E x‖ ≤ L * ‖y - x‖)
    (hgcont : Continuous fun t : ℝ => fderiv ℝ E (w + t • (-(eta)•d)) (-(eta)•d)) :
    E (w - eta•d)
      ≤ E w - eta * (fderiv ℝ E w d) + L * eta ^ 2 * ‖d‖ ^ 2 / 2 := by
  have h := smooth_from_lipschitz_gradient E (-(eta)•d) w L hdiff hsmooth hgcont
  rw [sub_eq_add_neg]
  -- производная по направлению
  have hder : (fderiv ℝ E w) (-(eta)•d) = -(eta * (fderiv ℝ E w d)) := by
    rw [map_smul, neg_smul, smul_eq_mul]
  rw [hder] at h
  -- норма
  have hnorm : ‖-(eta)•d‖ ^ 2 = eta ^ 2 * ‖d‖ ^ 2 := by
    have h1 : (-(eta:ℝ))•d = -(eta•d) := neg_smul eta d
    rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg heta]
    ring
  rw [hnorm] at h
  have hL : w + -eta • d = w + -(eta • d) := by rw [neg_smul]
  rw [hL] at h
  exact le_trans h (le_of_eq (by ring))



/-- МОСТ (compress): изменение энергии при РЕАЛЬНОМ
квантовании gridQ выводится из липшицевости функции
потерь: |E x − E(gridQ Δ x)| ≤ κ·Δ/2. В сочетании с
compress_stage (StageCalculus) это замыкает
h_emp_lip/h_emp_dist этапа сжатия операцией, а не
предпосылкой. -/
theorem compress_energy_bridge (E : ℝ → ℝ) (kappa : ℝ)
    (hkappa : 0 ≤ kappa)
    (hdiff : ∀ x : ℝ, HasFDerivAt E (fderiv ℝ E x) x)
    (hnorm : ∀ x : ℝ, ‖fderiv ℝ E x‖ ≤ kappa)
    (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    |E x - E (Hagi.Energy.gridQ Δ hΔ x)| ≤ kappa * Δ / 2 := by
  have hlip := lip_energy_quantization E kappa hdiff hnorm x
    (Hagi.Energy.gridQ Δ hΔ)
  have hq := Hagi.Energy.gridQ_error Δ hΔ x
  rw [show ((Hagi.Energy.gridQ Δ hΔ x) - x) = -(x - (Hagi.Energy.gridQ Δ hΔ x)) from by ring] at hq
  rw [abs_neg] at hq
  have h1 : kappa * ‖x - Hagi.Energy.gridQ Δ hΔ x‖ ≤ kappa * (Δ / 2) :=
    mul_le_mul_of_nonneg_left hq hkappa
  rw [Real.norm_eq_abs] at h1
  rw [Real.norm_eq_abs] at hlip
  exact le_trans hlip (by linarith)




/-- МОСТ (CorePremises, компонент 8): если энергия после
шага joint определяется РЕАЛЬНОЙ функцией потерь
E(params − η•stepDir) с L-липшицевым градиентом, а
производная по направлению представлена градиентом
состояния, то эмпирическая предпосылка гладкости
CorePremises ВЫВОДИТСЯ из операции + монотонности энергий
стадий (E(params) ≤ mergeEnergy). -/
theorem core_premises_joint_operational
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (E : X → ℝ) (S : Hagi.System.GrowthState X)
    (hdiff : ∀ w : X, HasFDerivAt E (fderiv ℝ E w) w)
    (hsmooth : ∀ x y : X, ‖fderiv ℝ E y - fderiv ℝ E x‖
      ≤ S.sp.L * ‖y - x‖)
    (hgcont : Continuous fun t : ℝ => fderiv ℝ E
      (S.params + t • (-(S.sp.eta)•S.stepDir))
      (-(S.sp.eta)•S.stepDir))
    (hgrad : fderiv ℝ E S.params S.stepDir
      = ⟪S.grad, S.stepDir⟫_ℝ)
    (heta : 0 ≤ S.sp.eta)
    (hE : E S.params ≤ S.effects.mergeEnergy) :
    E (S.params - S.sp.eta • S.stepDir)
      ≤ S.effects.mergeEnergy
        - S.sp.eta * ⟪S.grad, S.stepDir⟫_ℝ
        + S.sp.L * S.sp.eta ^ 2 * ‖S.stepDir‖ ^ 2 / 2 := by
  have h := joint_emp_smooth_derived E S.params S.stepDir
    S.sp.L S.sp.eta heta hdiff hsmooth hgcont
  rw [hgrad] at h
  linarith [h, hE]




/-- МОСТ (CorePremises, компонент 13): граница энергии
сжатия ВЫВОДИТСЯ из реального квантования gridQ:
при compressEnergy = E(gridQ Δ x), jointEnergy ≥ E x,
quantErr = |x − gridQ Δ x| (фактическая ошибка сетки),
s = 1 выполнено compressEnergy − jointEnergy ≤ κ·s·quantErr. -/
theorem core_premises_compress_operational
    (E : ℝ → ℝ) (kappa : ℝ)
    (hdiff : ∀ x : ℝ, HasFDerivAt E (fderiv ℝ E x) x)
    (hnorm : ∀ x : ℝ, ‖fderiv ℝ E x‖ ≤ kappa)
    (Δ : ℝ) (hΔ : 0 < Δ) (x jointEnergy : ℝ)
    (hjoint : E x ≤ jointEnergy) :
    E (Hagi.Energy.gridQ Δ hΔ x) - jointEnergy
      ≤ kappa * 1 * |x - Hagi.Energy.gridQ Δ hΔ x| := by
  have hlip := lip_energy_quantization E kappa hdiff hnorm x
    (Hagi.Energy.gridQ Δ hΔ)
  rw [Real.norm_eq_abs] at hlip
  have hupper : E (Hagi.Energy.gridQ Δ hΔ x) - E x
      ≤ kappa * |x - Hagi.Energy.gridQ Δ hΔ x| := by
    have := abs_sub_le_iff.mp hlip
    linarith [this.2]
  have h' : kappa * 1 * |x - Hagi.Energy.gridQ Δ hΔ x|
      = kappa * |x - Hagi.Energy.gridQ Δ hΔ x| := by ring
  rw [h']
  linarith [hupper, hjoint]

end Hagi.Unified
