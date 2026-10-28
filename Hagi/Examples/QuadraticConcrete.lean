import Hagi.Unified.CorePremisesDerived

/-!
# Concrete-слой: квадратичная функция потерь (аудит v6, §3)

«Один содержательный пример: квадратичная функция на ℝ,
где все премисы проверяются теоремами». E(x) = (x−a)²/2:
- производная x−a (теорема quad_hasDeriv);
- L-гладкость с L = 1 (теорема quad_smooth);
- κ-ограниченность градиента на [−R,R] с κ = R+|a|
  (теорема quad_kappa_bound);
- значение fderiv: (x−a)·c (теорема quad_fderiv_apply).
Это заготовка Concrete-слоя: операциональные премисы
аудита v6 (шаг 1) проверяются теоремами для квадратичной
функции потерь.
-/

namespace Hagi.Examples.Quadratic

open Real

/-- Квадратичная функция потерь: E(x) = (x−a)²/2. -/
noncomputable def quadE (a x : ℝ) : ℝ := (x - a) ^ 2 / 2

/-- ПРОИЗВОДНАЯ (теорема): E'(x) = x − a. -/
theorem quad_hasDeriv (a x : ℝ) :
    HasDerivAt (quadE a) (x - a) x := by
  have h1 : HasDerivAt (fun y => y - a) 1 x := by
    simpa using (hasDerivAt_id x).sub_const a
  have h2 := h1.pow 2
  have h3 := h2.div_const (2 : ℝ)
  norm_num at h3
  exact h3

/-- ЗНАЧЕНИЕ fderiv (теорема): (fderiv E x) c = (x−a)·c. -/
theorem quad_fderiv_apply (a x c : ℝ) :
    (fderiv ℝ (quadE a) x) c = (x - a) * c := by
  have hd : HasFDerivAt (quadE a)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (x - a)) x :=
    (quad_hasDeriv a x).hasFDerivAt
  rw [hd.fderiv]
  simp [mul_comm]

/-- L-ГЛАДКОСТЬ (теорема): |E'(y)−E'(x)| ≤ 1·|y−x| (L = 1). -/
theorem quad_smooth (a x y : ℝ) :
    ‖fderiv ℝ (quadE a) y - fderiv ℝ (quadE a) x‖ ≤ 1 * ‖y - x‖ := by
  have h1 : fderiv ℝ (quadE a) y
      = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (y - a) :=
    (quad_hasDeriv a y).hasFDerivAt.fderiv
  have h2 : fderiv ℝ (quadE a) x
      = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (x - a) :=
    (quad_hasDeriv a x).hasFDerivAt.fderiv
  rw [h1, h2]
  have hsub : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (y - a))
      - ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (x - a)
      = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (y - x) := by
    ext c
    simp
  rw [hsub]
  refine ContinuousLinearMap.opNorm_le_bound _
    (by positivity : (0:ℝ) ≤ 1 * |y - x|) ?_
  intro c
  have hval : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (y - x)) c
      = (y - x) * c := by
    simp
    ring
  rw [hval, Real.norm_eq_abs, abs_mul]
  have hle : |y - x| ≤ 1 * |y - x| := by norm_num
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg c)

/-- κ-ОГРАНИЧЕННОСТЬ (теорема): |E'(x)| ≤ R + |a| при |x| ≤ R. -/
theorem quad_kappa_bound (a R x : ℝ) (hR : 0 ≤ R)
    (hx : |x| ≤ R) :
    ‖fderiv ℝ (quadE a) x‖ ≤ R + |a| := by
  have h1 : fderiv ℝ (quadE a) x
      = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (x - a) :=
    (quad_hasDeriv a x).hasFDerivAt.fderiv
  rw [h1]
  refine ContinuousLinearMap.opNorm_le_bound _
    (by positivity : (0:ℝ) ≤ R + |a|) ?_
  intro c
  have hval : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (x - a)) c
      = (x - a) * c := by
    simp
    ring
  rw [hval, Real.norm_eq_abs, abs_mul]
  have h2' : |x - a| ≤ |x| + |a| := abs_sub x a
  have h3' : |x| + |a| ≤ R + |a| := by linarith
  exact mul_le_mul_of_nonneg_right (h2'.trans h3') (abs_nonneg c)

/-- НЕПРЕРЫВНОСТЬ t ↦ fderiv-значения вдоль сегмента (для
hgcont-посылки операциональной схемы). -/
theorem quad_gcont (a p d : ℝ) :
    Continuous (fun t : ℝ =>
      (fderiv ℝ (quadE a) (p + t * d)) d) := by
  have heq : (fun t : ℝ => (fderiv ℝ (quadE a) (p + t * d)) d)
      = fun t => (p + t * d - a) * d := by
    funext t
    exact quad_fderiv_apply a (p + t * d) d
  rw [heq]
  fun_prop

end Hagi.Examples.Quadratic
