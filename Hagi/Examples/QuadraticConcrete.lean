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

open Real InnerProductSpace

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

section Operational

open Hagi.System Hagi.Unified

/-- СОСТОЯНИЕ Concrete-витнеса: квадратичная функция потерь
quadE a, stepDir = 0 (тривиальный шаг), L = 1, kappa = 1+|a|
(на [−1,1]), s = 1, Δ = 1; энергии стадий операционально
согласованы: jointEnergy = E(params−η·d), compressEnergy =
E(gridQ Δ params), quantErr = фактическая ошибка сетки. -/
noncomputable def quadState (a : ℝ) : GrowthState ℝ where
  weightDim := 0
  weights := fun _ => 0
  params := 0
  experts := 0
  energy := quadE a 0
  protectedRisk := 0
  budget := 0
  gap := 0
  dataField := 0
  capability := 0
  verifier := 0
  runtimeError := 0
  stepDir := 0
  grad := -a
  sp := { eta := 1, L := 1, kappa := 1 + |a|, s := 1 }
  effects := {
    growGain := 0
    growCost := 0
    growRisk := 0
    growEnergy := quadE a 0
    mergeRisk := 0
    mergeCost := 0
    mergeEnergy := quadE a 0
    jointEnergy := quadE a (0 - 1 * (0:ℝ))
    jointRisk := 0
    jointCost := 0
    quantErr := |0 - Hagi.Energy.gridQ 1 one_pos 0|
    compressEnergy := quadE a (Hagi.Energy.gridQ 1 one_pos 0)
    compressRisk := 0
    compressCost := 0
  }

/-- fderiv-форма производной для hdiff-посылок. -/
theorem quad_hasFDeriv (a x : ℝ) :
    HasFDerivAt (quadE a) (fderiv ℝ (quadE a) x) x :=
  (quad_hasDeriv a x).differentiableAt.hasFDerivAt

/-- CONJUNCT 8 НА КВАДРАТЕ (теорема): операционная посылка
гладкости выводится для quadState — все гипотезы DerivAlong-
моста суть теоремы (производная, L=1-гладкость,
непрерывность, тождество направленной производной). -/
theorem quad_conj8 (a : ℝ) :
    (quadState a).effects.jointEnergy
      ≤ (quadState a).effects.mergeEnergy
        - (quadState a).sp.eta
          * ⟪(quadState a).grad, (quadState a).stepDir⟫_ℝ
        + (quadState a).sp.L * (quadState a).sp.eta ^ 2
          * ‖(quadState a).stepDir‖ ^ 2 / 2 :=
  conj8_h_emp_smooth_derived (quadE a) (quadState a)
    (quad_hasFDeriv a)
    (fun x y => by
      have h := quad_smooth a x y
      simpa [quadState, mul_one] using h)
    (by simp [quadState]; exact continuous_const)
    (by
      simp only [quad_fderiv_apply, quadState, inner_apply]
      ring)
    (by show (0:ℝ) ≤ 1; norm_num)
    (by rfl)
    (by rfl)

/-- κ-граница в точке 0 (|0| ≤ 1). -/
theorem quad_kappa_at0 (a : ℝ) :
    ‖fderiv ℝ (quadE a) 0‖ ≤ 1 + |a| :=
  quad_kappa_bound a 1 0 (by norm_num) (by norm_num)

/-- CONJUNCT 13 НА КВАДРАТЕ (теорема): точка 0 — узел сетки
(gridQ 1 0 = 0), quantErr = 0, compressEnergy = E(0) =
jointEnergy — посылка сжатия выполняется с нулевым зазором
(прямое вычисление, без глобальной κ-границы). -/
theorem quad_conj13 (a : ℝ) :
    quadE a (Hagi.Energy.gridQ 1 one_pos 0)
      - quadE a (0 - 1 * (0:ℝ))
      ≤ (1 + |a|) * 1 * |0 - Hagi.Energy.gridQ 1 one_pos 0| := by
  have hzero : Hagi.Energy.gridQ 1 one_pos 0 = 0 := by
    simp [Hagi.Energy.gridQ]
  have hstep : (0:ℝ) - 1 * 0 = 0 := by ring
  rw [hzero, hstep]
  norm_num
open Hagi.System Hagi.Unified InnerProductSpace Real

/-- GenState-обёртка квадратичного состояния (нулевой gen). -/
noncomputable def quadGen (a : ℝ) : GenState ℝ where
  toGrowthState := quadState a
  gen := ⟨0, 0, 0, 0, 0⟩

/-- Пост-цикл состояние: точная композиция стадий + gen. -/
noncomputable def quadGen' (a : ℝ) : GenState ℝ where
  toGrowthState := compress (joint (merge (grow (quadState a))))
  gen := ⟨0, 0, 0, 0, 0⟩

/-- ПОЛНЫЙ CONCRETE-ВИТНЕС CorePremises НА КВАДРАТЕ (аудит
v6 §3, завершение Concrete-линии): все 16 конъюнктов —
теоремы (rfl-структурные + quad-леммы) для реальной функции
потерь E = (x−a)²/2. Вместе с MasterHAGICoreOperational:
одностадийный мастер-результат выполняется на квадратичной
функции потерь без единой постулируемой «эмпирической»
посылки. -/
theorem quad_core_premises (a : ℝ) (w : Fin 5 → ℝ) :
    CorePremises (quadGen a) (quadGen' a) 0 w := by
  constructor
  all_goals simp [CorePremises, quadGen, quadGen', quadState,
    Hagi.Energy.gridQ]
  all_goals (try positivity)
  all_goals (try linarith [abs_nonneg a])
end Operational

end Hagi.Examples.Quadratic
