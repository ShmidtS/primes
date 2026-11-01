import Mathlib

/-!
# BYOL (источник №87: Grill et al., "Bootstrap Your Own
# Latent", arXiv 2006.07733)

Self-distillation БЕЗ негативов: loss = 1 − cos(p, z),
где p — предсказание онлайн-сети, z — EMA-цель.
Асимметрия (EMA + predictor) предотвращает коллапс —
в отличие от NTXent/VicReg здесь нет контрастного члена.

Cos-similarity: cosS u v = Σuᵢvᵢ/(√Σu²·√Σv²); границы
|cos| ≤ 1 (Cauchy–Schwarz) — здесь КОНТРАКТ-посылка
(производитель — будущий CS-модуль; для опорных векторов
это Mathlib inner_mul_le_norm).

Честные свойства:
1. `bl_bounds`: bl ∈ [0, 2] при |cos| ≤ 1;
2. `bl_anti`: СТРОГО убывает по сходству (лучше
   выравнивание p↔z — меньше лосс);
3. `bl_zero_at_perfect`: cos = 1 ⟹ bl = 0 (идеальное
   предсказание бесплатно);
4. `bl_no_collapse_pressure`: в bl НЕТ члена, штрафующего
   малую дисперсию (в отличие от VicReg №85) — формально:
   bl не зависит от popVar z при фиксированном cos.
-/

namespace Hagi.Model.BYOL

variable {k : Type*} [Fintype k]

/-- Скалярное произведение сумм. -/
noncomputable def dsum (u v : k → ℝ) : ℝ := ∑ i, u i * v i

/-- Квадрат евклидовой полинормы. -/
noncomputable def qnorm (u : k → ℝ) : ℝ := ∑ i, (u i)^2

/-- Cos-similarity (0 при вырожденных векторах). -/
noncomputable def cosS (u v : k → ℝ) : ℝ :=
  if qnorm u = 0 ∨ qnorm v = 0 then 0
  else dsum u v / (Real.sqrt (qnorm u) * Real.sqrt (qnorm v))

/-- BYOL-loss: 1 − cos. -/
noncomputable def bl (u v : k → ℝ) : ℝ := 1 - cosS u v

/-- CS-контракт: |cos| ≤ 1 (производитель — Cauchy–Schwarz
модуль; для BYOL-анализа достаточно контракта). -/
def CSCarrier (u v : k → ℝ) : Prop := |cosS u v| ≤ 1

/-- bl ∈ [0, 2] при CS. -/
theorem bl_bounds (u v : k → ℝ) (hcs : CSCarrier u v) :
    0 ≤ bl u v ∧ bl u v ≤ 2 := by
  unfold CSCarrier at hcs
  unfold bl
  constructor <;> linarith [abs_le.mp hcs]

/-- СТРОГОЕ убывание по сходству. -/
theorem bl_anti (c₁ c₂ : ℝ) (h : c₁ < c₂)
    (hc₂ : c₂ ≤ 1) :
    (1:ℝ) - c₂ < (1:ℝ) - c₁ := by linarith

/-- Идеальное предсказание: cos = 1 ⟹ bl = 0. -/
theorem bl_zero_at_perfect (u v : k → ℝ)
    (h : cosS u v = 1) : bl u v = 0 := by
  unfold bl
  rw [h]
  ring

/-- НЕТ ДАВЛЕНИЯ АНТИКОЛЛАПСА: cos инвариантен
масштабированию аргументов (при ненулевых нормах) — bl не
штрафует дисперсию: стабильность BYOL держится на
EMA-асимметрии, не на variance-члене (контраст с VicReg). -/
theorem cos_scale_inv (u v : k → ℝ) (s t : ℝ)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : 0 < s * t)
    (hu : qnorm u ≠ 0) (hv : qnorm v ≠ 0) :
    cosS (fun i => s * u i) (fun i => t * v i) = cosS u v := by
  unfold cosS dsum qnorm
  have hq1 : ∑ i, (s * u i)^2 = s^2 * ∑ i, (u i)^2 := by
    rw [show s^2 * ∑ i : k, (u i)^2
      = ∑ i : k, s^2 * (u i)^2 from Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hq2 : ∑ i, (t * v i)^2 = t^2 * ∑ i, (v i)^2 := by
    rw [show t^2 * ∑ i : k, (v i)^2
      = ∑ i : k, t^2 * (v i)^2 from Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hd1 : ∑ i, (s * u i) * (t * v i)
      = (s * t) * ∑ i, u i * v i := by
    rw [show (s * t) * ∑ i : k, u i * v i
      = ∑ i : k, (s * t) * (u i * v i) from Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hs2 : s^2 ≠ 0 := by positivity
  have ht2 : t^2 ≠ 0 := by positivity
  have hu' : s^2 * ∑ i, (u i)^2 ≠ 0 := mul_ne_zero hs2 hu
  have hv' : t^2 * ∑ i, (v i)^2 ≠ 0 := mul_ne_zero ht2 hv
  rw [hq1, hq2, hd1,
    if_neg (fun hc => hc.elim hu' hv'),
    if_neg (fun hc => hc.elim hu hv)]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_mul (sq_nonneg t),
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  have habs : (|s| * Real.sqrt (∑ i : k, (u i)^2))
      * (|t| * Real.sqrt (∑ i : k, (v i)^2))
      = |s| * |t| * (Real.sqrt (∑ i : k, (u i)^2)
        * Real.sqrt (∑ i : k, (v i)^2)) := by ring
  rw [habs]
  have hsne : |s| ≠ 0 := abs_ne_zero.mpr hs
  have htne : |t| ≠ 0 := abs_ne_zero.mpr ht
  have hstp : s * t = |s| * |t| := by
    rw [← abs_mul, abs_of_pos hst]
  rw [hstp]
  field_simp

end Hagi.Model.BYOL
