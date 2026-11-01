import Mathlib

/-!
# Двухстадийное иерархическое чанкование

Иерархическая сеть с двумя уровнями динамической
компрессии: внешняя стадия сжимает поток в первом
коэффициенте, внутренняя — во втором. Главная сеть видит
позиции, сжатые в ПРОИЗВЕДЕНИЕ коэффициентов; полная
компрессия мультипликативна по стадиям.
-/

namespace Hagi.Model.HNet2

/-- Число позиций главной сети после двух стадий
чанкования. -/
noncomputable def hier2Positions (T r1 r2 : ℝ) : ℝ :=
  T / (r1 * r2)

/-- Вспомогательный закон: деление на коэффициент,
не меньший единицы, не увеличивает неотрицательную
величину. -/
theorem div_le_of_one_le (x c : ℝ) (hx : 0 ≤ x) (hc : 1 ≤ c) :
    x / c ≤ x := by
  have hc' : (0:ℝ) < c := by linarith
  have hprod : (0:ℝ) ≤ x * (c - 1) :=
    mul_nonneg hx (by linarith)
  rw [div_le_iff₀ hc']
  nlinarith

/-- ПОЛНАЯ КОМПРЕССИЯ МУЛЬТИПЛИКАТИВНА: две стадии с
коэффициентами дают то же сжатие, что одна стадия с их
произведением. -/
theorem hier2_compression_product (T r1 r2 : ℝ)
    (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) :
    hier2Positions T r1 r2 = T / r1 / r2 := by
  unfold hier2Positions
  field_simp

/-- Стадии только сжимают: при коэффициентах,
не меньших единицы, поток позиций главной сети не длиннее
исходного. -/
theorem hier2_positions_le (T r1 r2 : ℝ)
    (hT : 0 ≤ T) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2) :
    hier2Positions T r1 r2 ≤ T := by
  have h12 : (1:ℝ) ≤ r1 * r2 := by
    have := mul_le_mul hr1 hr2 (by linarith) (by linarith)
    linarith [this]
  exact div_le_of_one_le T (r1 * r2) hT h12

/-- Стоимость двухстадийной иерархии: внешние стадии
платят по потоку до и после первого сжатия, главная сеть —
по квадрату сжатой длины. -/
noncomputable def hier2Cost (c1 c2 cm T r1 r2 : ℝ) : ℝ :=
  c1 * T + c2 * T / r1 + cm * (hier2Positions T r1 r2)^2

/-- Dense-базлайн: главная сеть по всей длине. -/
noncomputable def denseCost (cm T : ℝ) : ℝ := cm * T^2

/-- УСЛОВИЕ ВЫИГРЫША: если сжатая главная сеть с накладными
расходами внешних стадий строго дешевле dense-эталона при
ЛИНЕЙНОЙ цене главной стадии, то двухстадийная иерархия
строго дешевле и при квадратичной цене (квадрат сжатой
длины не дороже самой сжатой длины при достаточной
компрессии). -/
theorem hier2_beats_dense (c1 c2 cm T r1 r2 : ℝ)
    (hcm : 0 ≤ cm) (hT : 0 ≤ T)
    (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2)
    (hmain : cm * (T^2 / (r1 * r2)) + c1 * T + c2 * T / r1
      < cm * T^2) :
    hier2Cost c1 c2 cm T r1 r2 < denseCost cm T := by
  have h12 : (1:ℝ) ≤ r1 * r2 := by
    have := mul_le_mul hr1 hr2 (by linarith) (by linarith)
    linarith [this]
  have h12pos : (0:ℝ) < r1 * r2 := by positivity
  have hquad : T^2 / (r1 * r2)^2 ≤ T^2 / (r1 * r2) := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (r1 * r2)^2)
      h12pos]
    have hprod : (0:ℝ) ≤ T^2 * ((r1 * r2) - 1) :=
      mul_nonneg (by positivity) (by linarith)
    have hsplit : T^2 * ((r1 * r2) - 1) = T^2 * (r1 * r2) - T^2 := by
      ring
    nlinarith
  have key : cm * (hier2Positions T r1 r2)^2
      ≤ cm * (T^2 / (r1 * r2)) := by
    unfold hier2Positions
    rw [div_pow]
    exact mul_le_mul_of_nonneg_left hquad hcm
  unfold hier2Cost denseCost
  linarith

end Hagi.Model.HNet2
