import Hagi.Energy.Cooling

/-!
# ComputeScaling — compute-optimal нижняя граница потерь

Формализация следствия инфо-теор. scaling laws
(Jeon–Van Roy, arXiv 2407.01456): при потерях a/m + b/n и
линейной стоимости C = m+n — L ≥ (√a+√b)²/C для любой
аллокации бюджета между моделью и данными.
-/

namespace Hagi.Optimization

/-- COMPUTE-OPTIMAL НИЖНЯЯ ГРАНИЦА (инфо-теор. scaling laws,
Jeon–Van Roy arXiv 2407.01456): при потерях L(m,n) = a/m + b/n
(модель m, данные n) и линейной стоимости вычислений
C = m+n — для ЛЮБОЙ аллокации
L ≥ (√a + √b)² / C:
суммарный бюджет ограничивает потери снизу; равенство
достигается только при n·√a = m·√b (линейная
data/model-пропорция — вывод Jeon–Van Roy). -/
theorem compute_scaling_lower_bound (a b m n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hn : 0 < n) :
    (Real.sqrt a + Real.sqrt b) ^ 2 / (m + n) ≤ a / m + b / n := by
  set X := Real.sqrt a with hX
  set Y := Real.sqrt b with hY
  have e1 : X * X = a := by rw [hX]; exact Real.mul_self_sqrt (le_of_lt ha)
  have e2 : Y * Y = b := by rw [hY]; exact Real.mul_self_sqrt (le_of_lt hb)
  have hmn : (0:ℝ) < m + n := by linarith
  have key : (n * X - m * Y) ^ 2 ≥ 0 := sq_nonneg _
  rw [div_add_div _ _ hm.ne' hn.ne',
    div_le_div_iff₀ hmn (by positivity : (0:ℝ) < m * n)]
  have hex : (a * n + m * b) * (m + n)
      = (X + Y) ^ 2 * (m * n) + (n * X - m * Y) ^ 2 := by
    rw [← e1, ← e2]
    ring
  linarith [hex, key]

/-- ДОСТИЖИМОСТЬ ГРАНИЦЫ (Jeon–Van Roy): аллокация
m = √a·s, n = √b·s (линейная data/model-пропорция m/n = √a/√b)
ДОСТИГАЕТ нижней границы compute_scaling_lower_bound:
L = (√a+√b)²/(m+n) — граница точная, оптимум вычислений. -/
theorem compute_scaling_bound_attained (a b s : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) :
    (Real.sqrt a + Real.sqrt b) ^ 2
      / (Real.sqrt a * s + Real.sqrt b * s)
      = a / (Real.sqrt a * s) + b / (Real.sqrt b * s) := by
  set X := Real.sqrt a with hX
  set Y := Real.sqrt b with hY
  have e1 : X * X = a := by rw [hX]; exact Real.mul_self_sqrt (le_of_lt ha)
  have e2 : Y * Y = b := by rw [hY]; exact Real.mul_self_sqrt (le_of_lt hb)
  have hXs : (0:ℝ) < X * s := by
    have : (0:ℝ) < X := Real.sqrt_pos.mpr ha
    positivity
  have hYs : (0:ℝ) < Y * s := by
    have : (0:ℝ) < Y := Real.sqrt_pos.mpr hb
    positivity
  have hXY : (0:ℝ) < X + Y := by
    have : (0:ℝ) < X := Real.sqrt_pos.mpr ha
    have : (0:ℝ) < Y := Real.sqrt_pos.mpr hb
    linarith
  have keyL : (X + Y) ^ 2 / (X * s + Y * s) = (X + Y) / s := by
    have hfac : X * s + Y * s = (X + Y) * s := by ring
    rw [hfac]
    field_simp
  have keyR : a / (X * s) + b / (Y * s) = (X + Y) / s := by
    rw [← e1, ← e2]
    have h1 : X * X / (X * s) = X / s := by field_simp
    have h2 : Y * Y / (Y * s) = Y / s := by field_simp
    rw [h1, h2]
    ring
  rw [keyL, keyR]

end Hagi.Optimization
