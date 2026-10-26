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

end Hagi.Optimization
