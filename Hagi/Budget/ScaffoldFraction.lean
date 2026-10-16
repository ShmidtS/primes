/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib
import Hagi.Budget.FactorizedBPW
set_option linter.style.header false

/-!
# Доля каркаса vs эффективная размерность (R526)

Количественный мост «1,5% каркаса ⟺ d_eff ~ 5-6»:
факториальная таблица 4!..8!, доля фазового объёма
на направление 1/k! и её монотонность по d_eff.
Точечные значения: 1/5! ≈ 0.83% < 1,5%; 1/6! ≈ 0.14%.
Связь с FactorizedBPW (d_eff ≤ 8) и ThermoPrune.
-/

namespace Hagi.Budget

open Real Finset Nat

/-- Факториальная таблица (точные значения):
4! = 24, 5! = 120, 6! = 720, 7! = 5040, 8! = 40320. -/
theorem fact4 : (4 : ℕ).factorial = 24 := by norm_num
theorem fact5 : (5 : ℕ).factorial = 120 := by norm_num
theorem fact6 : (6 : ℕ).factorial = 720 := by norm_num
theorem fact7 : (7 : ℕ).factorial = 5040 := by norm_num
theorem fact8 : (8 : ℕ).factorial = 40320 := by norm_num

/-- Обратные доли как Real: 1/5! = 1/120 ≈ 0.0083 < 0.015 (1,5%). -/
theorem inv_fact5_lt_15pct : (1:ℝ) / ((5:ℕ).factorial : ℝ) < 3/200 := by
  norm_num

/-- 1/6! = 1/720 ≈ 0.0014 < 0.015. -/
theorem inv_fact6_lt_15pct : (1:ℝ) / ((6:ℕ).factorial : ℝ) < 3/200 := by
  norm_num

/-- **Главный мост R526**: уже при d_eff = 5 доля фонового
объёма 1/5! = 1/120 ≈ 0.83% меньше 1,5% — каркас «1,5%»
достижим пятью эффективными направлениями. -/
theorem scaffold_15pct_at_deff5 : (1:ℝ) / ((5:ℕ).factorial : ℝ) ≤ 0.015 := by
  rw [show (0.015:ℝ) = 3/200 from by norm_num]
  norm_num

/-- Монотонность падения доли по d_eff: 1/(k+1)! ≤ 1/k!. -/
theorem inv_fact_mono (k : ℕ) :
    (1:ℝ) / (((k+1 : ℕ).factorial : ℝ)) ≤ (1:ℝ) / (k.factorial : ℝ) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : (k+1 : ℕ).factorial = (k+1 : ℕ) * k.factorial := Nat.factorial_succ k
  rw [h]
  push_cast
  nlinarith [Nat.factorial_pos k]

end Hagi.Budget
