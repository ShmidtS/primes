/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

set_option linter.style.header false

/-!
# CriticalBatch — критический размер батча (SFO-оптимум)

Формализация Proposition 4.2 из «Convergence Bound and
Critical Batch Size of Muon Optimizer» (arXiv:2507.01598,
Sato): если граница сходимости имеет форму X/T + Y/√b + Z
(статистический член убывает как 1/√b), то SFO-сложность
T_b·b = X·b^{3/2}/((ε−Z)√b − Y) имеет ГЛОБАЛЬНЫЙ минимум при
√b* = 3Y/(2(ε−Z)), т.е. b* = 9Y²/(4(ε−Z)²) > 9Y²/(4ε²) —
оптимальный батч растёт квадратично по шумовому члену и
обратно квадратично по точности.

Ядро доказательства — чистая полиномиальная идентичность
(AM-GM-форма): 4(t+Y)³ = 27Y²t + (2t−Y)²(t+4Y) — минимум
(t+Y)³/t по t>0 достигается при t = Y/2; ноль производных не
нужен, всё — кольцевая арифметика и монотонность деления.

Доказано:
* `sfo_min_core`: 27XY²/(4c³) ≤ X(t+Y)³/(c³t) для всех
  t > 0, X ≥ 0, c > 0, Y ≥ 0 (глобальная нижняя граница
  SFO-стоимости в t-координате);
* `sfo_global_min`: s* = 3Y/(2c) — глобальный минимум
  SFO-стоимости X·s³/(cs−Y) на области s > Y/c;
* `critical_batch_lower`: b* = s*² и при c < ε выполняется
  9Y²/(4ε²) < b* — порог плана (§2) — нижняя граница
  критического батча.

Честная граница: X, Y, Z, ε — параметры границы сходимости
(измеряемые контракты Muon-теории); доказана арифметика
оптимума, не сама граница сходимости.
-/

open Real

namespace Hagi.CriticalBatch

/-- SFO-сложность как функция s = √b:
X·s³/(c·s − Y), где c = ε − Z. -/
noncomputable def sfoCost (X c Y s : ℝ) : ℝ :=
  X * s ^ 3 / (c * s - Y)

/-- Критическая точка s* = 3Y/(2c). -/
noncomputable def criticalS (c Y : ℝ) : ℝ := 3 * Y / (2 * c)

/-- Ядро минимума (AM-GM-идентичность): глобальная нижняя
граница (t+Y)³/t по t > 0 равна 27Y²/4 при t = Y/2. -/
theorem sfo_min_core (X c t Y : ℝ) (hX : 0 ≤ X) (hc : 0 < c)
    (ht : 0 < t) (hY : 0 ≤ Y) :
    X * 27 * Y ^ 2 / (4 * c ^ 3)
      ≤ X * (t + Y) ^ 3 / (c ^ 3 * t) := by
  have hkey : 27 * Y ^ 2 * t
      ≤ 4 * (t + Y) ^ 3 := by
    have h2 : 4 * (t + Y) ^ 3
        = 27 * Y ^ 2 * t + (2 * t - Y) ^ 2 * (t + 4 * Y) := by
      ring
    have h3 : 0 ≤ (2 * t - Y) ^ 2 * (t + 4 * Y) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  calc X * 27 * Y ^ 2 / (4 * c ^ 3)
      = X * (27 * Y ^ 2 * t) / (4 * (c ^ 3 * t)) := by
        field_simp
    _ ≤ X * (4 * (t + Y) ^ 3) / (4 * (c ^ 3 * t)) :=
        (div_le_div_iff_of_pos_right (by positivity)).mpr
          (mul_le_mul_of_nonneg_left hkey hX)
    _ = X * (t + Y) ^ 3 / (c ^ 3 * t) := by
        field_simp

/-- Глобальный минимум: при X ≥ 0, c > 0, Y ≥ 0 точка
s* = 3Y/(2c) минимизирует SFO-стоимость на всей области
s > Y/c (подстановка t = c·s − Y > 0 сводит к sfo_min_core
при t* = Y/2). -/
theorem sfo_global_min (X c Y s : ℝ) (hX : 0 ≤ X) (hc : 0 < c)
    (hY : 0 ≤ Y) (hs : Y / c < s) :
    sfoCost X c Y (criticalS c Y) ≤ sfoCost X c Y s := by
  have hlt : Y < c * s := by
    have := (div_lt_iff₀ hc).mp hs
    linarith
  have htpos : 0 < c * s - Y := by linarith
  have hsc : s = ((c * s - Y) + Y) / c := by
    field_simp
    ring
  have hcs : criticalS c Y = (Y / 2 + Y) / c := by
    unfold criticalS
    field_simp
    ring
  have hcostL : sfoCost X c Y (criticalS c Y)
      = X * 27 * Y ^ 2 / (4 * c ^ 3) := by
    rw [hcs]
    unfold sfoCost
    field_simp
    ring
  have hcostR : sfoCost X c Y s
      = X * ((c * s - Y) + Y) ^ 3 / (c ^ 3 * (c * s - Y)) := by
    rw [hsc]
    unfold sfoCost
    field_simp
    ring
  rw [hcostL, hcostR]
  exact sfo_min_core X c (c * s - Y) Y hX hc htpos hY

/-- Критический батч: при c = ε − Z < ε порог плана
9Y²/(4ε²) строго ниже b* = (3Y/(2c))². -/
theorem critical_batch_lower (Y ε Z : ℝ) (hY : 0 < Y)
    (hZpos : 0 < Z) (hZ : Z < ε) (hε : 0 < ε) :
    9 * Y ^ 2 / (4 * ε ^ 2)
      < (criticalS (ε - Z) Y) ^ 2 := by
  have hc : 0 < ε - Z := by linarith
  have hsq : (ε - Z) ^ 2 < ε ^ 2 := by
    nlinarith [mul_pos hZpos (by linarith : (0:ℝ) < 2 * ε - Z)]
  unfold criticalS
  rw [div_pow]
  have hcross : 9 * Y ^ 2 * (2 * (ε - Z)) ^ 2
      < (3 * Y) ^ 2 * (4 * ε ^ 2) := by
    have h36 : (0:ℝ) < 36 * Y ^ 2 := by positivity
    have h2 := mul_lt_mul_of_pos_left hsq h36
    nlinarith [h2]
  exact (div_lt_div_iff₀
    (show (0:ℝ) < 4 * ε ^ 2 by positivity)
    (show (0:ℝ) < (2 * (ε - Z)) ^ 2 by positivity)).mpr
      hcross

end Hagi.CriticalBatch
