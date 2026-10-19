/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.Round

set_option linter.style.header false

/-!
# Energy.Quantizer — единый оператор решётки `Q_Δ`

Канонический объект «квантователь шага `Δ`»: ближайший узел
решётки `Δℤ`, `gridQ Δ x = Δ * round (x / Δ)`. Одна формула
заменяет точечные варианты округления (ternary, half, clamp):
ошибка `≤ Δ / 2` равномерно по `x`, оператор идемпотентен,
его образ — в точности решётка `Δℤ`.
-/

namespace Hagi.Energy

/-- **Квантователь решётки `Δℤ`**: ближайший узел решётки
к действительному `x`. Условие `0 < Δ` фиксирует шаг сетки.
Это единый оператор квантования проекта: тернарное
округление, half-округление и клэмп скалярных модулей —
частные настройки шага и диапазона этого отображения. -/
noncomputable def gridQ (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) : ℝ :=
  Δ * (round (x / Δ) : ℝ)

/-- **Ошибка квантования** (равномерная): расстояние до
ближайшего узла решётки не превышает полушага `Δ / 2`.
Обобщает `roundHalf_error` и `roundTern_error_scaled`
на произвольный шаг без ограничений на `x`. -/
theorem gridQ_error (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    |gridQ Δ hΔ x - x| ≤ Δ / 2 := by
  have hsplit : gridQ Δ hΔ x - x = Δ * ((round (x / Δ) : ℝ) - x / Δ) := by
    unfold gridQ
    field_simp
  rw [hsplit, abs_mul, abs_of_pos hΔ]
  have hy : |(round (x / Δ) : ℝ) - x / Δ| ≤ 1 / 2 := by
    rw [abs_sub_comm, abs_sub_round_eq_min]
    rcases le_total (Int.fract (x / Δ)) (1 - Int.fract (x / Δ)) with h | h
    · rw [min_eq_left h]
      linarith [Int.fract_nonneg (x / Δ)]
    · rw [min_eq_right h]
      linarith
  nlinarith [hy, hΔ]

/-- **Образ — решётка**: результат квантования всегда равен
`Δ * n` с целым `n` (узел решётки шага `Δ`). -/
theorem gridQ_mem_grid (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    ∃ n : ℤ, gridQ Δ hΔ x = Δ * (n : ℝ) :=
  ⟨round (x / Δ), rfl⟩

/-- **Нормировка**: деление результата на шаг возвращает
целый индекс узла. -/
theorem gridQ_div (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    gridQ Δ hΔ x / Δ = (round (x / Δ) : ℝ) := by
  unfold gridQ
  field_simp

/-- **Идемпотентность**: повторное квантование не меняет
узел решётки — `gridQ` является ретракцией `ℝ → Δℤ`. -/
theorem gridQ_idem (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    gridQ Δ hΔ (gridQ Δ hΔ x) = gridQ Δ hΔ x := by
  have h2 : (Δ * ((round (x / Δ) : ℤ) : ℝ)) / Δ
      = ((round (x / Δ) : ℤ) : ℝ) := by
    field_simp
  unfold gridQ
  rw [h2, round_intCast]

end Hagi.Energy
