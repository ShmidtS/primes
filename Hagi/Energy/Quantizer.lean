/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Order.Round

/-!
# Квантователь (объединённый)

Решётчатый квантователь gridQ с покоординатной оценкой и
векторный контракт gridQVec. Слит из двух модулей; имена
деклараций сохранены.
-/

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


/-- **Оптимальный шаг решётки: Δ* = c.** Компромисс
«точность × объём памяти»: ошибка квантования стоит Δ
(ошибка ≤ Δ/2 на `gridQ`), точность Δ требует ~log(1/Δ) бит
на вес, а хранение/стирание бита стоит c (ландауэровская
цена, см. `landauer_cooling_floor`). Суммарная цена

  `f(Δ) = Δ + c·log(1/Δ)`

минимальна ровно при Δ = c: для любого Δ > 0

  `f(c) ≤ f(Δ)`

(доказано алгебраически из log x ≤ x − 1 без случая-разбора).
Оптимальный шаг квантования пропорционален цене бита:
дорогая память/энергия ⇒ грубее решётка; дешёвая ⇒ точнее.
Это формальный ответ на «максимальное качество при
минимальном объёме»: уровень квантования весов выбирается
равным удельной цене информации. -/
theorem quantizer_optimal_step (c Δ : ℝ) (hc : 0 < c) (hΔ : 0 < Δ) :
    c + c * Real.log (1/c) ≤ Δ + c * Real.log (1/Δ) := by
  have h1 : Real.log (Δ/c) ≤ Δ/c - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : c * Real.log (Δ/c) ≤ Δ - c := by
    have := mul_le_mul_of_nonneg_left h1 hc.le
    field_simp at this
    linarith
  have h3 : Real.log (Δ/c) = Real.log Δ - Real.log c :=
    Real.log_div (hΔ.ne') (hc.ne')
  rw [h3] at h2
  have h4 : Real.log (1/c) = -Real.log c := by
    rw [one_div, Real.log_inv]
  have h5 : Real.log (1/Δ) = -Real.log Δ := by
    rw [one_div, Real.log_inv]
  rw [h4, h5]
  linarith
end Hagi.Energy

/-!
# Векторный контракт квантования: единая решётка

Покоординатная оценка `gridQ_error` и векторная
`quant_residual_norm` соединяются в один исполняемый
контракт: вектор весов, квантованный покоординатно на
решётку с шагом дельта, имеет квадрат евклидовой
невязки не более числа координат на квадрат полушага.
Никаких гипотез за пределами положительности шага.
-/

namespace Hagi.Energy

open Finset

variable {k : Type*} [Fintype k]

/-- Векторный квантователь: покоординатная решётка. -/
noncomputable def gridQVec (Δ : ℝ) (hΔ : 0 < Δ)
    (w : k → ℝ) : k → ℝ :=
  fun i => gridQ Δ hΔ (w i)

omit [Fintype k] in
/-- Покоординатная невязка в пределах полушага. -/
theorem gridQVec_error (Δ : ℝ) (hΔ : 0 < Δ)
    (w : k → ℝ) (i : k) :
    |w i - gridQVec Δ hΔ w i| ≤ Δ / 2 := by
  have h := gridQ_error Δ hΔ (w i)
  rw [abs_sub_comm]
  exact h

/-- ГЛАВНЫЙ КОНТРАКТ: квадрат евклидовой невязки
векторного квантования не превосходит количества
координат на квадрат полушага — без единой эмпирической
предпосылки. -/
theorem gridQVec_norm_sq (Δ : ℝ) (hΔ : 0 < Δ)
    (w : k → ℝ) :
    (∑ i, (w i - gridQVec Δ hΔ w i) ^ 2)
      ≤ (Fintype.card k : ℝ) * (Δ / 2) ^ 2 := by
  have hres : ∀ i : k, |w i - gridQVec Δ hΔ w i| ≤ Δ / 2 :=
    fun i => gridQVec_error Δ hΔ w i
  have hn : (Fintype.card k : ℝ) = (Fintype.card k : ℝ) := rfl
  -- сводим к Fin-форме quant_residual_norm через произвольный Fintype
  calc (∑ i, (w i - gridQVec Δ hΔ w i) ^ 2)
      ≤ ∑ i, (Δ / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          have hle := hres i
          rw [abs_le] at hle
          nlinarith [hle.1, hle.2]
    _ = (Fintype.card k : ℝ) * (Δ / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Hagi.Energy
