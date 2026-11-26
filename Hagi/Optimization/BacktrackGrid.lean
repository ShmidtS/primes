/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Optimization.EF21Quantizer

/-!
# BacktrackGrid — сертификат сетки backtracking в fit_fiber_guarded (optimal_processor.py)

Шаг `x − η g` для L-гладкой функции (`smooth_from_lipschitz_gradient`) даёт
`f(x − ηg) ≤ quadModel f g L η = f − η(1 − Lη/2)‖g‖²`. Сетка кода —
`[1, 1/2, 1/4, 1/10, 3/100]`, принимается первый строго уменьшающий шаг.

* `quadModel_lt` — шаг спуска при `0 < η < 2/L`, `g ≠ 0`.
* `grid_exists_descend` — при `L ≤ 1/η_min` HOLD невозможен: минимальный шаг
  сетки всегда уменьшает, перебор его найдёт.
* `grid_min_drop` — снижение не меньше `η_min/2 · ‖g‖² = 3/200·‖g‖²`.

Честная граница: `L` кодом не измеряется; при `L > 1/η_min` HOLD при `g ≠ 0`
возможен и означает «гладкость выше бюджета сетки».
-/

namespace Hagi.Optimization.BacktrackGrid

/-- Верхняя квадратичная модель шага `x − η g` для L-гладкой функции:
`f − η‖g‖² + L η²‖g‖²/2 = f − η(1 − Lη/2)‖g‖²`. -/
noncomputable def quadModel (f g L η : ℝ) : ℝ := f - η * g ^ 2 + L * η ^ 2 * g ^ 2 / 2
theorem quadModel_eq (f g L η : ℝ) : quadModel f g L η = f - η * (1 - L * η / 2) * g ^ 2 := by
  unfold quadModel; ring
/-- Descent step: при `0 < η < 2/L` и `g ≠ 0` модель строго ниже `f`. -/
theorem quadModel_lt (f g L η : ℝ) (hL : 0 < L) (hη0 : 0 < η) (hη : η < 2 / L) (hg : g ≠ 0) :
    quadModel f g L η < f := by
  rw [quadModel_eq]
  have hpos : 0 < η * (1 - L * η / 2) := by
    have h1 : L * η / 2 < 1 := by
      have := (lt_div_iff₀ hL).1 hη
      nlinarith
    positivity
  have hsq : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  exact sub_lt_self f (mul_pos hpos hsq)
/-- Сетка `fit_fiber_guarded` и её минимальный шаг. -/
noncomputable def grid : List ℝ := [1, 1 / 2, 1 / 4, 1 / 10, 3 / 100]
theorem grid_min : ∀ η ∈ grid, 3 / 100 ≤ η ∧ η ≤ 1 := by
  intro η h
  norm_num [grid] at h
  rcases h with h | h | h | h | h <;> rw [h] <;> norm_num
/-- HOLD невозможен: при `L ≤ 1/η_min` и `g ≠ 0` в сетке есть шаг спуска
(минимальный), поэтому перебор от больших шагов к меньшим найдёт уменьшающий. -/
theorem grid_exists_descend (f g L : ℝ) (hL : 0 < L) (hg : g ≠ 0)
    (hLmax : L ≤ 1 / (3 / 100)) : ∃ η ∈ grid, quadModel f g L η < f := by
  have hLmax' : L * (3 / 100) ≤ 1 := (le_div_iff₀ (by norm_num : (0:ℝ) < 3/100)).1 hLmax
  refine ⟨3 / 100, by norm_num [grid], ?_⟩
  have hη0 : (0:ℝ) < 3 / 100 := by norm_num
  have hηL : L * (3 / 100) < 2 := by linarith
  have hη : (3:ℝ) / 100 < 2 / L := by
    rw [lt_div_iff₀ hL]; nlinarith
  exact quadModel_lt f g L (3 / 100) hL hη0 hη hg
/-- Гарантированное снижение на минимальном шаге сетки: `f − (3/200)‖g‖²`. -/
theorem grid_min_drop (f g L : ℝ) (hL : 0 < L) (hLmax : L ≤ 1 / (3 / 100)) :
    quadModel f g L (3 / 100) ≤ f - (3 / 200) * g ^ 2 := by
  rw [quadModel_eq]
  have hLmax' : L * (3 / 100) ≤ 1 := (le_div_iff₀ (by norm_num : (0:ℝ) < 3/100)).1 hLmax
  have h1 : (1:ℝ) - L * (3 / 100) / 2 ≥ 1 / 2 := by linarith
  have hsq : 0 ≤ g ^ 2 := sq_nonneg g
  nlinarith

end Hagi.Optimization.BacktrackGrid
