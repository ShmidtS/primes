import Mathlib
import Hagi.Probability.NoiseTemperature

/-!
# GradCentralization (источник №86: Yang et al.,
# "Gradient Centralization", arXiv 2004.02861)

Центрирование градиента: g' = g − mean(g)·1 перед шагом —
проекция на гиперплоскость нулевого среднего.

Честные свойства (реюз centered/sum_centered из
NoiseTemperature):
1. `gc_zero_sum`: Σ g'ᵢ = 0 (компонента среднего удалена
   точно — реюз sum_centered);
2. `gc_pythagoras`: ТОЧНОЕ разложение Пифагора
   ‖g‖² = ‖g'‖² + n·μ² (ортопроекция);
3. `gc_norm_le`: ‖g'‖ ≤ ‖g‖ (центрирование НЕ увеличивает
   норму градиента — шаг не разрастается);
4. `gc_const_zero`: константный градиент центрируется в
   ноль (бесполезная общая компонента отбрасывается).
-/

namespace Hagi.Step.GradCentralization

open Hagi.Probability

variable {V : Type} [Fintype V] [Nonempty V]

/-- Центрированный градиент (реюз centered). -/
noncomputable def gc (g : V → ℝ) : V → ℝ := centered g

/-- Сумма центрированного — ноль (реюз sum_centered). -/
theorem gc_zero_sum (g : V → ℝ) : ∑ v, gc (V := V) g v = 0 :=
  sum_centered g

/-- ПИФАГОР (точный): норма квадрата раскладывается на
центрированную часть + компоненту среднего. -/
theorem gc_pythagoras (g : V → ℝ) :
    (∑ v, (g v)^2)
      = (∑ v, (gc g v)^2)
        + (Fintype.card V : ℝ) * (popMean (V := V) g)^2 := by
  have hkey : ∀ v : V, (g v)^2
      = ((g v - popMean (V := V) g)^2
          + 2 * (g v - popMean (V := V) g) * popMean (V := V) g)
        + (popMean (V := V) g)^2 := fun v => by ring
  have hc : gc g = fun v => g v - popMean (V := V) g := rfl
  rw [hc]
  rw [Finset.sum_congr rfl (fun v _ => hkey v),
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have hsc : ∑ x, (g x - popMean (V := V) g) = 0 := sum_centered g
  have hterm : ∑ x, 2 * (popMean (V := V) g * (g x - popMean (V := V) g)) = 0 := by
    have h1 : ∀ x : V, 2 * (popMean (V := V) g * (g x - popMean (V := V) g))
        = (2 * popMean (V := V) g) * (g x - popMean (V := V) g) := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum, hsc]
    ring
  rw [hterm, add_zero]
  have hconst : ∑ v : V, (popMean (V := V) g)^2
      = (Fintype.card V : ℝ) * (popMean (V := V) g)^2 := by
    simp
  rw [hconst]

/-- Центрирование НЕ увеличивает норму. -/
theorem gc_norm_le (g : V → ℝ) :
    (∑ v, (gc (V := V) g v)^2) ≤ (∑ v, (g v)^2) := by
  have hpy := gc_pythagoras g
  have hnn : (0:ℝ) ≤ (Fintype.card V : ℝ) * (popMean (V := V) g)^2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-- Константный градиент центрируется в ноль. -/
theorem gc_const_zero (c : ℝ) :
    gc (fun _ => c : V → ℝ) = 0 := by
  have hmean : popMean (fun _ => c : V → ℝ) = c := by
    unfold popMean
    rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul, mul_div_cancel_left₀]
  funext v
  unfold gc centered
  simp [hmean]

end Hagi.Step.GradCentralization
