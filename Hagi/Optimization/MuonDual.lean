/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# MuonDual — ортогонализованный шаг максимизирует линейный функционал

Muon (optimal_lm.py, `lr_muon`): шаг по `G (GᵀG)^{-1/2}` — полярному множителю,
вычисляемому Polar Express (`PolarExpressCert`). Матричный смысл: спектральная
норма — двойственная к ядровой, `‖G‖_* = max_{‖U‖≤1} ⟨G, U⟩`, и ортогонализация
даёт максимизатор.

В евклидовом пространстве (скалярный срез каждого сингулярного направления):
* `inner_le_of_norm_le_one` — `⟨g, u⟩ ≤ ‖g‖` при `‖u‖ ≤ 1`;
* `polar_step_attains` — `u = ‖g‖⁻¹ • g` допустим и достигает `‖g‖`;
* `muon_direction_max` — любой допустимый `u` не лучше ортогонализованного.

Матричная (ядровая) норма не формализована — это общий каркас двойственности.
-/

namespace Hagi.Optimization.MuonDual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Двойственность евклидовой нормы: `⟨g, u⟩ ≤ ‖g‖` при `‖u‖ ≤ 1`. -/
theorem inner_le_of_norm_le_one (g u : E) (hu : ‖u‖ ≤ 1) : inner ℝ g u ≤ ‖g‖ := by
  have := real_inner_le_norm g u
  have := this.trans (mul_le_mul_of_nonneg_left hu (norm_nonneg g))
  simpa using this
/-- Ортогонализованный шаг Muon `u = g/‖g‖` — максимизирующий элемент. -/
theorem polar_step_attains (g : E) (hg : g ≠ 0) :
    ‖(‖g‖⁻¹ : ℝ) • g‖ ≤ 1 ∧ inner ℝ g ((‖g‖⁻¹ : ℝ) • g) = ‖g‖ := by
  have hpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hpos.ne']
  · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
/-- Итог: `max_{‖u‖≤1} ⟨g, u⟩ = ‖g‖` — спектральная (ядровая) норма градиента
достигается ортогонализацией; шаг Muon идёт по направлению максимума. -/
theorem muon_direction_max (g : E) (hg : g ≠ 0) (u : E) (hu : ‖u‖ ≤ 1) :
    inner ℝ g u ≤ inner ℝ g ((‖g‖⁻¹ : ℝ) • g) := by
  rw [(polar_step_attains g hg).2]
  exact inner_le_of_norm_le_one g u hu

end Hagi.Optimization.MuonDual
