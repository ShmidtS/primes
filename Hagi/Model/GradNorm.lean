import Mathlib

/-!
# GradNorm (источник №89: Chen et al., arXiv 1710.04057)

Балансировка мультитаск-лосса: веса задач wᵢ подстраиваются
обратно пропорционально нормам градиентов — выравнивание
«силы» задач предотвращает доминирование одной.

Честные свойства (скалярные нормы ‖gᵢ‖):
1. `gnWeight`: канонический вес wᵢ = c/‖gᵢ‖ (c > 0);
2. `gnBalanced`: взвешенная норма wᵢ·‖gᵢ‖ = c — ВСЕ задачи
   тянут с равной силой (точно, при ‖gᵢ‖ ≠ 0);
3. `gnPos`: веса положительны;
4. `gnInverse`: больший градиент — МЕНЬШЕ вес (обратная
   пропорциональность: анти-доминирование).
-/

namespace Hagi.Model.GradNorm

variable {k : Type*} [Fintype k]

/-- Канонический GradNorm-вес: c / ‖gᵢ‖. -/
noncomputable def gnWeight (c gnorm : ℝ) : ℝ := c / gnorm

/-- ВЗВЕШЕННАЯ НОРМА ТОЧНО РАВНА c: баланс сил задач. -/
theorem gnBalanced (c gnorm : ℝ) (hgn : gnorm ≠ 0) :
    gnWeight c gnorm * gnorm = c := by
  unfold gnWeight
  field_simp

/-- Веса положительны при c > 0, ‖g‖ > 0. -/
theorem gnPos (c gnorm : ℝ) (hc : 0 < c) (hgn : 0 < gnorm) :
    0 < gnWeight c gnorm := by
  unfold gnWeight
  exact div_pos hc hgn

/-- ОБРАТНАЯ ПРОПОРЦИОНАЛЬНОСТЬ: больший градиент —
меньше вес (анти-доминирование сильной задачи). -/
theorem gnInverse (c g₁ g₂ : ℝ) (hc : 0 < c)
    (h₁ : 0 < g₁) (h₂ : 0 < g₂) (h : g₁ < g₂) :
    gnWeight c g₂ < gnWeight c g₁ := by
  unfold gnWeight
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < g₂), mul_comm,
    ← mul_div_assoc, lt_div_iff₀ (by positivity : (0:ℝ) < g₁)]
  nlinarith

end Hagi.Model.GradNorm
