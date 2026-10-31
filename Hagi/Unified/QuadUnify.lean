import Mathlib
import Hagi.Unified.DescentCoreQuad
import Hagi.Model.ReferenceMachine

/-!
# QuadUnify (такт №277, аудит №5 P3): сведение квадратичных
линий — DescentCoreQuad и ReferenceMachine суть ОДНА
математика.

Оба модуля определяют E(w) = ½Σ(wᵢ−aᵢ)² независимо:
- DescentCoreQuad.quadE (инстанс Objective-контракта);
- Hagi.Model.ReferenceMachine.energy (вычислительная машина).
Здесь доказана их ИДЕНТИЧНОСТЬ (rfl-эквивалентность форм),
а также градиентов. Следствие: сертификаты машины
(QuadGate/QuadTrajectory/QuadBudget) и контрактные гарантии
(DescentCore.descent_drop) говорят об ОДНОЙ величине —
консолидация вместо параллельных дублирующихся теорий.
-/

namespace Hagi.Unified.QuadUnify

open Hagi.Unified.DescentCoreQuad Hagi.Model.ReferenceMachine

variable {n : ℕ}

/-- Формы совпадают точно: quadE = energy. -/
theorem quadE_eq_energy (a w : Fin n → ℝ) :
    DescentCoreQuad.quadE a w = Hagi.Model.ReferenceMachine.energy a w := by
  unfold DescentCoreQuad.quadE Hagi.Model.ReferenceMachine.energy
  rw [Finset.sum_div]

/-- Градиенты совпадают точно: quadGrad = grad. -/
theorem quadGrad_eq_grad (a w : Fin n → ℝ) :
    DescentCoreQuad.quadGrad a w = Hagi.Model.ReferenceMachine.grad a w := by
  unfold DescentCoreQuad.quadGrad Hagi.Model.ReferenceMachine.grad
  rfl

/-- СЛЕДСТВИЕ: одношаговая сходимость Objective-контракта
(quad_one_step) переформулируется для машины: один шаг
jointStep с η=1 попадает в оптимум с НУЛЕВОЙ энергией. -/
theorem machine_one_step_zero (a w : Fin n → ℝ) :
    Hagi.Model.ReferenceMachine.energy a (Hagi.Model.ReferenceMachine.jointStep a w 1) = 0 := by
  rw [Hagi.Model.ReferenceMachine.jointStep_energy a w 1]
  have : ((1:ℝ) - 1)^2 = 0 := by norm_num
  rw [this]
  ring

end Hagi.Unified.QuadUnify
