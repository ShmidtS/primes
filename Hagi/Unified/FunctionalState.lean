import Mathlib
import Hagi.Model.ReferenceMachine

/-!
# FunctionalState:
функциональное состояние — ответ на теорему-обструкцию.

Обструкция: в GrowthState эффекты — статические поля
StageEffects, и два последовательных продуктивных шага
математически несовместимы
(corePremises_single_step_obstruction : ... → False).

Здесь состояние по плану аудита:
- метрики — ВЫЧИСЛЯЕМЫЕ ФУНКЦИИ (не поля структуры);
- переход пересчитывает всё из новых весов;
- `fs_two_steps_productive`: ДВА последовательных
  продуктивных шага СТРОГО убывают энергию — прямая
  демонстрация, что обструкция — артефакт StageEffects,
  а не математики спуска.
-/

namespace Hagi.Unified.FunctionalState

open Hagi.Model.ReferenceMachine

variable {n : ℕ}

/-- Состояние: ТОЛЬКО физические переменные (веса, бюджет,
счётчик). Никаких полей-эффектов. -/
structure FunState (n : ℕ) where
  weights : Fin n → ℝ
  budget : ℝ
  stepCount : ℕ

/-- Энергия — ФУНКЦИЯ состояния (вычисляется из весов). -/
noncomputable def fsEnergy (a : Fin n → ℝ) (s : FunState n) : ℝ :=
  energy a s.weights

/-- Capability — функция состояния (probe-based можно
подключить отдельно; здесь 1/(1+E) как один канал). -/
noncomputable def fsCapa (a : Fin n → ℝ) (s : FunState n) : ℝ :=
  1 / (1 + fsEnergy a s)

/-- Функциональный шаг (совместный, без квантования —
базовый блок; квантованная версия = machineStep). -/
noncomputable def funStepJoint (a : Fin n → ℝ) (eta : ℝ)
    (s : FunState n) : FunState n where
  weights := jointStep a s.weights eta
  budget := s.budget - 1
  stepCount := s.stepCount + 1

/-- Функциональный шаг с квантованием. -/
noncomputable def funStep (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) : FunState n where
  weights := machineStep a s.weights eta Delta
  budget := s.budget - 1
  stepCount := s.stepCount + 1

/-- ЭНЕРГИЯ ФУНКЦИОНАЛЬНА: после шага энергия состояния =
энергия НОВЫХ весов (по определению, без копирования). -/
theorem fs_energy_after (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) :
    fsEnergy a (funStep a eta Delta s)
      = energy a (machineStep a s.weights eta Delta) := rfl

/-- Энергия в точке a равна нулю. -/
theorem energy_at_target (a : Fin n → ℝ) :
    energy a a = 0 := by
  unfold energy
  simp

/-- БЕЗ КВАНТОВАНИЯ: два последовательных шага СТРОГО
убывают энергию (0<η<2, η≠1, ненулевой остаток) —
обструкция GrowthState НЕ переносится на функциональное
состояние: продуктивная многошаговая динамика возможна. -/
theorem fs_two_steps_productive (a w : Fin n → ℝ) (eta : ℝ)
    (heta : 0 < eta) (heta2 : eta < 2) (hne : a ≠ w)
    (heta1 : eta ≠ 1)
    (s : FunState n) (hs : s.weights = w) :
    energy a ((funStepJoint a eta
      (funStepJoint a eta s)).weights)
      < energy a ((funStepJoint a eta s).weights)
    ∧ energy a ((funStepJoint a eta s).weights)
      < energy a s.weights := by
  have hw1 : (funStepJoint a eta s).weights
      = jointStep a w eta := by
    show jointStep a s.weights eta = jointStep a w eta
    rw [hs]
  have hw2 : (funStepJoint a eta
      (funStepJoint a eta s)).weights
      = jointStep a (jointStep a w eta) eta := by
    show jointStep a (funStepJoint a eta s).weights eta
      = jointStep a (jointStep a w eta) eta
    rw [hw1]
  rw [hw2, hw1, hs]
  -- первый шаг продуктивен
  have hdec1 := jointStep_energy_decrease a w eta heta heta2 hne
  -- остаток после первого шага ненулевой (E₁ > 0)
  have hE1 : energy a (jointStep a w eta)
      = (1 - eta) ^ 2 * energy a w := jointStep_energy a w eta
  have hE0pos : 0 < energy a w := by
    have hex : ∃ i, w i - a i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (funext fun i => by
        have := hc i
        linarith [sub_eq_zero.mp (hc i)])
    obtain ⟨i, hi⟩ := hex
    unfold energy
    exact Finset.sum_pos' (fun j _ => by positivity)
      ⟨i, Finset.mem_univ i, by positivity⟩
  have hq : (1 - eta) ^ 2 ≠ 0 := by
    intro hc
    exact heta1 (by
      have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp hc
      linarith [sub_eq_zero.mp this])
  have hE1pos : 0 < energy a (jointStep a w eta) := by
    rw [hE1]
    exact mul_pos (by positivity) hE0pos
  -- второй шаг продуктивен: остаток ≠ цели
  have hne2 : a ≠ jointStep a w eta := by
    intro hc
    have hz : energy a (jointStep a w eta) = energy a a :=
      congrArg (energy a) hc.symm
    rw [hz, energy_at_target] at hE1pos
    exact absurd hE1pos (by norm_num)
  have hdec2 := jointStep_energy_decrease a
    (jointStep a w eta) eta heta heta2 hne2
  exact ⟨hdec2, hdec1⟩

end Hagi.Unified.FunctionalState
