import Mathlib
import Hagi.Unified.FunctionalState
import Hagi.Unified.QuadMachine

/-!
# FsGate: commit/hold-gate над ФУНКЦИОНАЛЬНЫМ
состоянием — замыкание FunState в траекторный цикл.

Мост: веса fsGate-шага РАВНЫ gateStep из QuadTrajectory
(тот же вычисленный gate); энергия — функция состояния.
Следствия (все проекции доказанных теорем):
1. `fsGate_weights_eq`: fsGate-веса = gateStep-веса;
2. `fsGate_mono`: энергия функционального состояния не
   возрастает на gate-шаге;
3. `fsTraj_mono`: кумулятивная монотонность по T.

Итог: полный стек (FunState × QuadGate × QuadTrajectory)
— функциональное состояние в сертифицированном цикле.
-/

namespace Hagi.Unified.FsGate

open Hagi.Model.ReferenceMachine Hagi.Unified.FunctionalState
  Hagi.Unified.QuadGate Hagi.Unified.QuadTrajectory
  Hagi.Unified.CommitGate

variable {n : ℕ}

open Classical

/-- Gate-шаг над функциональным состоянием: commit при
открытом gate (веса = machineStep), иначе hold. -/
noncomputable def fsGate (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) : FunState n :=
  if gate (machineCert a s.weights eta Delta) then
    funStep a eta Delta s else s

/-- Веса-мост: fsGate-веса = gateStep-веса (тот же
вычисленный gate над теми же весами). -/
theorem fsGate_weights_eq (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) :
    (fsGate a eta Delta s).weights
      = gateStep a eta Delta s.weights := by
  unfold fsGate gateStep funStep
  by_cases hg : gate (machineCert a s.weights eta Delta)
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]

/-- ЭНЕРГИЯ НЕ ВОЗРАСТАЕТ на gate-шаге (проекция
gateStep_mono через веса-мост). -/
theorem fsGate_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (s : FunState n) :
    fsEnergy a (fsGate a eta Delta s) ≤ fsEnergy a s := by
  unfold fsEnergy
  rw [fsGate_weights_eq a eta Delta s]
  exact gateStep_mono a eta Delta hD s.weights

/-- Траектория функционального состояния. -/
noncomputable def fsTraj (a : Fin n → ℝ) (eta Delta : ℝ)
    (s₀ : FunState n) : ℕ → FunState n
  | 0 => s₀
  | (t + 1) => fsGate a eta Delta (fsTraj a eta Delta s₀ t)

/-- Кумулятивная монотонность: энергия вдоль всей
fs-траектории не возрастает (индукция + fsGate_mono). -/
theorem fsTraj_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (s₀ : FunState n) (T : ℕ) :
    fsEnergy a (fsTraj a eta Delta s₀ T) ≤ fsEnergy a s₀ := by
  induction T with
  | zero => exact le_refl _
  | succ t ih =>
    have hstep := fsGate_mono a eta Delta hD
      (fsTraj a eta Delta s₀ t)
    exact le_trans hstep ih


/-- БЮДЖЕТ-ШАГ: commit платит 1, hold бесплатен. -/
theorem fsGate_budget (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) :
    (fsGate a eta Delta s).budget
      = if gate (machineCert a s.weights eta Delta)
        then s.budget - 1 else s.budget := by
  unfold fsGate funStep
  by_cases hg : gate (machineCert a s.weights eta Delta)
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]

/-- СЧЁТЧИК-ШАГ: commit считается, hold нет. -/
theorem fsGate_count (a : Fin n → ℝ) (eta Delta : ℝ)
    (s : FunState n) :
    (fsGate a eta Delta s).stepCount
      = if gate (machineCert a s.weights eta Delta)
        then s.stepCount + 1 else s.stepCount := by
  unfold fsGate funStep
  by_cases hg : gate (machineCert a s.weights eta Delta)
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]

/-- БЮДЖЕТ НЕ ВОЗРАСТАЕТ: бюджет вдоль fs-траектории не
превышает начального (индукция: commit платит, hold
бесплатен). -/
theorem fsTraj_budget_le (a : Fin n → ℝ) (eta Delta : ℝ)
    (s₀ : FunState n) (T : ℕ) :
    (fsTraj a eta Delta s₀ T).budget ≤ s₀.budget := by
  induction T with
  | zero => exact le_refl _
  | succ t ih =>
    simp only [fsTraj]
    have hstep := fsGate_budget a eta Delta
      (fsTraj a eta Delta s₀ t)
    rw [hstep]
    by_cases hg : gate (machineCert a
      ((fsTraj a eta Delta s₀ t)).weights eta Delta)
    · rw [if_pos hg]
      linarith
    · rw [if_neg hg]
      exact ih

/-- СЧЁТЧИК ≤ T: число реальных шагов не превышает горизонт
(верхняя граница commitCount). -/
theorem fsTraj_count_le (a : Fin n → ℝ) (eta Delta : ℝ)
    (s₀ : FunState n) (T : ℕ) :
    (fsTraj a eta Delta s₀ T).stepCount
      ≤ s₀.stepCount + T := by
  induction T with
  | zero =>
    show s₀.stepCount ≤ s₀.stepCount + 0
    omega
  | succ t ih =>
    simp only [fsTraj]
    have hstep := fsGate_count a eta Delta
      (fsTraj a eta Delta s₀ t)
    rw [hstep]
    by_cases hg : gate (machineCert a
      ((fsTraj a eta Delta s₀ t)).weights eta Delta)
    · rw [if_pos hg]
      omega
    · rw [if_neg hg]
      omega

end Hagi.Unified.FsGate
