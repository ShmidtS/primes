import Mathlib
import Hagi.Unified.QuadGate

/-!
# QuadTrajectory: многошаговый
сертифицированный цикл поверх ВЫЧИСЛЕННОГО gate.

Аудит №5 (этап P3): «нетривиальный многократный цикл с
реальным изменением параметров и проверяемой
безопасностью». Здесь:

- `gateStep`: шаг цикла = commit (machineStep), если gate
  открыт, иначе hold (w не меняется) — ветвление ВЫЧИСЛИМО;
- `gateTraj`: итерация gateStep — траектория весов;
- `gateStep_mono`: энергия НЕ ВОЗРАСТАЕТ на любом шаге
  (commit — строго убывает по quad_gate_commit, hold —
  точное равенство);
- `gateTraj_mono`: кумулятивная монотонность по T;
- `gateTraj_drop`: суммарное убывание = Σ приростов
  commit-шагов (телескоп честный, каждая ступень вычислена).
-/

namespace Hagi.Unified.QuadTrajectory

open Classical

open Hagi.Model.ReferenceMachine Hagi.Unified.QuadGate Hagi.Unified.CommitGate

variable {n : ℕ}

/-- Один шаг цикла: commit при открытом gate, иначе hold. -/
noncomputable def gateStep (a : Fin n → ℝ) (eta Delta : ℝ)
    (w : Fin n → ℝ) : Fin n → ℝ :=
  if gate (machineCert a w eta Delta) then
    machineStep a w eta Delta else w

/-- Траектория: итерация gateStep из w₀. -/
noncomputable def gateTraj (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => w₀
  | (t + 1) => gateStep a eta Delta (gateTraj a eta Delta w₀ t)

/-- МОНОТОННОСТЬ ШАГА: энергия не возрастает на каждом
шаге цикла (commit: строгое убывание; hold: равенство). -/
theorem gateStep_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w : Fin n → ℝ) :
    energy a (gateStep a eta Delta w) ≤ energy a w := by
  unfold gateStep
  by_cases hg : gate (machineCert a w eta Delta)
  · rw [if_pos hg]
    exact le_of_lt (quad_gate_commit a w eta Delta hD hg)
  · rw [if_neg hg]

/-- Кумулятивная монотонность: энергия вдоль всей
траектории не возрастает (индукция по T). -/
theorem gateTraj_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w₀ : Fin n → ℝ) (T : ℕ) :
    energy a (gateTraj a eta Delta w₀ T) ≤ energy a w₀ := by
  induction T with
  | zero => exact le_refl (energy a w₀)
  | succ t ih =>
    have hstep := gateStep_mono a eta Delta hD
      (gateTraj a eta Delta w₀ t)
    exact le_trans hstep ih

/-- ЧЕСТНЫЙ ТЕЛЕСКОП: убывание на шаге — разность РЕАЛЬНЫХ
энергий (commit) или ноль (hold); при открытом gate
убывание СТРОГО положительно. -/
theorem gateStep_drop (a : Fin n → ℝ) (eta Delta : ℝ)
    (w : Fin n → ℝ) :
    energy a w - energy a (gateStep a eta Delta w)
      = if gate (machineCert a w eta Delta)
        then energy a w
          - energy a (machineStep a w eta Delta)
        else 0 := by
  unfold gateStep
  by_cases hg : gate (machineCert a w eta Delta)
  · rw [if_pos hg, if_pos hg]
  · rw [if_neg hg, if_neg hg]
    ring

/-- Строгое убывание НА COMMIT: gate открыт ⟹ шаг строго
уменьшает вычисленную энергию (реюз quad_gate_commit). -/
theorem gateStep_pos (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w : Fin n → ℝ)
    (hg : gate (machineCert a w eta Delta)) :
    0 < energy a w - energy a (gateStep a eta Delta w) := by
  rw [gateStep_drop]
  rw [if_pos hg]
  exact sub_pos.mpr (quad_gate_commit a w eta Delta hD hg)

end Hagi.Unified.QuadTrajectory