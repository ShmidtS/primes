import Mathlib
import Hagi.Unified.MeasureProto
import Hagi.Unified.QuadMachine

/-!
# ProtoTrajectory: протокол × траектория —
полная цепочка execution × measurement × certificate.

Замыкание интеграции аудита №5: лоссы, измеряемые
ПРОТОКОЛОМ (MeasureProto, ), вдоль РЕАЛЬНОЙ
траектории commit/hold (QuadTrajectory, ):

1. `proto_loss_mono`: loss-канал протокола не возрастает
   вдоль траектории (проекция gateTraj_mono);
2. `proto_loss_telescope`: ТОЧНЫЙ телескоп loss-канала =
   E₀ − E_T (проекция trajDropSum);
3. `proto_progress_bound`: суммарный сертифицированный
   прогресс loss-канала ≤ начального loss (проекция
   trajDropBound).

Всё происхождено: исполнение (gateTraj) × измерение
(machineProto.loss = energy) × сертификат (телескоп).
-/

namespace Hagi.Unified.ProtoTrajectory

open Hagi.Model.ReferenceMachine Hagi.Unified.QuadGate
  Hagi.Unified.QuadTrajectory Hagi.Unified.QuadBudget
  Hagi.Unified.MeasureProto

variable {n : ℕ}

/-- Лосс-канал протокола НЕ ВОЗРАСТАЕТ вдоль траектории. -/
theorem proto_loss_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w₀ : Fin n → ℝ) (T : ℕ) :
    (machineProto a).loss (gateTraj a eta Delta w₀ T)
      ≤ (machineProto a).loss w₀ := by
  show energy a (gateTraj a eta Delta w₀ T) ≤ energy a w₀
  exact gateTraj_mono a eta Delta hD w₀ T

/-- ТОЧНЫЙ телескоп loss-канала протокола. -/
theorem proto_loss_telescope (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T,
      ((machineProto a).loss (gateTraj a eta Delta w₀ t)
        - (machineProto a).loss
          (gateTraj a eta Delta w₀ (t + 1)))
      = (machineProto a).loss w₀
        - (machineProto a).loss (gateTraj a eta Delta w₀ T) :=
  trajDropSum a eta Delta w₀ T

/-- СУММАРНЫЙ СЕРТИФИЦИРОВАННЫЙ ПРОГРЕСС ≤ начального
loss (измеренного протоколом). -/
theorem proto_progress_bound (a : Fin n → ℝ) (eta Delta : ℝ)
    (w₀ : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T,
      ((machineProto a).loss (gateTraj a eta Delta w₀ t)
        - (machineProto a).loss
          (gateTraj a eta Delta w₀ (t + 1)))
      ≤ (machineProto a).loss w₀ :=
  trajDropBound a eta Delta w₀ T

/-- CAPABILITY-КАНАЛ НЕ УБЫВАЕТ вдоль траектории
(инверсия loss-монотонности: меньше энергии — больше
capability). -/
theorem proto_capa_mono (a : Fin n → ℝ) (eta Delta : ℝ)
    (hD : 0 < Delta) (w₀ : Fin n → ℝ) (T : ℕ) :
    (machineProto a).capability w₀
      ≤ (machineProto a).capability
        (gateTraj a eta Delta w₀ T) := by
  exact machineProto_capa_mono a (gateTraj a eta Delta w₀ T)
    w₀ (gateTraj_mono a eta Delta hD w₀ T)

end Hagi.Unified.ProtoTrajectory
