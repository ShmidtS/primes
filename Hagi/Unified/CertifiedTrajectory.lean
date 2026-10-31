import Mathlib
import Hagi.Unified.StepContract
import Hagi.Model.MeasurementCert

/-!
# CertifiedTrajectory — единая траекторная теорема (такт №230)

Связка трёх уровней сертификации в одно утверждение:
1. Execution (CertifiedTransition.exec — переход выполнен);
2. Measurement (StepMeasurement — заявленный прирост в
   anytime-полосе измеренного);
3. Contract (StepContract — доказанное падение потенциала
   + риск + бюджет; телескопирование trajectory_convergence).

Итог: ЧЕСТНЫЙ КУМУЛЯТИВНЫЙ ПРОГРЕСС — нижняя оценка по
измерениям (Σ measured − Σ δ) не превосходит верхнюю
гарантию по потенциалу (Φ₀ − Φ_min + Σ risk): прогресс
одновременно подтверждён данными И ограничен теорией.
-/

namespace Hagi.Unified.CertifiedTrajectory

open Hagi.Unified.StepCert Hagi.Model.MeasurementCert

/-- ЕДИНАЯ ТРАЕКТОРНАЯ ТЕОРЕМА: если каждый шаг t
(а) выполнен как контракт StepContract с падением
    decrease = claimed (связка контракта с измерением), и
() его измеренный прирост лежит в anytime-полосе
    (StepMeasurement), и
(c) потенциал Φ ограничен снизу и спускается по контракту,
то кумулятивный ИЗМЕРЕННЫЙ прирост за вычетом суммарной
полосы не превосходит Φ₀ − Φ_min + Σ risk: прогресс
подтверждён снизу данными и ограничен сверху теорией. -/
theorem certified_progress_honest {T : ℕ}
    (cs : Fin T → StepContract)
    (ms : Fin T → StepMeasurement)
    (hlink : ∀ t : Fin T, (cs t).decrease = (ms t).claimed)
    (Φ : ℕ → ℝ) (Φ_min : ℝ)
    (h_step : ∀ t : Fin T,
      Φ (t.val + 1) ≤ Φ t.val - (cs t).decrease + (cs t).riskCost)
    (h_floor : ∀ t ≤ T, Φ_min ≤ Φ t) :
    ∑ t : Fin T, (ms t).measured - ∑ t : Fin T, (ms t).delta
      ≤ Φ 0 - Φ_min + ∑ t : Fin T, (cs t).riskCost := by
  -- нижняя полоса измерений ≤ Σ claimed (chain_floor) ...
  have hmeas := chain_floor ms
  -- ... claimed = decrease (связка) ...
  have hclaim : ∑ t : Fin T, (ms t).claimed
      = ∑ t : Fin T, (cs t).decrease := by
    refine Finset.sum_congr rfl ?_
    intro t _
    exact (hlink t).symm
  -- ... и decrease ≤ Φ₀ − Φ_min + Σ risk (телескоп)
  have htele := trajectory_convergence cs Φ Φ_min h_step h_floor
  linarith [hmeas, hclaim ▸ htele]

/-- СЛЕДСТВИЕ — СИГНАЛЬНЫЙ ПРИРОС: если суммарный измеренный
прирост строго превышает суммарную полосу шума, то
кумулятивный прогресс строго положителен И ограничен
бюджетно-рисковой квотой теории. -/
theorem certified_progress_signal {T : ℕ}
    (cs : Fin T → StepContract)
    (ms : Fin T → StepMeasurement)
    (hlink : ∀ t : Fin T, (cs t).decrease = (ms t).claimed)
    (Φ : ℕ → ℝ) (Φ_min : ℝ)
    (h_step : ∀ t : Fin T,
      Φ (t.val + 1) ≤ Φ t.val - (cs t).decrease + (cs t).riskCost)
    (h_floor : ∀ t ≤ T, Φ_min ≤ Φ t)
    (hsignal : ∑ t : Fin T, (ms t).delta
      < ∑ t : Fin T, (ms t).measured) :
    0 < ∑ t : Fin T, (cs t).decrease
      ∧ ∑ t : Fin T, (cs t).decrease
        ≤ Φ 0 - Φ_min + ∑ t : Fin T, (cs t).riskCost := by
  constructor
  · -- Σ claimed ≥ Σ measured − Σ δ > 0
    have hmeas := chain_floor ms
    have hclaim : ∑ t : Fin T, (ms t).claimed
        = ∑ t : Fin T, (cs t).decrease :=
      Finset.sum_congr rfl (fun t _ => (hlink t).symm)
    have h0 : ∑ t : Fin T, (ms t).measured - ∑ t : Fin T, (ms t).delta
        ≤ ∑ t : Fin T, (ms t).claimed := hmeas
    rw [hclaim] at h0
    have hpos : (0:ℝ) < ∑ t : Fin T, (ms t).measured
        - ∑ t : Fin T, (ms t).delta := by
      have : (0:ℝ) < ∑ t : Fin T, (ms t).measured
          - ∑ t : Fin T, (ms t).delta :=
        sub_pos.mpr hsignal
      linarith
    linarith
  · exact trajectory_convergence cs Φ Φ_min h_step h_floor

end Hagi.Unified.CertifiedTrajectory
