import Hagi.System.GrowthState

/-!
# StepCertificate — полный сертификат шага (P2.10)

Спуск, риск, ошибка обобщения, стоимость в одном контракте:
базовый Certificate (decrease/riskSpend/budgetSpend) плюс
gen-полоса epsG (компонентная полоса метрик обобщения —
см. Unified.MasterHAGI FullCycleRefinement).
-/

namespace Hagi.System

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- P2.10: ПОЛНЫЙ СЕРТИФИКАТ ШАГА — спуск, риск, ошибка
обобщения (полоса epsG), стоимость в одном контракте. -/
structure StepCertificate (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] where
  /-- Базовый сертификат спуска/риска/стоимости. -/
  base : Certificate
  /-- Эпсилон-полоса метрик обобщения шага. -/
  epsG : ℝ
  h_epsG : 0 ≤ epsG

/-- КОНСТРУКТОР-МОСТ: сертификат цикла состояния плюс gen-полоса
дают полный StepCertificate. -/
noncomputable def stepCertificateOfParts (S : GrowthState X)
    (epsG : ℝ) (h_epsG : 0 ≤ epsG) : StepCertificate X where
  base := verify S
  epsG := epsG
  h_epsG := h_epsG

/-- Звучность конструктора: базовое поле — в точности
verify-сертификат состояния. -/
theorem stepCertificate_base (S : GrowthState X)
    (epsG : ℝ) (h_epsG : 0 ≤ epsG) :
    (stepCertificateOfParts S epsG h_epsG).base = verify S := rfl

end Hagi.System
