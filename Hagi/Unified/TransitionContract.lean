import Mathlib
import Hagi.Model.CertifiedTransition
import Hagi.Unified.StepContract

/-!
# TransitionContract (P1-миграция v3, такт №246)

Мост CertifiedTransitionV2 → StepContract: каждый
сертифицированный переход (исполнение + активный риск-лимит)
порождает числовой контракт шага моноида StepContract —
после чего ЕДИНАЯ траекторная теорема
trajectory_convergence / certified_progress_honest применима
к реальным переходам без дублирования телескопов.
-/

namespace Hagi.Unified.TransitionContract

open Hagi.System Hagi.Model Hagi.Unified.StepCert

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Порождённый контракт шага: доказанный спуск = verify-
сертификат пост-состояния; риск = сумма эффект-рисков шага
(неотрицательна по h_risks_nn); бюджет = сумма эффект-стоимостей. -/
noncomputable def ctContract (S S' : GrowthState X)
    (u : StageInput X) (riskLim : ℝ)
    (hd0 : 0 ≤ (verify S').decrease) : StepContract where
  decrease := (verify S').decrease
  riskCost := u.eff.growRisk + u.eff.mergeRisk
    + u.eff.jointRisk + u.eff.compressRisk
  budgetSpend := u.eff.growCost + u.eff.mergeCost
    + u.eff.jointCost + u.eff.compressCost
  hDecreasePos := hd0
  hRiskNonneg := by
    obtain ⟨h1, h2, h3, h4⟩ := u.h_risks_nn
    linarith
  hBudgetNonneg := by
    obtain ⟨h1, h2, h3, h4⟩ := u.h_costs_nn
    linarith

/-- МОСТ V2 → CONTRACT: сертифицированный переход с
неотрицательным verify-спуском порождает StepContract;
спуск контракта = сертификат пост-состояния. -/
theorem ctv2_contract (S S' : GrowthState X) (u : StageInput X)
    (riskLim : ℝ) (hc : CertifiedTransitionV2 S S' u riskLim)
    (hd0 : 0 ≤ (verify S').decrease) :
    (ctContract S S' u riskLim hd0).decrease
      = (verify S').decrease := rfl

/-- РИСК КОНТРАКТА ДОМИНИРУЕТ ПРИРОСТ: safety-бухгалтерия
CertifiedTransition даёт ΔR ≤ riskCost контракта — риск-канал
StepContract честно накрывает реальный прирост риска. -/
theorem ctRisk_covers (S S' : GrowthState X) (u : StageInput X)
    (riskLim : ℝ) (hc : CertifiedTransition S S' u riskLim)
    (hd0 : 0 ≤ (verify S').decrease) :
    S'.protectedRisk - S.protectedRisk
      ≤ (ctContract S S' u riskLim hd0).riskCost := by
  have hs := hc.safety
  unfold ctContract
  linarith

end Hagi.Unified.TransitionContract
