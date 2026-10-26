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

/-- ИТОГОВЫЙ АЛГОРИТМ (отбор безопасного шага): лучший
decrease среди кандидатов. -/
def bestDecrease (cands : List (StepCertificate X)) : ℝ :=
  (cands.map fun c => c.base.decrease).foldr max 0

/-- ОТБОР ЗВУЧЕН: если хоть один кандидат продуктивен
(положительный decrease), отбор по максимуму сертификата
даёт положительный decrease — безопасный шаг найден. -/
theorem safe_selection_productive
    (cands : List (StepCertificate X))
    (h : ∃ c ∈ cands, 0 < c.base.decrease) :
    0 < bestDecrease cands := by
  obtain ⟨c, hc, hpos⟩ := h
  unfold bestDecrease
  have hmem : c.base.decrease ∈ (cands.map fun c => c.base.decrease) :=
    List.mem_map_of_mem (f := fun c : StepCertificate X => c.base.decrease) hc
  have hle : ∀ (l : List ℝ) (x : ℝ), x ∈ l → x ≤ l.foldr max 0 := by
    intro l x hx
    induction l with
    | nil => cases hx
    | cons a l ih =>
      cases List.mem_cons.mp hx with
      | inl h => rw [h, List.foldr_cons]; exact le_max_left a _
      | inr hmem =>
        rw [List.foldr_cons]
        exact le_trans (ih hmem) (le_max_right a _)
  have hle' := hle _ _ hmem
  linarith [hle']

end Hagi.System
