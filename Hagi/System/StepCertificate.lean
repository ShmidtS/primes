import Hagi.System.GrowthState
import Hagi.Cert.StepGen

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

/-- АУДИТ v4 §3.4: ДОПУСТИМОСТЬ кандидата — риск и бюджет
укладываются в лимиты шага (не только decrease > 0). -/
def StepFeasible (riskLim budgetLim : ℝ) (c : StepCertificate X) : Prop :=
  c.base.riskSpend ≤ riskLim ∧ c.base.budgetSpend ≤ budgetLim

noncomputable instance (riskLim budgetLim : ℝ) :
    DecidablePred (fun (c : StepCertificate X) =>
      StepFeasible riskLim budgetLim c) :=
  fun _ => instDecidableAnd

/-- Лучший decrease среди ДОПУСТИМЫХ кандидатов. -/
noncomputable def bestFeasibleDecrease (riskLim budgetLim : ℝ)
    (cands : List (StepCertificate X)) : ℝ :=
  bestDecrease ((cands.filter (fun c => decide (StepFeasible riskLim budgetLim c))))

/-- ОТБОР ПОЛНОЗВУЧЕН: если ДОПУСТИМЫЙ кандидат с положительным
decrease существует, отбор среди допустимых даёт положительный
decrease — сертификат продуктивности уважает бюджет и риск
(закрытие разрыва «выбор проверяет только спуск», аудит v4 §3.4). -/
theorem safe_feasible_selection_productive
    (riskLim budgetLim : ℝ)
    (cands : List (StepCertificate X))
    (h : ∃ c ∈ cands, StepFeasible riskLim budgetLim c
      ∧ 0 < c.base.decrease) :
    0 < bestFeasibleDecrease riskLim budgetLim cands := by
  obtain ⟨c, hc, ⟨hrisk, hbud⟩, hpos⟩ := h
  unfold bestFeasibleDecrease
  apply safe_selection_productive
  refine ⟨c, ?_, hpos⟩
  exact List.mem_filter.mpr ⟨hc, by
    simp [StepFeasible, hrisk, hbud]⟩

/-! ### C279-адаптер: StepCertificate → общее ядро CertStepGen

A10 item 2 (adapter batch 2): полный сертификат шага — view над
общим ядром `Hagi.Cert.CertStepGen`. Носитель содержит ЧИСЛА
(`base.decrease` / `base.riskSpend` / `base.budgetSpend`) без
законов: спуск, точные бюджетный и риск-законы — посылки
потребителя. `riskRem` — СВОБОДНЫЙ параметр: остаток риска в
носителе не записан, это данные потребителя (без молчаливого
0-пиннинга); траты берутся из чисел носителя. -/

/-- C279: полный сертификат шага как шаг общего ядра
(premise-form: числа-траты — носителя, точные законы —
посылки потребителя; riskRem — свободный параметр). -/
noncomputable def StepCertificate.toCertStepGen {TaskId : Type*}
    {S : Type*} (c : StepCertificate X)
    (hpos : 0 < c.base.decrease)
    (M : Hagi.Cert.SystemMetrics S TaskId) (s s' : S)
    (hdesc : M.objective s' ≤ M.objective s - c.base.decrease)
    {b' riskRem : ℝ}
    (hbud : M.budget s = b' + c.base.budgetSpend)
    (hbud' : M.budget s' = b')
    (hbudnn : 0 ≤ b')
    (hrisk : M.risk s = c.base.riskSpend + riskRem)
    (hrisk' : M.risk s' = riskRem)
    (hrem : 0 ≤ riskRem)
    (obl : Hagi.Cert.StepObligations TaskId)
    (hfloors : Hagi.Cert.FloorsKept M obl s') :
    Hagi.Cert.CertStepGen M obl (fun _ => 0) s s' where
  drop := c.base.decrease
  drop_pos := hpos
  descent := hdesc
  budgetSpend := c.base.budgetSpend
  budget_next := by rw [hbud, hbud']; linarith
  budget_nonneg := by rw [hbud']; exact hbudnn
  riskSpend := c.base.riskSpend
  riskRem := riskRem
  risk_next := hrisk'
  risk_split := hrisk
  risk_nonneg := hrem
  delta := 0
  delta_next := by simp
  delta_nonneg := by norm_num
  floorsKept := hfloors

end Hagi.System
