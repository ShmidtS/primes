/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.System.GrowthState
import Hagi.Model.CertifiedTransition

set_option linter.style.header false

/-!
# ProductiveTransition — отделяем инвариантность от прогресса
(аудит v18 §3.2)

Аудит: witness полной неподвижности (Assumptions.trunc_idle_witness)
показывает, что предпосылки базового цикла допускают отсутствие
обучения. Инвариантность (система не нарушает инварианты и
сохраняет ресурсы) ≠ продуктивность (система совершает полезный
шаг с измеримым приростом).

Закрыто:
* `Productive S S'` — предикат: прирост capability ≥ δ_C ИЛИ
  спад энергии ≥ δ_L (строгий);
* `idle_not_productive` — переход с нулевыми изменениями НЕ
  продуктивен (формализация «нельзя считать productive при
  нулевом фактическом изменении полезной метрики»);
* `productive_of_ctv3_idle_false` — V3-сертификат + нулевые
  дельты → противоречие: сертифицированный спад исключает
  полную неподвижность (связка инвариантности и прогресса).
-/

namespace Hagi.Unified.PT

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- ПРОДУКТИВНЫЙ ПЕРЕХОД: измеримый прирост полезной метрики —
прирост capability ≥ δC ИЛИ спад энергии ≥ δL. -/
def Productive (S S' : Hagi.System.GrowthState X)
    (δC δL : ℝ) : Prop :=
  δC ≤ S'.capability - S.capability
    ∨ δL ≤ S.energy - S'.energy

/-- НУЛЕВОЙ ПЕРЕХОД НЕ ПРОДУКТИВЕН: при нулевых фактических
изменениях обеих метрик Productive невозможен при
положительных порогах — «нельзя считать productive при
нулевом фактическом изменении». -/
theorem idle_not_productive (S : Hagi.System.GrowthState X)
    (δC δL : ℝ) (hC : 0 < δC) (hL : 0 < δL) :
    ¬ Productive S S δC δL := by
  intro h
  rcases h with hC' | hL'
  · linarith
  · linarith

/-- СЕРТИФИЦИРОВАННЫЙ СПАД ИСКЛЮЧАЕТ ПОЛНУЮ НЕПОДВИЖНОСТЬ:
V3-сертификат (фактический спад E' < E) + нулевая дельта
энергии → противоречие. Инвариантность и продуктивность
связаны: сертифицированный переход обязательно продуктивен
по энергетическому каналу (δL может быть сколь угодно малым
положительным). -/
theorem ctv3_idle_contra {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    (S : Hagi.System.GrowthState X) (u : Hagi.Model.StageInput X)
    (riskLim : ℝ) (hc : Hagi.Model.CertifiedTransitionV3 S
      (Hagi.Model.advance S u) u riskLim)
    (hzero : (Hagi.Model.advance S u).energy = S.energy) :
    False := by
  have hdrop := hc.hActualDescent
  rw [hzero] at hdrop
  exact absurd hdrop (by linarith)

/-- СВЯЗКА: сертифицированный переход с ΔE = −d (d > 0)
продуктивен по энергии с порогом δL = d. -/
theorem productive_of_ctv3 {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    (S : Hagi.System.GrowthState X) (u : Hagi.Model.StageInput X)
    (riskLim : ℝ) (hc : Hagi.Model.CertifiedTransitionV3 S
      (Hagi.Model.advance S u) u riskLim)
    (δC δL : ℝ) (hδ : 0 < δL)
    (hdrop : S.energy - (Hagi.Model.advance S u).energy ≥ δL) :
    Productive S (Hagi.Model.advance S u) δC δL :=
  Or.inr hdrop

end Hagi.Unified.PT
