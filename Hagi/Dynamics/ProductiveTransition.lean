/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.System.GrowthState
import Hagi.Model.CertifiedTransition
import Mathlib.Tactic

set_option linter.style.header false

/-!
# ProductiveTransition — отделяем инвариантность от прогресса

Предпосылки базового цикла допускают отсутствие обучения
(witness полной неподвижности `Assumptions.trunc_idle_witness`). Инвариантность (система не нарушает инварианты и
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
set_option linter.style.header false

/-!
# ControllerPolicy — выведенная оптимальная политика контроллера

* `ratio_dominance`: при максимальном сертифицированном
  отношении `Γ ibest/K ibest` и бюджете B —
  `Gam j·(B/K j) ≤ Gam ibest·(B/K ibest)`;
* `budget_allocation_dominance`: при неотрицательных
  `alloc` с `Σ alloc a·K (idx a) ≤ B` —
  `Σ Gam (idx a)·alloc a ≤ (Gam ibest/K ibest)·B` —
  концентрация бюджета на лучшем отношении доминирует
  любое разбиение.
-/

open Real Finset

namespace Hagi.Dynamics

theorem ratio_dominance (Gam : ℕ → ℝ) (K : ℕ → ℝ) (ibest j : ℕ) (B : ℝ)
    (_hK : ∀ i, 0 < K i)
    (hratio : ∀ i, Gam i / K i ≤ Gam ibest / K ibest)
    (hB : 0 ≤ B) :
    Gam j * (B / K j) ≤ Gam ibest * (B / K ibest) := by
  have h1 : Gam j / K j ≤ Gam ibest / K ibest := hratio j
  have hmul : (Gam j / K j) * B ≤ (Gam ibest / K ibest) * B :=
    mul_le_mul_of_nonneg_right h1 hB
  have e1 : (Gam j / K j) * B = Gam j * (B / K j) := by ring
  have e2 : (Gam ibest / K ibest) * B = Gam ibest * (B / K ibest) := by ring
  rw [e1, e2] at hmul
  exact hmul

/-- При `0 < K i`, максимальном отношении
`Gam i/K i ≤ Gam ibest/K ibest` и `0 ≤ B`:
`Gam j·(B/K j) ≤ Gam ibest·(B/K ibest)`. -/
theorem budget_allocation_dominance (Gam : ℕ → ℝ) (K : ℕ → ℝ) (ibest : ℕ)
    {iota : Type} [Fintype iota] (idx : iota → ℕ) (alloc : iota → ℝ) (B : ℝ)
    (hK : ∀ i, 0 < K i) (hGam : ∀ i, 0 ≤ Gam i)
    (hratio : ∀ i, Gam i / K i ≤ Gam ibest / K ibest)
    (halloc : ∀ a, 0 ≤ alloc a)
    (hsum : ∑ a : iota, alloc a * K (idx a) ≤ B) :
    ∑ a : iota, Gam (idx a) * alloc a
      ≤ (Gam ibest / K ibest) * B := by
  have hterm : ∀ a : iota, Gam (idx a) * alloc a
      ≤ (Gam ibest / K ibest) * (alloc a * K (idx a)) := by
    intro a
    have hr0 := hratio (idx a)
    have hKpos := hK (idx a)
    have hKib := hK ibest
    rw [div_le_div_iff₀ hKpos hKib] at hr0
    have hmul : alloc a * (Gam (idx a) * K ibest)
        ≤ alloc a * (Gam ibest * K (idx a)) :=
      mul_le_mul_of_nonneg_left hr0 (halloc a)
    rw [show Gam ibest / K ibest * (alloc a * K (idx a))
        = (Gam ibest * (alloc a * K (idx a))) / K ibest from by ring]
    rw [le_div_iff₀ hKib]
    nlinarith [hmul]
  calc ∑ a, Gam (idx a) * alloc a
      ≤ ∑ a, (Gam ibest / K ibest) * (alloc a * K (idx a)) :=
        Finset.sum_le_sum (s := Finset.univ) (f := fun a => Gam (idx a) * alloc a)
          (g := fun a => (Gam ibest / K ibest) * (alloc a * K (idx a)))
          (fun a _ => hterm a)
    _ = (Gam ibest / K ibest) * ∑ a, (alloc a * K (idx a)) := by
        exact (Finset.mul_sum (s := Finset.univ)
          (f := fun a => alloc a * K (idx a)) (a := Gam ibest / K ibest)).symm
    _ ≤ (Gam ibest / K ibest) * B :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (hGam ibest) (hK ibest).le)

end Hagi.Dynamics


set_option linter.style.header false

/-!
# ProxyDeploymentGap — self-shift в eps-бюджете

Порт 2609.32677 (certified thresholds при self-induced
distribution shift), абстрактная бюджетная форма.

Контракт: верификатор F3-петли выдаёт пороги
(certified thresholds). Каждая итерация самообучения
сдвигает распределение, на котором верификатор измерял свой
порог: измеримый зазор proxy-deployment delta_t входит в
eps-бюджет как ДОПОЛНИТЕЛЬНЫЙ член рядом со статистической
погрешностью e_t.

* `budget_consumed` — монотонность потребления бюджета.
* `guarantee_horizon_bound` — если каждый шаг тратит не менее
  c > 0 (min стат-погрешность + сдвиг), то горизонт живости
  гарантии ограничен eps / c: self-shift ограничивает скорость
  самообновления верификатора (Red-Queen-цена).
* `shift_paid_from_budget` — зазор любого подмножества шагов
  всегда оплачен из общего бюджета: перенести сертифицированный
  порог на сдвинутое распределение можно только за счёт eps.

**Честные границы**: e_t и delta_t — измеряемые (h_emp_-слой);
теорема НЕ утверждает, что зазор мал — только что он
ОПЛАЧИВАЕТСЯ из того же eps-бюджета, что и статистика.
-/

open Finset Real

namespace Hagi.Dynamics

/-- Пошаговый контракт бюджета: guarantee-предикат жив,
пока накопленное потребление (стат-погрешность + зазор
proxy-deployment) не превысило eps. -/
def BudgetAlive (e delta : ℕ → ℝ) (eps : ℝ) (T : ℕ) : Prop :=
  ∑ t ∈ Finset.range T, (e t + delta t) ≤ eps

/-- **Монотонность потребления**: живость на длинном
горизонте влечёт живость на коротком. -/
theorem budget_consumed (e delta : ℕ → ℝ) (eps : ℝ) (T : ℕ)
    (hnn : ∀ t, 0 ≤ e t + delta t)
    (halive : BudgetAlive e delta eps (T + 1)) :
    BudgetAlive e delta eps T := by
  unfold BudgetAlive at *
  have h := halive
  have hmono : ∑ t ∈ Finset.range T, (e t + delta t)
      ≤ ∑ t ∈ Finset.range (T + 1), (e t + delta t) := by
    rw [Finset.sum_range_succ]
    linarith [hnn T]
  exact le_trans hmono h

/-- **Предел скорости самообновления**: если каждый шаг
потребляет не менее c > 0 бюджета, то горизонт живости
ограничен eps: (T: R) * c <= eps. Self-induced shift
ограничивает частоту самообновлений верификатора. -/
theorem guarantee_horizon_bound (e delta : ℕ → ℝ) (eps c : ℝ)
    (hc : 0 < c)
    (hstep : ∀ t, c ≤ e t + delta t)
    (T : ℕ) (halive : BudgetAlive e delta eps T) :
    (T : ℝ) * c ≤ eps := by
  have hsum : ∑ t ∈ Finset.range T, (e t + delta t) ≤ eps := halive
  have hge : ∀ K : ℕ,
      (K : ℝ) * c ≤ ∑ t ∈ Finset.range K, (e t + delta t) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ]
        push_cast
        nlinarith [ih, hstep K]
  linarith [hge T]

/-- **Зазор оплачен бюджетом**: суммарный self-shift любого
подмножества шагов горизонта не превосходит полного бюджета:
сертифицированный порог переносится на сдвинутое
распределение только за счёт eps (слагаемое зазора нельзя
«спрятать» в статистическую часть бесплатно). -/
theorem shift_paid_from_budget (e delta : ℕ → ℝ) (eps : ℝ)
    (T : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range T)
    (he : ∀ t, 0 ≤ e t) (hdelta : ∀ t, 0 ≤ delta t)
    (halive : BudgetAlive e delta eps T) :
    ∑ t ∈ S, delta t ≤ eps := by
  have h1 : ∑ t ∈ S, delta t
      ≤ ∑ t ∈ S, (e t + delta t) :=
    Finset.sum_le_sum fun t _ => by linarith [he t]
  have hdiff : (0:ℝ)
      ≤ ∑ t ∈ Finset.range T \ S, (e t + delta t) :=
    Finset.sum_nonneg fun t _ => by linarith [he t, hdelta t]
  have h2 : ∑ t ∈ S, (e t + delta t)
      ≤ ∑ t ∈ Finset.range T, (e t + delta t) := by
    have hsd : ∑ t ∈ Finset.range T \ S, (e t + delta t)
          + ∑ t ∈ S, (e t + delta t)
        = ∑ t ∈ Finset.range T, (e t + delta t) :=
      Finset.sum_sdiff hS
    linarith [hdiff, hsd]
  have h3 := halive
  exact le_trans h1 (le_trans h2 h3)

end Hagi.Dynamics

