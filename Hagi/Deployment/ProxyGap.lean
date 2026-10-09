/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib
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

namespace Hagi

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

end Hagi
