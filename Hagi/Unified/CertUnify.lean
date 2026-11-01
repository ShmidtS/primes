import Mathlib
import Hagi.Unified.CertifiedLoop
import Hagi.Unified.StepContract

/-!
# CertUnify : сведение сертификатных миров

Раньше два параллельных телескопа:
- StepContract.trajectory_convergence (моноид-мир,
  ~2000 строк шаблона заменил);
- CertifiedLoop.certified_loop (зависимый мир).

Здесь формально: StepCert-мир ПОСТАВЛЯЕТ посылки
моноид-телескопа — trajectory_convergence становится
СЛЕДСТВИЕМ certified-цепочки, а не параллельной теорией.

1. `scOf`: проекция StepCert → StepContract
   (decrease = drop, riskCost = 0 — риск учтён в
   riskBound-гипотезе перехода, budgetSpend = spend);
2. `tc_step_of_steṕcert`: посылка h_step старого
   телескопа ВЫВОДИМА из StepCert-цепочки (без новых
   предположений);
3. `tc_consequence`: итог trajectory_convergence для
   certified-цепочки — старый телескоп применим
   автоматически.

Замечание: certified_loop даёт оценку БЕЗ пошагового
floor (сильнее); tc-версия сохранена для совместимости
с моноид-композицией контрактов.
-/

namespace Hagi.Unified.CertUnify

open Hagi.Unified.CertifiedLoop Hagi.Unified.StepCert
open Hagi.Unified.HonestTransition Hagi.Unified.LinkedQVec

variable {S : Type*}

/-- Проекция зависимого шага в моноид-контракт. -/
noncomputable def scOf (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (s s' : S) (bt b' : ℝ)
    (c : StepCert obj M floor riskLim s s' bt b') :
    StepContract where
  decrease := c.trans.objectiveDrop
  riskCost := 0
  budgetSpend := c.spend
  hDecreasePos := le_of_lt c.trans.objectiveDrop_pos
  hRiskNonneg := le_refl 0
  hBudgetNonneg := c.hspend_nn

/-- Посылка h_step старого телескопа ВЫВОДИМА из
StepCert-цепочки (riskCost = 0: риск уже учтён в
riskBound-гипотезе каждого перехода). -/
theorem tc_step_of_stepcert (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b : ℕ → ℝ) (n : ℕ)
    (certs : ∀ t : Fin n,
      StepCert obj M floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1)))
    (t : Fin n) :
    obj (f (t.val + 1))
      ≤ obj (f t.val) - (scOf obj M floor riskLim _ _ _ _
        (certs t)).decrease
        + (scOf obj M floor riskLim _ _ _ _ (certs t)).riskCost := by
  have hd : (scOf obj M floor riskLim _ _ _ _
      (certs t)).decrease = (certs t).trans.objectiveDrop := rfl
  have hr : (scOf obj M floor riskLim _ _ _ _
      (certs t)).riskCost = 0 := rfl
  rw [hd, hr]
  linarith [(certs t).trans.actualDescent]

/-- ИТОГ trajectory_convergence для certified-цепочки:
старый телескоп — автоматическое следствие. -/
theorem tc_consequence (obj : S → ℝ) (M : MeasuredState S)
    (floor : Fin 5 → ℝ) (riskLim : ℝ)
    (f : ℕ → S) (b : ℕ → ℝ) (n : ℕ)
    (certs : ∀ t : Fin n,
      StepCert obj M floor riskLim (f t.val) (f (t.val + 1))
        (b t.val) (b (t.val + 1)))
    (Φ_min : ℝ) (h_floor : ∀ t ≤ n, Φ_min ≤ obj (f t)) :
    ∑ t : Fin n, (certs t).trans.objectiveDrop
      ≤ obj (f 0) - Φ_min := by
  have key := trajectory_convergence
    (fun t => scOf obj M floor riskLim (f t.val) (f (t.val + 1))
      (b t.val) (b (t.val + 1)) (certs t))
    (fun t => obj (f t)) Φ_min
    (fun t => tc_step_of_stepcert obj M floor riskLim f b n
      certs t)
    h_floor
  have hsum : ∑ t : Fin n, (scOf obj M floor riskLim
      (f t.val) (f (t.val + 1)) (b t.val) (b (t.val + 1))
      (certs t)).decrease
      = ∑ t : Fin n, (certs t).trans.objectiveDrop :=
    Finset.sum_congr rfl fun t _ => rfl
  have hsumr : ∑ t : Fin n, (scOf obj M floor riskLim
      (f t.val) (f (t.val + 1)) (b t.val) (b (t.val + 1))
      (certs t)).riskCost = 0 := by
    simp [scOf]
  rwa [hsum, hsumr, add_zero] at key

end Hagi.Unified.CertUnify
