import Mathlib
import Hagi.Unified.CertifiedLoop
import Hagi.Unified.StepContract
import Hagi.Unified.MeasureProto
import Hagi.Model.CertifiedTransition
import Hagi.Model.MeasurementCert
import Hagi.Unified.ExecutedCert

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

/-! ### Мост MeasureProto → MeasuredState -/

open Hagi.Unified.MeasureProto in
/-- Протокол измерений поставляет вектор качества:
e₀ = −loss, e₁ = −risk, e₂ = capability, e₃/e₄ —
резерв. Один мир измерений вместо двух. -/
noncomputable def protoMeasured {P : Type} (pr : MeasureProto P) :
    Hagi.Unified.LinkedQVec.MeasuredState P where
  evaluate := fun w i =>
    match i with
    | 0 => -pr.loss w
    | 1 => -pr.risk w
    | 2 => pr.capability w
    | _ => 0

theorem protoMeasured_spec {P : Type}
    (pr : Hagi.Unified.MeasureProto.MeasureProto P)
    (w : P) :
    (protoMeasured pr).evaluate w 0 = -pr.loss w
      ∧ (protoMeasured pr).evaluate w 1 = -pr.risk w
      ∧ (protoMeasured pr).evaluate w 2 = pr.capability w := by
  refine ⟨rfl, rfl, rfl⟩

/-! ### Мост CertifiedTransitionV2 → HonestTransition -/

open InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

open Hagi.Model Hagi.System

/-- Старый сертификат (verify-показатель + активный
риск-лимит) + операциональные условия спуска
(advance_energy_drop) + явные позитивности дают
зависимый HonestTransition: энергетическая гарантия
выводится из исполнения, а не из показателя. -/
noncomputable def ctv2Honest (S : Hagi.System.GrowthState X)
    (u : StageInput X) (riskLim : ℝ)
    (hc : CertifiedTransitionV2 S (advance S u) u riskLim)
    (hgain : u.eff.growEnergy ≤ S.energy - u.eff.growGain)
    (hgap0 : 0 ≤ u.gap)
    (hmerge : u.eff.mergeEnergy ≤ u.eff.growEnergy - u.gap)
    (hL : 0 < u.sp.L)
    (heta : u.sp.eta ≤ 1 / u.sp.L)
    (hdesc : ‖u.stepDir‖ ^ 2 ≤ ⟪u.grad, u.stepDir⟫_ℝ)
    (hjoint : u.eff.jointEnergy
      ≤ u.eff.mergeEnergy - u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        + u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
    (hledger : u.eff.compressEnergy - u.eff.jointEnergy
      ≤ u.sp.kappa * u.sp.s * u.eff.quantErr)
    (hD : 0 < u.eff.growGain + u.gap
      + (u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
      - u.sp.kappa * u.sp.s * u.eff.quantErr)
    (hBud : u.eff.growCost + u.eff.mergeCost
      + u.eff.jointCost + u.eff.compressCost ≤ S.budget) :
    HonestTransition (fun St => St.energy) S (advance S u)
      ((advance S u).protectedRisk - S.protectedRisk) riskLim
      (u.eff.growCost + u.eff.mergeCost + u.eff.jointCost
        + u.eff.compressCost) (advance S u).budget where
  objectiveDrop := u.eff.growGain + u.gap
      + (u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
      - u.sp.kappa * u.sp.s * u.eff.quantErr
  objectiveDrop_pos := hD
  actualDescent := by
    show (advance S u).energy ≤ S.energy - _
    have hE : (advance S u).energy = u.eff.compressEnergy := rfl
    rw [hE]
    have h := Hagi.Model.advance_energy_drop S u hgain hgap0
      hmerge hL heta hdesc hjoint hledger
    linarith
  riskBound := hc.hRiskLim
  budgetBound := by
    have hB : (advance S u).budget = S.budget
        - (u.eff.growCost + u.eff.mergeCost
          + u.eff.jointCost + u.eff.compressCost) := by
      simp [Hagi.Model.advance]
      ring
    rw [hB]
    linarith

/-! ### Мост StepMeasurement → ExecutedCert -/

/-- Сертификат измерения (claimed-полоса) + связка
измерения с исполнением дают единый ExecutedCert:
полоса пере-центрируется на фактический спуск. -/
noncomputable def smToExec {S : Type} {obj : S → ℝ} {step : S → S}
    {s : S} {m : Hagi.Model.MeasurementCert.StepMeasurement}
    (hmeas : m.measured = obj s - obj (step s))
    (hdrop : 0 < m.claimed)
    (hactual : obj (step s) ≤ obj s - m.claimed) :
    Hagi.Unified.ExecutedCert.ExecutedCert obj step s m.measured m.delta where
  drop := m.claimed
  drop_pos := hdrop
  actual := hactual
  delta_nn := m.hdelta
  link := by
    show |m.measured - (obj s - obj (step s))| ≤ m.delta
    rw [hmeas]
    simp [m.hdelta]

end Hagi.Unified.CertUnify
