import Mathlib
import Hagi.Unified.CertifiedLoop
import Hagi.Unified.StepContract
import Hagi.Unified.MachineProto
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
   (decrease = drop, riskCost = riskSpend — реальный расход
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
  riskCost := c.riskSpend
  budgetSpend := c.budgetSpend
  hDecreasePos := le_of_lt c.trans.objectiveDrop_pos
  hRiskNonneg := c.hriskSpend_nn
  hBudgetNonneg := c.hbudgetSpend_nn

/-- Посылка h_step старого телескопа ВЫВОДИМА из
StepCert-цепочки (riskCost = riskSpend: риск больше НЕ
сбрасывается — TD-07 исправлен, контракт несёт реальный
расход риска). -/
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
      (certs t)).riskCost = (certs t).riskSpend := rfl
  rw [hd, hr]
  linarith [(certs t).trans.actualDescent, (certs t).hriskSpend_nn]

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
      ≤ obj (f 0) - Φ_min
        + ∑ t : Fin n, (certs t).riskSpend := by
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
      (certs t)).riskCost
      = ∑ t : Fin n, (certs t).riskSpend := by
    exact Finset.sum_congr rfl fun t _ => rfl
  rwa [hsum, hsumr] at key

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

/-! ### Мост ExecutedCert → StepContract (композиционное
замыкание: цепочки сертификатов исполнения сводятся к
моноид-телескопу StepContract — audit v19 §4) -/

/-- Проекция сертификата исполнения+измерения в моноид-контракт:
drop → decrease, risk/budget передаются явно (исполнение их не
порождает — их поставляет носитель), связка измерения с
исполнением уже внутри типа. -/
noncomputable def ecToSc {S : Type} {obj : S → ℝ} {step : S → S}
    {s : S} {m d : ℝ}
    (c : Hagi.Unified.ExecutedCert.ExecutedCert obj step s m d)
    (riskCost budgetSpend : ℝ)
    (hrisk : 0 ≤ riskCost) (hbudget : 0 ≤ budgetSpend) :
    StepContract where
  decrease := c.drop
  riskCost := riskCost
  budgetSpend := budgetSpend
  hDecreasePos := le_of_lt c.drop_pos
  hRiskNonneg := hrisk
  hBudgetNonneg := hbudget

/-- Композиция сохраняет связку измерения: цепочка
ExecutedCert со значениями risk/budget даёт посылки
trajectory_convergence без дополнительных гипотез. -/
theorem ec_chain_to_tc {S : Type} {obj : S → ℝ} {step : S → S}
    {s : S}
    (f : ℕ → S) (hf : ∀ t, f (t + 1) = step (f t)) (h0 : f 0 = s)
    (ms ds risks budgets : ℕ → ℝ)
    (cs : ∀ t, Hagi.Unified.ExecutedCert.ExecutedCert
      obj step (f t) (ms t) (ds t))
    (hrisks : ∀ t, 0 ≤ risks t) (hbudgets : ∀ t, 0 ≤ budgets t)
    (Emin : ℝ) (hE : ∀ t : ℕ, Emin ≤ obj (f t)) (T : ℕ) :
    ∑ t : Fin T, (ecToSc (cs t.val) (risks t.val)
      (budgets t.val) (hrisks t.val) (hbudgets t.val)).decrease
      ≤ obj (f 0) - Emin
        + ∑ t : Fin T, risks t.val := by
  have hstep : ∀ t : Fin T, obj (f (t.val + 1))
      ≤ obj (f t.val)
      - (ecToSc (cs t.val) (risks t.val) (budgets t.val)
          (hrisks t.val) (hbudgets t.val)).decrease
      + (ecToSc (cs t.val) (risks t.val) (budgets t.val)
          (hrisks t.val) (hbudgets t.val)).riskCost := by
    intro t
    have h1 := (cs t.val).actual
    have h2 : f (t.val + 1) = step (f t.val) := hf t.val
    show obj (f (t.val+1)) ≤ obj (f t.val)
      - (ecToSc (cs t.val) (risks t.val) (budgets t.val)
          (hrisks t.val) (hbudgets t.val)).decrease
      + (ecToSc (cs t.val) (risks t.val) (budgets t.val)
          (hrisks t.val) (hbudgets t.val)).riskCost
    simp only [ecToSc]
    rw [show obj (f (t.val+1)) = obj (step (f t.val)) from congrArg obj h2]
    linarith [h1, hrisks t.val]
  have hchain : ∀ t : Fin T,
      obj (f (t.val + 1)) ≤ obj (f t.val)
      - (ecToSc (cs t.val) (risks t.val) (budgets t.val)
          (hrisks t.val) (hbudgets t.val)).decrease
      + (ecToSc (cs t.val) (risks t.val) (budgets t.val)
          (hrisks t.val) (hbudgets t.val)).riskCost := hstep
  have := trajectory_convergence
    (fun t => ecToSc (cs t.val) (risks t.val) (budgets t.val)
      (hrisks t.val) (hbudgets t.val))
    (fun k => obj (f k)) Emin hchain
    (fun k _ => hE k)
  simpa [ecToSc] using this

end Hagi.Unified.CertUnify

/-!
# Семейственный телескоп CertifiedTransitionV2

Кумулятивная связь между прогрессом сертификатов и
реальной энергией ВЫВОДИТСЯ из поштучных сертификатов
перехода с операциональными условиями спуска: гипотеза
телескопа становится теоремой. Каждый шаг честен по
`ctv2Honest`; индукция по горизонту собирает телескоп.
-/

namespace Hagi.Unified.Ctv2Telescope

open Hagi.Model Hagi.System Hagi.Unified.CertUnify Hagi.Unified.HonestTransition
open InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Заявленный спуск шага (тот же, что у сертификата). -/
noncomputable def stepDrop (u : StageInput X) : ℝ :=
  u.eff.growGain + u.gap
    + (u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
      - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2)
    - u.sp.kappa * u.sp.s * u.eff.quantErr

/-- ГЛАВНАЯ ТЕОРЕМА: из поштучных сертификатов перехода с
операциональными условиями спуска выводится кумулятивный
телескоп — сумма заявленных спусков не превосходит
реального убывания энергии. -/
theorem ctv2_family_telescope
    (S : ℕ → Hagi.System.GrowthState X)
    (u : ℕ → StageInput X) (riskLim : ℝ) (T : ℕ)
    (hexec : ∀ t, S (t + 1) = advance (S t) (u t))
    (hc : ∀ t, CertifiedTransitionV2 (S t) (advance (S t) (u t))
      (u t) riskLim)
    (hgain : ∀ t, (u t).eff.growEnergy
      ≤ (S t).energy - (u t).eff.growGain)
    (hgap0 : ∀ t, 0 ≤ (u t).gap)
    (hmerge : ∀ t, (u t).eff.mergeEnergy
      ≤ (u t).eff.growEnergy - (u t).gap)
    (hL : ∀ t, 0 < (u t).sp.L)
    (heta : ∀ t, (u t).sp.eta ≤ 1 / (u t).sp.L)
    (hdesc : ∀ t, ‖(u t).stepDir‖ ^ 2
      ≤ ⟪(u t).grad, (u t).stepDir⟫_ℝ)
    (hjoint : ∀ t, (u t).eff.jointEnergy
      ≤ (u t).eff.mergeEnergy
        - (u t).sp.eta * ⟪(u t).grad, (u t).stepDir⟫_ℝ
        + (u t).sp.L * (u t).sp.eta ^ 2
          * ‖(u t).stepDir‖ ^ 2 / 2)
    (hledger : ∀ t, (u t).eff.compressEnergy
        - (u t).eff.jointEnergy
      ≤ (u t).sp.kappa * (u t).sp.s * (u t).eff.quantErr) :
    ∑ t ∈ Finset.range T, stepDrop (u t)
      ≤ (S 0).energy - (S T).energy := by
  have hstep : ∀ t, (S (t + 1)).energy
      ≤ (S t).energy - stepDrop (u t) := by
    intro t
    have hd := Hagi.Model.advance_energy_drop (S t) (u t)
      (hgain t) (hgap0 t) (hmerge t) (hL t) (heta t)
      (hdesc t) (hjoint t) (hledger t)
    rw [hexec t]
    have hE : (advance (S t) (u t)).energy
        = (u t).eff.compressEnergy := rfl
    rw [hE]
    unfold stepDrop
    linarith
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have hs := hstep T
    linarith

/-- МОСТ ПОКАЗАТЕЛЬ ↔ ЧЕСТНЫЙ СПУСК: при выровненном
направлении, корректном шаге и ошибке квантования в
половину сетки честный спуск шага не меньше показателя
verify нового состояния. -/
theorem stepDrop_ge_verify (S : Hagi.System.GrowthState X)
    (u : StageInput X)
    (heta0 : 0 ≤ u.sp.eta)
    (hdesc : ‖u.stepDir‖ ^ 2 ≤ ⟪u.grad, u.stepDir⟫_ℝ)
    (hL : 0 < u.sp.L) (heta : u.sp.eta ≤ 1 / u.sp.L)
    (hkappa : 0 ≤ u.sp.kappa) (hs : 0 ≤ u.sp.s)
    (hq : u.eff.quantErr ≤ 1 / 2) :
    (Hagi.System.verify (advance S u)).decrease ≤ stepDrop u := by
  unfold Hagi.System.verify Hagi.System.gainJoint stepDrop
  simp only [Hagi.Model.advance]
  have hd2 : (0:ℝ) ≤ ‖u.stepDir‖ ^ 2 := by positivity
  have key : u.sp.eta * ‖u.stepDir‖ ^ 2 / 2
      ≤ u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ
        - u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2 / 2 := by
    have h1 : u.sp.eta * ‖u.stepDir‖ ^ 2
        ≤ u.sp.eta * ⟪u.grad, u.stepDir⟫_ℝ := by
      nlinarith [mul_le_mul_of_nonneg_left hdesc heta0]
    have h2 : u.sp.L * u.sp.eta ^ 2 * ‖u.stepDir‖ ^ 2
        ≤ u.sp.eta * ‖u.stepDir‖ ^ 2 := by
      have hLeta : u.sp.L * u.sp.eta ≤ 1 := by
        have := (le_div_iff₀ hL).mp heta
        linarith
      nlinarith [mul_nonneg heta0 hd2,
        mul_le_mul_of_nonneg_right hLeta hd2]
    field_simp
    linarith
  have hq2 : u.sp.kappa * u.sp.s * u.eff.quantErr
      ≤ u.sp.kappa * u.sp.s / 2 := by
    have hk := mul_nonneg hkappa hs
    have := mul_le_mul_of_nonneg_left hq hk
    rw [mul_div_assoc'] at this
    norm_num at this
    linarith
  linarith

/-- СЛЕДСТВИЕ: телескоп в форме показателей verify выводится
из тех же поштучных условий — гипотеза кумулятивного
прогресса для семейства переходов является теоремой. -/
theorem verify_family_telescope
    (S : ℕ → Hagi.System.GrowthState X)
    (u : ℕ → StageInput X) (riskLim : ℝ) (T : ℕ)
    (hexec : ∀ t, S (t + 1) = advance (S t) (u t))
    (hc : ∀ t, CertifiedTransitionV2 (S t) (advance (S t) (u t))
      (u t) riskLim)
    (hgain : ∀ t, (u t).eff.growEnergy
      ≤ (S t).energy - (u t).eff.growGain)
    (hgap0 : ∀ t, 0 ≤ (u t).gap)
    (hmerge : ∀ t, (u t).eff.mergeEnergy
      ≤ (u t).eff.growEnergy - (u t).gap)
    (hL : ∀ t, 0 < (u t).sp.L)
    (heta : ∀ t, (u t).sp.eta ≤ 1 / (u t).sp.L)
    (heta0 : ∀ t, 0 ≤ (u t).sp.eta)
    (hdesc : ∀ t, ‖(u t).stepDir‖ ^ 2
      ≤ ⟪(u t).grad, (u t).stepDir⟫_ℝ)
    (hjoint : ∀ t, (u t).eff.jointEnergy
      ≤ (u t).eff.mergeEnergy
        - (u t).sp.eta * ⟪(u t).grad, (u t).stepDir⟫_ℝ
        + (u t).sp.L * (u t).sp.eta ^ 2
          * ‖(u t).stepDir‖ ^ 2 / 2)
    (hledger : ∀ t, (u t).eff.compressEnergy
        - (u t).eff.jointEnergy
      ≤ (u t).sp.kappa * (u t).sp.s * (u t).eff.quantErr)
    (hkappa : ∀ t, 0 ≤ (u t).sp.kappa)
    (hs : ∀ t, 0 ≤ (u t).sp.s)
    (hq : ∀ t, (u t).eff.quantErr ≤ 1 / 2) :
    ∑ t ∈ Finset.range T, (Hagi.System.verify (S (t + 1))).decrease
      ≤ (S 0).energy - (S T).energy := by
  have htele := ctv2_family_telescope S u riskLim T hexec hc
    hgain hgap0 hmerge hL heta hdesc hjoint hledger
  have hle : ∀ t ∈ Finset.range T,
      (Hagi.System.verify (S (t + 1))).decrease ≤ stepDrop (u t) := by
    intro t ht
    rw [hexec t]
    exact stepDrop_ge_verify (S t) (u t) (heta0 t) (hdesc t)
      (hL t) (heta t) (hkappa t) (hs t) (hq t)
  calc ∑ t ∈ Finset.range T, (Hagi.System.verify (S (t + 1))).decrease
      ≤ ∑ t ∈ Finset.range T, stepDrop (u t) :=
        Finset.sum_le_sum hle
    _ ≤ (S 0).energy - (S T).energy := htele

end Hagi.Unified.Ctv2Telescope
