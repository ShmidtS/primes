/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Hagi.Model.CertifiedTransition
import Hagi.Unified.HonestTransition
import Hagi.Unified.StepContract

set_option linter.style.header false

/-!
# TransitionCert — ЕДИНЫЙ сертификат перехода (аудит v18 P0)

Пять контрактов перехода повторяют одни понятия. Единый
generic-тип `TransitionCert`; GrowthState-контракт V3 —
частный случай; единый телескоп `certs_telescope` закрывает
кумулятивные trajectory-теоремы один раз для всех носителей.
-/

namespace Hagi.Unified.TC

variable {State : Type*}

/-- ЕДИНЫЙ СЕРТИФИКАТ ПЕРЕХОДА. -/
structure TransitionCert (obj risk : State → ℝ)
    (step : State → State) (s : State) (riskLim : ℝ) where
  /-- Фактический спад objective (строгий). -/
  actual_descent : obj (step s) < obj s
  /-- Риск в лимите: пост-риск ≤ пре-риск + riskLim. -/
  risk_bound : risk (step s) ≤ risk s + riskLim

/-- КОНВЕРСИЯ V3 → unified. -/
theorem of_ctv3 {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X]
    (S : Hagi.System.GrowthState X) (u : Hagi.Model.StageInput X)
    (riskLim : ℝ) (hc : Hagi.Model.CertifiedTransitionV3 S
      (Hagi.Model.advance S u) u riskLim) :
    TransitionCert (fun St : Hagi.System.GrowthState X => St.energy)
      (fun St => St.protectedRisk)
      (fun St => Hagi.Model.advance St u) S riskLim where
  actual_descent := hc.hActualDescent
  risk_bound := by
    have h := hc.hRiskLim
    linarith

/-- ЕДИНЫЙ ТЕЛЕСКОП: T шагов по цепочке x(t+1) = step (x t) с
сертификатом на каждом шаге. Итог: objective кумулятивно
убывает (строго при T ≥ 1 через фактический спад первого
шага), риск суммируется в лимите. -/
theorem certs_telescope {obj risk : State → ℝ}
    (step : State → State) (x : ℕ → State) (riskLim : ℝ)
    (T : ℕ) (hchain : ∀ t : ℕ, t < T → x (t + 1) = step (x t))
    (certs : ∀ t : ℕ, t < T →
      TransitionCert obj risk step (x t) riskLim) :
    (0 < T → obj (x T) < obj (x 0)) ∧
    risk (x T) ≤ risk (x 0) + (T:ℝ) * riskLim := by
  revert certs hchain
  induction T with
  | zero =>
    intro certs _
    exact ⟨fun h => absurd h (by omega), by simp⟩
  | succ T ih =>
    intro hchain certs
    have ihc := ih
      (fun t ht => hchain t (Nat.lt_of_lt_of_le ht
        (Nat.le_succ T)))
      (fun t ht => certs t (Nat.lt_of_lt_of_le ht
        (Nat.le_succ T)))
    obtain ⟨hcond, hrisk⟩ := ihc
    have hc := certs T (Nat.lt_succ_self T)
    have hchain' : x (T + 1) = step (x T) :=
      hchain T (Nat.lt_succ_self T)
    -- objective: строгое убывание по цепочке
    have hdesc := hc.actual_descent
    have hstrict : obj (x (T + 1)) < obj (x 0) := by
      rcases Nat.eq_zero_or_pos T with hT0 | hTpos
      · subst hT0
        have hc0 := certs 0 (by norm_num)
        have hch0 : x 1 = step (x 0) :=
          hchain 0 (by norm_num)
        rw [hch0]
        exact hc0.actual_descent
      · -- T ≥ 1: ih даёт строгий спад до x T, плюс шаг hdesc
        have hprev : obj (x T) < obj (x 0) := hcond hTpos
        have hch : x (T + 1) = step (x T) :=
          hchain T (by
            have := Nat.lt_succ_self T
            omega)
        rw [hch]
        exact lt_of_le_of_lt (le_of_lt hdesc) hprev
    have hgoal1 : obj (x (T + 1)) < obj (x 0) := hstrict
    -- риск: кумулятивная граница
    have hrb := hc.risk_bound
    have hrisk' : risk (x (T + 1))
        ≤ risk (x 0) + ((T:ℝ) + 1) * riskLim := by
      have h1 : risk (step (x T)) ≤ risk (x T) + riskLim := hrb
      have h1' : risk (x (T + 1)) ≤ risk (x T) + riskLim := by
        rw [hchain']
        exact h1
      have h2 : risk (x T) ≤ risk (x 0)
          + (T:ℝ) * riskLim := hrisk
      have hcast : ((T:ℝ) + 1) * riskLim
          = ((T + 1:ℕ):ℝ) * riskLim := by
        push_cast [Nat.cast_succ]
        ring
      rw [hcast]
      linarith
    have hcast : ((T:ℝ) + 1) * riskLim
        = ((T + 1:ℕ):ℝ) * riskLim := by
      push_cast [Nat.cast_succ]
      ring
    exact ⟨fun _ => hgoal1, by
      have h := hrisk'
      rw [hcast] at h
      exact h⟩


/-! ### Мост в ядро CertStep (цикл 41) -/

/-- TransitionCert → CertStep: строгий спад даёт drop =
obj s − obj (step s) > 0 — ядро с ТОЧНЫМ спуском. -/
noncomputable def TransitionCert.toCertStep {obj risk : State → ℝ}
    {step : State → State} {s : State} {riskLim : ℝ}
    (C : TransitionCert obj risk step s riskLim) :
    Hagi.Unified.HonestTransition.CertStep obj s (step s) where
  drop := obj s - obj (step s)
  drop_pos := by linarith [C.actual_descent]
  actual := by linarith [C.actual_descent]

end Hagi.Unified.TC

/-! ### Мост CertifiedTransitionV2 → StepContract
(перенесён из Unified.TransitionContract, консолидация). -/

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
