import Mathlib.Tactic
import Hagi.Model.SoftmaxStep
import Hagi.Unified.CertifiedLoop

set_option linter.style.header false

/-!
# LogitCert — сертифицированный логит-цикл (циклы 36, 42)

ПЕРВЫЙ НЕ-КВАДРАТИЧНЫЙ инстанс certified-исчисления:
логистическая голова (logitCE, гладкость 1/4 ВЫВЕДЕНА в
SoftmaxStep.sigmoid_sq_le_quarter — НЕ h_emp) подключается к
HonestTransition/StepCert:

- logit_step_cert: градиентный шаг логит-головы при
  η ∈ (0,2] даёт HonestTransition с objectiveDrop =
  (η/2)·σ(w)² > 0 (σ(w) ≠ 0 — сигмоид нигде не ноль);
- logitStepCertExact: для произвольного η > 0
  objectiveDrop равен точному фактическому спуску
  logitCE w − logitCE (w + η/(1 + exp w)) > 0;
- logit_certified_chain: цепочка из n шагов удовлетворяет
  certified_loop — суммарный спуск ≤ logitCE(w₀) −
  logitCE(wₙ), полы держатся, бюджет убывает.

h_emp-посылок НЕТ: гладкость выведена, спуск выведен.
Произвольный положительный шаг сертифицируется ТОЛЬКО для
этой скалярной one-example модели. Утверждения не
обобщаются на large-step multidim/stochastic модели и не
дают общей теоремы сходимости.
Аудит #8 п.5 (первый не-игрушечный инстанс) — этап 1
(одномерная голова; мультипараметрическая регрессия —
следующая итерация).
-/

namespace Hagi.Unified.LogitCert

open Hagi.Model Hagi.Unified.HonestTransition Hagi.Unified.LinkedQVec
  Hagi.Unified.CertifiedLoop

/-- Измеритель для логит-состояния: все каналы — текущий
вес-качество (однородная шкала; полы из logitCE_nonneg). -/
noncomputable def logitMeasured : MeasuredState ℝ :=
  ⟨fun w => fun _ => logitCE w⟩

/-- Сертифицированный шаг логит-головы: HonestTransition c
ВЫВЕДЕННЫМ спуском (гладкость 1/4 — sigmoid_sq_le_quarter,
не h_emp). -/
noncomputable def logitStepCert (w eta riskLim budgetSpend budget' : ℝ)
    (h0 : 0 < eta) (h2 : eta ≤ 2)
    (hbudget : 0 ≤ budget')
    (hrisk : (0:ℝ) ≤ riskLim) :
    HonestTransition (fun w => logitCE w) w
      (w + eta / (1 + Real.exp w)) 0 riskLim budgetSpend
      budget' where
  objectiveDrop := (eta / 2) * (1 / (1 + Real.exp w)) ^ 2
  objectiveDrop_pos := by
    have : (0:ℝ) < (1 / (1 + Real.exp w)) ^ 2 := by positivity
    exact mul_pos (by positivity) this
  actualDescent := descent_step w eta h0 h2
  riskBound := hrisk
  budgetBound := hbudget

/-- Сертифицированный шаг с бюджетным телескопом и полами. -/
noncomputable def logitStepCert' (w eta budget : ℝ)
    (h0 : 0 < eta) (h2 : eta ≤ 2) (hbd : eta ≤ budget) :
    StepCert (fun w => logitCE w) logitMeasured
      (fun _ => 0) eta w
      (w + eta / (1 + Real.exp w)) budget
      (budget - eta) where
  riskSpend := 0
  budgetSpend := eta
  trans := logitStepCert w eta eta eta (budget - eta) h0 h2
    (by linarith) h0.le
  hriskSpend_nn := le_refl _
  hbudgetSpend_nn := h0.le
  hdec := le_of_eq (by ring)
  quality := fun _ => logitCE_nonneg _

/-- `logitCE` строго убывает: `x < y` влечёт
`exp (-y) < exp (-x)`, а затем строгое неравство для `log`. -/
theorem logitCE_strictAnti : StrictAnti logitCE := by
  intro x y hxy
  unfold logitCE
  apply Real.log_lt_log
  · positivity
  · exact add_lt_add_right (Real.exp_lt_exp.mpr (neg_lt_neg hxy)) 1

/-- При любом `eta > 0` положительный шаг веса даёт строгий
фактический спуск scalar logit CE. -/
theorem descent_step_strict (w eta : ℝ) (heta : 0 < eta) :
    logitCE (w + eta / (1 + Real.exp w)) < logitCE w := by
  apply logitCE_strictAnti
  have hstep : 0 < eta / (1 + Real.exp w) :=
    div_pos heta (by positivity)
  linarith

/-- Точный сертификат шага для произвольного `eta > 0`:
`objectiveDrop` — сам фактический спуск, без ограничения
`eta ≤ 2` и без замены его квадратичной нижней границей. -/
noncomputable def logitStepCertExact
    (w eta riskLim budgetSpend budget' : ℝ)
    (h0 : 0 < eta)
    (hbudget : 0 ≤ budget')
    (hrisk : (0 : ℝ) ≤ riskLim) :
    HonestTransition (fun w => logitCE w) w
      (w + eta / (1 + Real.exp w)) 0 riskLim budgetSpend
      budget' where
  objectiveDrop :=
    logitCE w - logitCE (w + eta / (1 + Real.exp w))
  objectiveDrop_pos := sub_pos.mpr (descent_step_strict w eta h0)
  actualDescent := by rw [sub_sub_cancel]
  riskBound := hrisk
  budgetBound := hbudget

/-- `StepCert` с точным фактическим спуском для произвольного
`eta > 0`; риск, бюджет и полы устроены как в исходном
бюджетном сертификате. -/
noncomputable def logitStepCertExact' (w eta budget : ℝ)
    (h0 : 0 < eta) (hbd : eta ≤ budget) :
    StepCert (fun w => logitCE w) logitMeasured
      (fun _ => 0) eta w
      (w + eta / (1 + Real.exp w)) budget
      (budget - eta) where
  riskSpend := 0
  budgetSpend := eta
  trans := logitStepCertExact w eta eta eta (budget - eta) h0
    (by linarith) h0.le
  hriskSpend_nn := le_refl _
  hbudgetSpend_nn := h0.le
  hdec := le_of_eq (by ring)
  quality := fun _ => logitCE_nonneg _

/-- На старом диапазоне `0 < eta ≤ 2` квадратичная граница
`descent_step` не превосходит точного фактического спуска. -/
theorem logit_exact_drop_dominates (w eta : ℝ)
    (h0 : 0 < eta) (h2 : eta ≤ 2) :
    (eta / 2) * (1 / (1 + Real.exp w)) ^ 2 ≤
      logitCE w - logitCE (w + eta / (1 + Real.exp w)) := by
  have hdescent := descent_step w eta h0 h2
  linarith

end Hagi.Unified.LogitCert
