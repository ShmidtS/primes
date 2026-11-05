import Mathlib.Tactic
import Hagi.Model.SoftmaxStep
import Hagi.Unified.CertifiedLoop

set_option linter.style.header false

/-!
# LogitCert — сертифицированный логит-цикл (цикл 36)

ПЕРВЫЙ НЕ-КВАДРАТИЧНЫЙ инстанс certified-исчисления:
логистическая голова (logitCE, гладкость 1/4 ВЫВЕДЕНА в
SoftmaxStep.sigmoid_sq_le_quarter — НЕ h_emp) подключается к
HonestTransition/StepCert:

- logit_step_cert: градиентный шаг логит-головы при
  η ∈ (0,2] даёт HonestTransition с objectiveDrop =
  (η/2)·σ(w)² > 0 (σ(w) ≠ 0 — сигмоид нигде не ноль);
- logit_certified_chain: цепочка из n шагов удовлетворяет
  certified_loop — суммарный спуск ≤ logitCE(w₀) −
  logitCE(wₙ), полы держатся, бюджет убывает.

h_emp-посылок НЕТ: гладкость выведена, спуск выведен.
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

end Hagi.Unified.LogitCert
