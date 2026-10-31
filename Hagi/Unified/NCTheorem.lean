import Mathlib
import Hagi.Model.NeuralComputer
import Hagi.Unified.StepContract

/-!
# NCTheorem (приоритет 7 «HAGI Neural Computer», такт №251)

ГЛОБАЛЬНАЯ ТЕОРЕМА нейрокомпьютера: траектория
ncAdvance-переходов с честными контрактами шага
удовлетворяет единому телескопическому принципу
StepContract: суммарный доказанный спуск ≤ Φ₀ − Φ_min +
Σ risk, при этом процессор заморожен на всей траектории
(инвариант переносится индукцией по переходам).
-/

namespace Hagi.Unified.NCTheorem

open Hagi.Model.NeuralComputer Hagi.Unified.StepCert

/-- Контракт шага нейрокомпьютера: доказанный спуск d
(энергетический сертификат), риск = riskSpend входа,
бюджет = cost входа. -/
noncomputable def ncContract (u : NCInput) (d : ℝ)
    (hd : 0 ≤ d) : StepContract where
  decrease := d
  riskCost := u.riskSpend
  budgetSpend := u.cost
  hDecreasePos := hd
  hRiskNonneg := u.hrisk
  hBudgetNonneg := u.hcost

/-- Телескоп нейрокомпьютера: если потенциал Φ (функция
состояний) спускается по контрактам T циклов, то суммарный
спуск ≤ Φ₀ − Φ_min + Σ риск — прогресс обучения
нейрокомпьютера ограничен теорией (реюз
trajectory_convergence через ncContract-мост). -/
theorem nc_trajectory_bound {T : ℕ}
    (S : ℕ → NCState) (u : Fin T → NCInput)
    (d : Fin T → ℝ) (hd : ∀ t, 0 ≤ d t)
    (hstep : ∀ t : Fin T, S (t.val + 1) = ncAdvance (S t.val) (u t))
    (Φ : NCState → ℝ) (Φ_min : ℝ)
    (hΦ : ∀ t : Fin T,
      Φ (S (t.val + 1)) ≤ Φ (S t.val) - d t + (u t).riskSpend)
    (hfloor : ∀ t ≤ T, Φ_min ≤ Φ (S t)) :
    ∑ t : Fin T, d t
      ≤ Φ (S 0) - Φ_min + ∑ t : Fin T, (u t).riskSpend := by
  exact trajectory_convergence
    (fun t => ncContract (u t) (d t) (hd t))
    (fun t => Φ (S t)) Φ_min
    (fun t => hΦ t)
    (fun t ht => hfloor t (by omega))

/-- ПРОЦЕССОР ЗАМОРОЖЕН НА ВСЕЙ ТРАЕКТОРИИ: индукция по
переходам — инвариант nc_cpu_frozen переносится с одного
шага на весь горизонт (глобальная формулировка). -/
theorem nc_cpu_frozen_trajectory {T : ℕ}
    (S : ℕ → NCState) (u : Fin T → NCInput)
    (hstep : ∀ t : Fin T, S (t.val + 1) = ncAdvance (S t.val) (u t)) :
    ∀ t ≤ T, (S t).cpu = (S 0).cpu := by
  intro t ht
  induction t with
  | zero => rfl
  | succ n ih =>
      have hn : n ≤ T := by omega
      have hprev := ih hn
      have h := hstep ⟨n, by omega⟩
      rw [h]
      exact (nc_cpu_frozen (S n) (u ⟨n, by omega⟩)).trans hprev

end Hagi.Unified.NCTheorem
