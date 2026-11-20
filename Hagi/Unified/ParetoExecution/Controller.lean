/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Growth.SelfDevelopment
import Hagi.Model.StageSemantics
import Mathlib.Tactic
import Hagi.Model.SoftmaxStep
import Hagi.Unified.LogitCert
import Hagi.State.TrainState
import Hagi.Unified.ParetoExecution.Selection
import Mathlib.Data.List.MinMax
set_option linter.style.header false

set_option linter.style.header false

/-!
# ParetoLogit — конечный Pareto-контроллер на реальной
скалярной логистической цели (цикл 72)

Мост между циклами 70/71 (конечный контроллер над РЕАЛЬНЫМИ
преемниками и робастный отбор с ограниченной ошибкой оценки) и
точной логистической сертификацией циклов 36/42 (`logitCE`,
`descent_step_strict`, `logitStepCertExact`, `certified_loop`):

* `logitProblem eta` — конечная задача `Fin 2 → ℝ` с целью
  `-logitCE`: действие 0 — тождественный шаг, действие 1 —
  РЕАЛЬНЫЙ градиентный шаг `w + eta/(1+exp w)`; память и
  операции — явные модельные единицы (индексы `Fin 2`);
  безопасность каждого действия — фактическое неувеличение CE
  на всех скалярных состояниях (для действия 1 — строгий
  спуск при `eta > 0`, для действия 0 — тождество).
* `logit_selectedNext` — при допустимости обоих действий
  выбранный преемник РОВНО реальный шаг обновления для любого
  состояния и любого `eta > 0`; базовое тождественное действие
  исключается именно строгим улучшением CE.
* `logitEstimate` — детерминированный пессимистичный
  оцениватель `-logitCE w - 1/2` с ТОЧНОЙ ошибкой `1/2`;
  робастный отбор по нему всё равно исполняет реальный шаг
  (порядок оценок совпадает с порядком истинных значений).
  Это НЕ стохастическая калибровка, НЕ IID-модель и НЕ гарантия
  для произвольных искажённых оценок за пределами границы.
* `logit_budget_loop` — многошаговый бюджетный сертификат
  через существующий `certified_loop`/`certified_loop_all`/
  `certified_loop_strict` (без дублирующей индукции):
  полы качества на всех состояниях, точный телескоп CE-спусков,
  неотрицательный остаточный бюджет, строгий спуск при `n ≥ 1`.
* `logit_quadratic_bound` — квадратичная гарантия спуска из
  СУЩЕСТВУЮЩЕЙ `logitCE_trajectory_bound` (без второго
  телескопа) при ограниченных шагах `0 < eta t ≤ 2`.

Все утверждения — о данной одномерной one-example модели и
данном конечном семействе действий; это не глобально
оптимальная скорость обучения, не оптимальный нейрооптимизатор,
не минимальное число операций и не общая теория сходимости.
-/

namespace Hagi.Unified.ParetoLogit

open Hagi.Model Hagi.Unified.ParetoExecution Hagi.Unified.LogitCert
  Hagi.Unified.LinkedQVec Hagi.Unified.CertifiedLoop

/-! ### Конечная задача управления с реальной целью `-logitCE` -/

/-- Реальный преемник: действие 1 исполняет точный скалярный
градиентный шаг `w + eta/(1 + exp w)`, действие 0 — тождество. -/
noncomputable def logitStepFun (eta : ℝ) (a : Fin 2) (w : ℝ) : ℝ :=
  if a = 1 then w + eta / (1 + Real.exp w) else w

@[simp] theorem logitStepFun_zero (eta : ℝ) (w : ℝ) :
    logitStepFun eta 0 w = w := by
  simp [logitStepFun]

@[simp] theorem logitStepFun_one (eta : ℝ) (w : ℝ) :
    logitStepFun eta 1 w = w + eta / (1 + Real.exp w) := by
  simp [logitStepFun]

/-- Безопасность действия — ФАКТИЧЕСКОЕ неувеличение CE
преемника на всех скалярных состояниях (не безусловное
`True`): для действия 1 это строгий спуск при `eta > 0`,
для действия 0 — тождество. -/
def logitSafe (eta : ℝ) (a : Fin 2) : Prop :=
  ∀ w : ℝ, logitCE (logitStepFun eta a w) ≤ logitCE w

theorem logitSafe_zero (eta : ℝ) : logitSafe eta 0 := by
  intro w
  rw [logitStepFun_zero]

theorem logitSafe_one (eta : ℝ) (heta : 0 < eta) : logitSafe eta 1 := by
  intro w
  exact le_of_lt (descent_step_strict w eta heta)

/-- Именованный некомпьютабельный DecidablePred-инстанс
безопасности (через Classical.propDecidable). -/
noncomputable instance logitSafeDecidable (eta : ℝ) :
    DecidablePred (logitSafe eta) :=
  fun _ => Classical.propDecidable _

/-- Конечная задача управления over `Fin 2` и скалярного состояния:
цель в точности `-logitCE`, шаг — реальный преемник модели,
память/операции — явные модельные единицы (счётчики индексов). -/
noncomputable def logitProblem (eta : ℝ) : ControllerProblem (Fin 2) ℝ where
  value := fun w => -logitCE w
  step := logitStepFun eta
  memory := fun a => a.val
  operations := fun a => 2 * a.val
  safe := logitSafe eta

noncomputable instance logitProblemSafeDecidable (eta : ℝ) :
    DecidablePred (logitProblem eta).safe :=
  fun _ => Classical.propDecidable _

@[simp] theorem logitProblem_value (eta w : ℝ) :
    (logitProblem eta).value w = -logitCE w := rfl

@[simp] theorem logitProblem_step (eta : ℝ) (a : Fin 2) (w : ℝ) :
    (logitProblem eta).step a w = logitStepFun eta a w := rfl

/-- Допустимость тождественного действия при любых лимитах. -/
theorem logit_feasible_zero (eta : ℝ) (M C : ℕ) :
    (0 : Fin 2) ∈ feasible (logitProblem eta) M C := by
  refine mem_feasible.mpr ⟨logitSafe_zero eta, ?_, ?_⟩ <;>
    simp [logitProblem]

/-- Допустимость реального шага обновления при `eta > 0` и
достаточных лимитах (память 1, операции 2 — модельные
единицы действия 1). -/
theorem logit_feasible_one (eta : ℝ) (heta : 0 < eta) (M C : ℕ)
    (hM : 1 ≤ M) (hC : 2 ≤ C) :
    (1 : Fin 2) ∈ feasible (logitProblem eta) M C := by
  refine mem_feasible.mpr ⟨logitSafe_one eta heta, ?_, ?_⟩ <;>
    simp [logitProblem] <;> omega

/-! ### Точный отбор: преемник — реальный шаг обновления -/

/-- При допустимости обоих действий выбранный преемник РОВНО
реальный шаг `w + eta/(1+exp w)` для ЛЮБОГО состояния `w` и
любого `eta > 0`. Базовое тождественное действие исключается
именно строгим улучшением CE (`descent_step_strict`), а не
схемой перебора. Утверждение — о данном конечном семействе,
не о глобально оптимальной скорости обучения. -/
theorem logit_selection_eq_one (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    selection (logitProblem eta) w M C 0 h0 = 1 := by
  apply selection_eq_one_of_value_lt (logitProblem eta) w M C h0 h1
  simp only [logitProblem_value, logitProblem_step, logitStepFun_zero,
    logitStepFun_one]
  have hdesc := descent_step_strict w eta heta
  linarith

/-- Выбранный преемник равен точному реальному шагу
обновления — при всех ресурсных предпосылках, оставшихся
видимыми (`h0`, `h1`). -/
theorem logit_selectedNext (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    selectedNext (logitProblem eta) w M C 0 h0
      = w + eta / (1 + Real.exp w) := by
  unfold selectedNext
  rw [logit_selection_eq_one eta heta w M C h0 h1]
  exact logitStepFun_one eta w

/-- Выбранный преемник строго снижает CE (одношаговый отбор
качества общего вида — по любому состоянию, не только по
константному). -/
theorem logit_selected_strict (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    logitCE (selectedNext (logitProblem eta) w M C 0 h0) < logitCE w := by
  rw [logit_selectedNext eta heta w M C h0 h1]
  exact descent_step_strict w eta heta

/-! ### Робастный отбор с детерминированным пессимистичным
оценивателем (ошибка ровно 1/2; не стохастика и не IID) -/

/-- Оцениватель: истинная цель плюс постоянный
пессимистичный сдвиг `-1/2`. Детерминированная функция
состояния; НЕ стохастическая уверенность и НЕ выборка. -/
noncomputable def logitEstimate (w : ℝ) : ℝ := -logitCE w - 1 / 2

/-- Абсолютная ошибка оценивателя ТОЧНО равна `1/2` в каждом
состоянии. -/
theorem logitEstimate_error (w : ℝ) :
    |-logitCE w - logitEstimate w| = 1 / 2 := by
  unfold logitEstimate
  norm_num

/-- Ошибка оценивателя ровно `1/2` на всех преемниках всех
действий задачи (конечное семейство). -/
theorem logitEstimate_error_action (eta : ℝ) (a : Fin 2) (w : ℝ) :
    |(logitProblem eta).value ((logitProblem eta).step a w)
      - logitEstimate ((logitProblem eta).step a w)| = 1 / 2 :=
  logitEstimate_error _

/-- При допустимости обоих действий робастный отбор по
оценивателю с постоянным сдвигом снова исполняет РЕАЛЬНЫЙ
шаг обновления: порядок оценок совпадает с порядком истинных
значений цели. -/
theorem logit_robust_selection_eq_one (eta : ℝ) (heta : 0 < eta)
    (w : ℝ) (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    selection (withEstimatedValue (logitProblem eta) logitEstimate)
      w M C 0 ((mem_feasible_withEstimatedValue _ _).mpr h0) = 1 := by
  have hm0 : (0 : Fin 2) ∈ feasible
      (withEstimatedValue (logitProblem eta) logitEstimate) M C :=
    (mem_feasible_withEstimatedValue _ _).mpr h0
  apply selection_eq_one_of_value_lt
    (withEstimatedValue (logitProblem eta) logitEstimate) w M C hm0
    ((mem_feasible_withEstimatedValue _ _).mpr h1)
  change logitEstimate ((logitProblem eta).step 0 w) <
    logitEstimate ((logitProblem eta).step 1 w)
  simp only [logitProblem_step, logitStepFun_zero, logitStepFun_one]
  unfold logitEstimate
  have hdesc := descent_step_strict w eta heta
  linarith

/-- Робастный преемник — реальный скалярный шаг обновления,
следовательно строгий спуск CE. -/
theorem logit_robustNext (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    robustNext (logitProblem eta) logitEstimate w M C 0 h0
      = w + eta / (1 + Real.exp w) := by
  have hsel := logit_robust_selection_eq_one eta heta w M C h0 h1
  change (withEstimatedValue (logitProblem eta) logitEstimate).step
    (selection (withEstimatedValue (logitProblem eta) logitEstimate) w M C 0
      ((mem_feasible_withEstimatedValue _ _).mpr h0)) w = _
  rw [hsel]
  exact logitStepFun_one eta w

theorem logit_robust_strict (eta : ℝ) (heta : 0 < eta) (w : ℝ)
    (M C : ℕ) (h0 : (0 : Fin 2) ∈ feasible (logitProblem eta) M C)
    (h1 : (1 : Fin 2) ∈ feasible (logitProblem eta) M C) :
    logitCE (robustNext (logitProblem eta) logitEstimate w M C 0 h0)
      < logitCE w := by
  rw [logit_robustNext eta heta w M C h0 h1]
  exact descent_step_strict w eta heta

/-- При нулевых лимитах единственно допустимо тождественное
действие: робастный запасной итог — исходное состояние
(независимо от оценивателя; за пределами этих явных лимитов
неубывание базы для произвольных искажённых оценок НЕ
выводится). -/
theorem logit_robustNext_fallback (eta : ℝ) (w : ℝ) :
    robustNext (logitProblem eta) logitEstimate w 0 0 0
      (logit_feasible_zero eta 0 0) = w := by
  refine robustNext_fallback (logitProblem eta) logitEstimate w 0 0 0
    (logit_feasible_zero eta 0 0) ?_ ?_
  · intro a ha hm
    have hlt : a.val < 2 := a.isLt
    have hne : a.val ≠ 0 := fun h => ha (Fin.ext h)
    have h1 := (mem_feasible.mp hm).2.1
    simp only [logitProblem] at h1
    omega
  · rw [logitProblem_step]
    exact logitStepFun_zero eta w

/-! ### Многошаговый бюджетный сертификат через certified_loop -/

/-- Локальная (действительно используемая) индукция: из
точного бюджетного телескопа и пошаговых ограничений `eta t ≤ b t`
бюджет неотрицателен на всей цепочке `t ≤ n`. -/
theorem logit_budget_nonneg {n : ℕ} {b eta : ℕ → ℝ} (hb0 : 0 ≤ b 0)
    (htel : ∀ t < n, b (t + 1) = b t - eta t)
    (hle : ∀ t < n, eta t ≤ b t) : ∀ t ≤ n, 0 ≤ b t := by
  intro t
  induction t with
  | zero => intro _; exact hb0
  | succ t ih =>
    intro ht
    have htn : t < n := by omega
    have hbt : 0 ≤ b t := ih (by omega)
    rw [htel t htn]
    have := hle t htn
    linarith

/-- Пошаговый сертификат цепочки: реальный переход
`w t → w (t+1)` с точным фактическим спуском, тратой бюджета
`eta t`, нулевым риском и полами `logitCE ≥ 0` (floor 0 на всех
пяти каналах `logitMeasured`). riskLim = 0 равномерно по цепочке. -/
noncomputable def logitTrajCert (n : ℕ) (w eta b : ℕ → ℝ)
    (hrec : ∀ t < n, w (t + 1) = w t + eta t / (1 + Real.exp (w t)))
    (hpos : ∀ t < n, 0 < eta t)
    (hbnn : ∀ t ≤ n, 0 ≤ b t)
    (hbd : ∀ t < n, b (t + 1) ≤ b t - eta t) (t : Fin n) :
    StepCert (fun w => logitCE w) logitMeasured (fun _ => 0) 0
      (w t.val) (w (t.val + 1)) (b t.val) (b (t.val + 1)) where
  riskSpend := 0
  budgetSpend := eta t.val
  trans :=
    let core := logitStepCertExact (w t.val) (eta t.val) 0 (eta t.val)
      (b (t.val + 1)) (hpos t.val t.isLt)
      (hbnn (t.val + 1) (Nat.succ_le_of_lt t.isLt)) (le_refl 0)
    { objectiveDrop := core.objectiveDrop,
      objectiveDrop_pos := core.objectiveDrop_pos,
      actualDescent := by
        rw [hrec t.val t.isLt]
        exact core.actualDescent,
      riskBound := le_refl 0,
      budgetBound := hbnn (t.val + 1) (Nat.succ_le_of_lt t.isLt) }
  hriskSpend_nn := le_refl 0
  hbudgetSpend_nn := (hpos t.val t.isLt).le
  hdec := hbd t.val t.isLt
  quality := fun _ => logitCE_nonneg _

/-- **Многошаговый бюджетный сертификат логит-цикла** (через
существующие `certified_loop`, `certified_loop_all`,
`certified_loop_strict`; без дублирующей монотонной индукции).
Для точной рекуррентности `w(t+1) = w t + eta t/(1+exp(w t))`,
`0 < eta t ≤ 2`, `0 ≤ b 0`, `b(t+1) = b t − eta t`, `eta t ≤ b t`:
(a) все пять полей качества `logitMeasured` держатся на всех
фактических состояниях `t ≤ n` (в скалярной форме: `0 ≤ logitCE`);
(b) точный телескоп фактических спусков;
(c) неотрицательный остаточный бюджет и бюджетный телескоп
`b n ≤ b 0 − Σ eta t`;
(d) при `n ≥ 1` строгий спуск CE. -/
theorem logit_budget_loop (n : ℕ) (w eta b : ℕ → ℝ)
    (hrec : ∀ t < n, w (t + 1) = w t + eta t / (1 + Real.exp (w t)))
    (heta : ∀ t < n, 0 < eta t ∧ eta t ≤ 2)
    (hb0 : 0 ≤ b 0)
    (htel : ∀ t < n, b (t + 1) = b t - eta t)
    (hle : ∀ t < n, eta t ≤ b t) :
    (∀ t ≤ n, FloorKept logitMeasured (w t) (fun _ => 0))
      ∧ (∀ t ≤ n, 0 ≤ logitCE (w t))
      ∧ (∑ t ∈ Finset.range n, (logitCE (w t) - logitCE (w (t + 1)))
          ≤ logitCE (w 0) - logitCE (w n))
      ∧ (0 ≤ b n ∧ b n ≤ b 0 - ∑ t ∈ Finset.range n, eta t)
      ∧ (1 ≤ n → logitCE (w n) < logitCE (w 0)) := by
  have hpos : ∀ t < n, 0 < eta t := fun t ht => (heta t ht).1
  have hbnn := logit_budget_nonneg hb0 htel hle
  have hbd : ∀ t < n, b (t + 1) ≤ b t - eta t :=
    fun t ht => le_of_eq (htel t ht)
  have h₀ : FloorKept logitMeasured (w 0) (fun _ => 0) :=
    fun _ => logitCE_nonneg _
  have hdrops : ∀ t : Fin n,
      (logitCE (w t.val) - logitCE (w (t.val + 1)))
        = (logitTrajCert n w eta b hrec hpos hbnn hbd t).trans.objectiveDrop :=
    fun t => by
      simp only [logitTrajCert, logitStepCertExact, hrec t.val t.isLt]
  have hspends : ∀ t : Fin n, eta t.val
      = (logitTrajCert n w eta b hrec hpos hbnn hbd t).budgetSpend :=
    fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := certified_loop (fun w => logitCE w)
    logitMeasured (fun _ => 0) 0 w b
    (fun t => logitCE (w t) - logitCE (w (t + 1))) eta n
    h₀ hb0 (logitTrajCert n w eta b hrec hpos hbnn hbd) hdrops hspends
  refine ⟨certified_loop_all (fun w => logitCE w) logitMeasured
    (fun _ => 0) 0 w b (fun t => logitCE (w t) - logitCE (w (t + 1)))
    eta n h₀ hb0 (logitTrajCert n w eta b hrec hpos hbnn hbd) hdrops hspends, ?_, h1, ⟨h3, h4⟩, ?_⟩
  · intro t _
    exact logitCE_nonneg (w t)
  · intro hn
    have hstrict := certified_loop_strict (fun w => logitCE w)
      logitMeasured (fun _ => 0) 0 w b
      (fun t => logitCE (w t) - logitCE (w (t + 1))) n
      h₀ hb0 (logitTrajCert n w eta b hrec hpos hbnn hbd) hdrops hn
    exact hstrict.1

/-! ### Квадратичная гарантия из существующего телескопа -/

/-- Квадратичная гарантия спуска для ограниченных шагов
`0 < eta t ≤ 2` — ПРЯМОЕ переиспользование существующей
`Hagi.Model.logitCE_trajectory_bound` с направлением
`d t = 1/(1+exp(w t))` и его точным `hdir`-тождеством (второй
телескоп не доказывается). -/
theorem logit_quadratic_bound (n : ℕ) (w eta : ℕ → ℝ)
    (hrec : ∀ t < n, w (t + 1) = w t + eta t / (1 + Real.exp (w t)))
    (heta : ∀ t < n, 0 < eta t ∧ eta t ≤ 2) :
    logitCE (w n) ≤ logitCE (w 0)
      - ∑ t ∈ Finset.range n, eta t * (1 / (1 + Real.exp (w t))) ^ 2 / 2 := by
  have hstep : ∀ t < n, w (t + 1)
      = w t + eta t * (1 / (1 + Real.exp (w t))) := by
    intro t ht
    rw [hrec t ht, mul_one_div]
  have hdir : ∀ t < n, (1 / (1 + Real.exp (w t))) ^ 2
      ≤ (-logitGrad (w t)) * (1 / (1 + Real.exp (w t))) := by
    intro t _
    have hgrad : -logitGrad (w t) = 1 / (1 + Real.exp (w t)) := by
      change -(-1 / (1 + Real.exp (w t))) = 1 / (1 + Real.exp (w t))
      field_simp
    rw [hgrad]
    exact le_of_eq (sq (1 / (1 + Real.exp (w t))))
  exact logitCE_trajectory_bound n w eta
    (fun t => 1 / (1 + Real.exp (w t))) hstep heta hdir

end Hagi.Unified.ParetoLogit
set_option linter.style.header false

/-!
# QualityResourceMin — exact minimum model resources under
an objective floor (cycle 73)

This complements the quality-first `ParetoExecution.selection`:
for a finite candidate family, choose a minimum-cost action whose
ACTUAL successor has `qfloor ≤ p.value (p.step a s)`. Feasibility is
the existing conjunction of model safety and both resource caps.

* `qualityEligible` is exactly the existing `feasible` condition plus
  the objective floor; it is not an externally declared desired effect.
* `resourceCost` is `(memory, operations)` in `ℕ ×ₗ ℕ`, explicitly
  memory-first. No arbitrary scalarization mixes different units.
* `exists_minimum_resource` reuses Mathlib's
  `Finset.exists_min_image`; `minimumResource` is the corresponding
  noncomputable `Classical.choose` witness.
* If the eligible set is empty, no witness can be supplied. The API
  does not fabricate a fallback, a quality improvement, or a feasible
  over-budget action.

This is an exact minimum only within the explicitly supplied finite
family and its model cost/objective. It does not certify a global
architecture optimum, minimal search complexity/FLOPs, physical bytes,
hardware latency, task accuracy, or an executable optimizer over ℝ.
-/

namespace Hagi.Unified.QualityResourceMin

open Prod.Lex Hagi.Unified.ParetoExecution

variable {A : Type} {S : Type*}

/-- The explicit memory-first resource cost in declared model units.
Operations decide only memory ties; no mixed scalar objective. -/
def resourceCost (p : ControllerProblem A S) (a : A) : ℕ ×ₗ ℕ :=
  toLex (p.memory a, p.operations a)

/-- An action is eligible if it belongs to the original finite feasible
family AND its actual successor meets the objective floor. -/
def qualityEligible (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a : A) : Prop :=
  a ∈ feasible p M C ∧ qfloor ≤ p.value (p.step a s)

/-- A nonempty eligible finite family has a minimum resource-cost action,
using Mathlib's existing `Finset.exists_min_image`. -/
theorem exists_minimum_resource (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    ∃ a, qualityEligible p s M C qfloor a
      ∧ ∀ b, qualityEligible p s M C qfloor b →
          resourceCost p a ≤ resourceCost p b := by
  classical
  let U := Finset.univ.filter (qualityEligible p s M C qfloor)
  have hne : U.Nonempty :=
    ⟨a0, Finset.mem_filter.mpr ⟨Finset.mem_univ a0, h0⟩⟩
  obtain ⟨a, ha, hmin⟩ :=
    Finset.exists_min_image U (resourceCost p) hne
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro b hb
  exact hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)

/-- Exact finite-family selection at minimum declared resource cost.
The eligible witness excludes the empty-family case; the choice is
mathematical selection, not a certified executable search algorithm. -/
noncomputable def minimumResource (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) : A :=
  Classical.choose (exists_minimum_resource p s M C qfloor a0 h0)

/-- Full specification: the selected action is eligible, and no other
eligible action has smaller resource cost. Cost order is the explicitly
supplied memory-first lexicographic order, not a universal preference. -/
theorem minimumResource_spec (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    qualityEligible p s M C qfloor (minimumResource p s M C qfloor a0 h0)
      ∧ ∀ b, qualityEligible p s M C qfloor b →
          resourceCost p (minimumResource p s M C qfloor a0 h0)
            ≤ resourceCost p b :=
  Classical.choose_spec (exists_minimum_resource p s M C qfloor a0 h0)

/-- The selected action retains the original model safety and both
exact resource caps; no objective-floor exception is introduced. -/
theorem minimumResource_feasible (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    minimumResource p s M C qfloor a0 h0 ∈ feasible p M C :=
  (minimumResource_spec p s M C qfloor a0 h0).1.1

/-- Quality is checked at the ACTUAL successor of the selected action,
not at the witness or at synthesized metadata. -/
theorem minimumResource_next_quality_ge (p : ControllerProblem A S)
    [Fintype A] [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ)
    (a0 : A) (h0 : qualityEligible p s M C qfloor a0) :
    qfloor ≤ p.value (p.step (minimumResource p s M C qfloor a0 h0) s) :=
  (minimumResource_spec p s M C qfloor a0 h0).1.2

/-- No eligible action has smaller declared resource cost than the
chosen action. This is class-relative, and the cost is not physical
measurement or a claim of minimum search time. -/
theorem minimumResource_cost_min (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    ∀ b, qualityEligible p s M C qfloor b →
      resourceCost p (minimumResource p s M C qfloor a0 h0)
        ≤ resourceCost p b :=
  (minimumResource_spec p s M C qfloor a0 h0).2

/-- The selected action retains the original model-level safety predicate.
This does not identify that predicate with physical safety. -/
theorem minimumResource_safe (p : ControllerProblem A S) [Fintype A]
    [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ) (a0 : A)
    (h0 : qualityEligible p s M C qfloor a0) :
    p.safe (minimumResource p s M C qfloor a0 h0) :=
  (mem_feasible.mp (minimumResource_feasible p s M C qfloor a0 h0)).1

end Hagi.Unified.QualityResourceMin
set_option linter.style.header false

/-!
# Guarded robust selection for the scalar logistic controller

This is a one-step specialization of `guardedRobustNext` to the actual
`logitProblem`, with `logitEstimate` and guard radius `1 / 2`.  The selected
successor is always an actual feasible logit successor.  Without an estimated
upgrade it is exactly the stay state; in all cases its logistic cross-entropy
is no greater than the stay value.

An exact update requires both feasibility of action `1` and an estimated
upgrade.  The upgrade can alternatively be obtained from an explicit true-CE
drop of at least `1`; smaller drops need not pass the `2 * (1 / 2)` guard.
These are deterministic one-step statements, not probability, generalization,
or parameter-convergence claims.
-/

namespace Hagi.Unified.GuardedRobustLogit

open Hagi.Model
open Hagi.Unified.ParetoExecution
open Hagi.Unified.GuardedRobustSelection
open Hagi.Unified.ParetoLogit
open Hagi.Unified.LogitCert

/-- The guarded robust successor specialized to the scalar logistic problem. -/
noncomputable def guardedLogitNext (eta : ℝ) (M C : ℕ) (w : ℝ) : ℝ :=
  guardedRobustNext (logitProblem eta) logitEstimate (1 / 2) w M C
    (0 : Fin 2) (logit_feasible_zero eta M C)

/-- The guarded successor is the actual step of some original feasible action. -/
theorem guardedLogitNext_exists (eta : ℝ) (M C : ℕ) (w : ℝ) :
    ∃ a ∈ feasible (logitProblem eta) M C,
      guardedLogitNext eta M C w = logitStepFun eta a w := by
  simpa only [guardedLogitNext, logitProblem_step] using
    (guardedRobustNext_exists (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2) (logit_feasible_zero eta M C))

/-- If no feasible action passes the estimate-margin guard, the actual
successor is exactly the stay state. -/
theorem guardedLogitNext_of_no_upgrade (eta : ℝ) (M C : ℕ) (w : ℝ)
    (h : ¬ estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    guardedLogitNext eta M C w = w := by
  unfold guardedLogitNext
  rw [guardedRobustNext_of_no_upgrade (logitProblem eta) logitEstimate (1 / 2)
    w M C (0 : Fin 2) (logit_feasible_zero eta M C) h]
  exact logitStepFun_zero eta w

/-- Unconditional one-step logistic-CE non-regression.  No positivity or
resource assumptions are needed: the error bound holds on every feasible
successor, including the always-feasible stay action. -/
theorem logitCE_guardedLogitNext_le (eta : ℝ) (M C : ℕ) (w : ℝ) :
    logitCE (guardedLogitNext eta M C w) ≤ logitCE w := by
  have h := guardedRobustNext_quality_ge_stay (logitProblem eta) logitEstimate
    (1 / 2) w M C (0 : Fin 2) (logit_feasible_zero eta M C)
    (fun a _ => le_of_eq (logitEstimate_error_action eta a w))
  change -logitCE w ≤ -logitCE (guardedLogitNext eta M C w) at h
  linarith only [h]

/-- A true-CE drop of at least `1` by action `1` supplies the exact
`2 * (1 / 2)` estimated-upgrade margin. -/
theorem estimatedUpgrade_of_logitCE_drop (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hdrop : 1 ≤ logitCE w - logitCE (w + eta / (1 + Real.exp w))) :
    estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2) := by
  refine ⟨1, logit_feasible_one eta heta M C hM hC, ?_⟩
  simp only [logitProblem_step, logitStepFun_zero, logitStepFun_one]
  unfold logitEstimate
  norm_num
  linarith only [hdrop]

/-- With action `1` feasible and the estimated-upgrade guard active, the
wrapper executes the existing robust logistic update exactly. -/
theorem guardedLogitNext_eq_update_of_upgrade (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    guardedLogitNext eta M C w = w + eta / (1 + Real.exp w) := by
  unfold guardedLogitNext guardedRobustNext
  rw [ite_eq_left hup]
  exact logit_robustNext eta heta w M C (logit_feasible_zero eta M C)
    (logit_feasible_one eta heta M C hM hC)

/-- The same exact update follows from an explicit true-CE drop of at least
`1`, rather than from a pre-established estimated-upgrade witness. -/
theorem guardedLogitNext_eq_update_of_logitCE_drop (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hdrop : 1 ≤ logitCE w - logitCE (w + eta / (1 + Real.exp w))) :
    guardedLogitNext eta M C w = w + eta / (1 + Real.exp w) := by
  exact guardedLogitNext_eq_update_of_upgrade eta heta M C hM hC w
    (estimatedUpgrade_of_logitCE_drop eta heta M C hM hC w hdrop)

/-- Under the exact-update resources and an active guard, logistic CE strictly
decreases by the existing scalar descent theorem. -/
theorem logitCE_guardedLogitNext_lt_of_upgrade (eta : ℝ) (heta : 0 < eta)
    (M C : ℕ) (hM : 1 ≤ M) (hC : 2 ≤ C) (w : ℝ)
    (hup : estimatedUpgrade (logitProblem eta) logitEstimate (1 / 2) w M C
      (0 : Fin 2)) :
    logitCE (guardedLogitNext eta M C w) < logitCE w := by
  rw [guardedLogitNext_eq_update_of_upgrade eta heta M C hM hC w hup]
  exact descent_step_strict w eta heta

end Hagi.Unified.GuardedRobustLogit
set_option linter.style.header false

/-!
# RobustResourceMin — minimum declared resources under a
bounded-estimation quality floor (cycle 74)

The exact finite policy of cycle 73 requires the successor's objective
value directly. Here only `estimate` may be available, but every actual
successor has error bounded by a uniform `eps`. Use the conservative
eligibility criterion
`qfloor + eps ≤ estimate (p.step a s)`. It implies the true-objective
floor `qfloor ≤ p.value (p.step a s)` by elementary arithmetic.

`robustMinimumResource` directly reuses `minimumResource` on the existing
`withEstimatedValue` problem. Resource costs and actual successors remain
those of `p`; there is no synthetic effect, second minimization engine or
resource exception at the upgrade boundary. The witness supplies
nonemptiness and the error bound supplies all quantitative claims.

Optimality is ONLY among lower-bound-certified candidates. A cheaper
candidate can meet the TRUE floor yet be excluded because its lower
bound cannot certify it. There is therefore no claim of minimum cost
among all truly floor-eligible actions, nor global/NAS/hardware/search
optimality. The absolute-error premise is deterministic; it is not a
statistical confidence level, calibration claim or physical measurement.
-/

namespace Hagi.Unified.RobustResourceMin

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin

variable {A : Type} {S : Type*}

/-- Choose a minimum-resource action in the estimated, conservative
floor class. Safety, caps, and actual step are definitionally unchanged. -/
noncomputable def robustMinimumResource {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) : A :=
  minimumResource (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0

/-- The chosen candidate's estimate meets the shifted floor, and it is
eligible in the original-step / original-resource policy. -/
theorem robustMinimumResource_eligible {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) :
    qualityEligible (withEstimatedValue p estimate) s M C (qfloor + eps)
      (robustMinimumResource estimate s M C qfloor eps a0 h0) :=
  (minimumResource_spec (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0).1

/-- The chosen action still has the original model safety and both exact
resource caps, independent of the quality-estimation error. -/
theorem robustMinimumResource_feasible {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) :
    robustMinimumResource estimate s M C qfloor eps a0 h0 ∈ feasible p M C := by
  have hf := minimumResource_feasible (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0
  exact (mem_feasible_withEstimatedValue p estimate).mp hf

/-- The actual successor meets the true floor. The only estimate-to-truth
connection is the explicitly supplied uniform absolute-error bound. -/
theorem robustMinimumResource_actual_quality_ge {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0)
    (herr : ∀ a, |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    qfloor ≤ p.value (p.step (robustMinimumResource estimate s M C
      qfloor eps a0 h0) s) := by
  have hq := minimumResource_next_quality_ge (withEstimatedValue p estimate)
    s M C (qfloor + eps) a0 h0
  have he := (abs_le.mp (herr (robustMinimumResource estimate s M C
    qfloor eps a0 h0))).1
  change qfloor + eps ≤ estimate (p.step (robustMinimumResource estimate s M C
    qfloor eps a0 h0) s) at hq
  linarith

/-- No lower-bound-certified competitor has smaller declared resource
cost. This deliberately does NOT quantify over every truly eligible b. -/
theorem robustMinimumResource_cost_min {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (a0 : A)
    (h0 : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a0) :
    ∀ b, qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) b →
      resourceCost p (robustMinimumResource estimate s M C qfloor eps a0 h0)
        ≤ resourceCost p b := by
  intro b hb
  exact minimumResource_cost_min (withEstimatedValue p estimate) s M C
    (qfloor + eps) a0 h0 b hb

/-- With the exact objective as estimator and zero error, this connector
is definitionally the preceding exact minimum-resource selector. No new
algorithm or conservativeness is added in that exact special case. -/
theorem robustMinimumResource_zero_exact {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (s : S) (M C : ℕ) (qfloor : ℝ)
    (a0 : A) (h0 : qualityEligible p s M C qfloor a0) :
    robustMinimumResource p.value s M C qfloor 0 a0 (by simpa using h0)
      = minimumResource p s M C qfloor a0 h0 := by
  simp [robustMinimumResource, withEstimatedValue, minimumResource]

end Hagi.Unified.RobustResourceMin
set_option linter.style.header false

/-!
# Guarded minimum-resource selection with baseline protection

When a feasible action has estimated quality at least `2 * eps` above the
stay action, this wrapper uses the existing robust minimum-resource selector.
The explicit one-sided baseline bound `hbase` turns that guard into a
certificate for the actual stay-quality floor. Otherwise it returns `stay`.

Under pointwise error bounds on currently feasible actions, the chosen action
has actual quality no lower than `stay`. Its declared memory-first resource
cost is minimal among the lower-bound-certified competitors specified below,
not among all truly nondecreasing actions or architectures.
-/

namespace Hagi.Unified.GuardedRobustResourceMin

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin
open Hagi.Unified.GuardedRobustSelection Hagi.Unified.RobustResourceMin

variable {A : Type} {S : Type*} [Fintype A]

/-- An estimated upgrade and the one-sided baseline error bound certify the
actual stay-quality floor for the original feasible action `a`. -/
theorem baselineCertificate_of_margin (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay a : A) (ha : a ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (hmargin : estimate (p.step stay s) + 2 * eps ≤ estimate (p.step a s)) :
    qualityEligible (withEstimatedValue p estimate) s M C
      (p.value (p.step stay s) + eps) a := by
  refine ⟨(mem_feasible_withEstimatedValue p estimate).mpr ha, ?_⟩
  change p.value (p.step stay s) + eps ≤ estimate (p.step a s)
  linarith

/-- Use the existing robust minimum-resource action when an estimated upgrade
exists, and otherwise stay. The baseline bound supplies the eligibility
certificate; no additional action or optimization engine is introduced. -/
noncomputable def guardedMinimumResource (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps) : A := by
  classical
  have _ := h0
  exact if h_up : estimatedUpgrade p estimate eps s M C stay then
    robustMinimumResource estimate s M C (p.value (p.step stay s)) eps
      (Classical.choose h_up)
      (baselineCertificate_of_margin p estimate eps s M C stay
        (Classical.choose h_up) (Classical.choose_spec h_up).1 hbase
        (Classical.choose_spec h_up).2)
  else
    stay

/-- Without an estimated upgrade, the guarded action is exactly `stay`. -/
theorem guardedMinimumResource_of_no_upgrade (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (h : ¬ estimatedUpgrade p estimate eps s M C stay) :
    guardedMinimumResource p estimate eps s M C stay h0 hbase = stay := by
  classical
  rw [guardedMinimumResource, dite_eq_right]
  exact h

/-- The guarded action remains feasible for the original problem in both the
upgrade and fallback branches. -/
theorem guardedMinimumResource_feasible (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps) :
    guardedMinimumResource p estimate eps s M C stay h0 hbase ∈
      feasible p M C := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · unfold guardedMinimumResource
    rw [dite_eq_left]
    · exact robustMinimumResource_feasible _ _ _ _ _ _ _ _
    · exact hup
  · rw [guardedMinimumResource_of_no_upgrade
      p estimate eps s M C stay h0 hbase hup]
    exact h0

/-- With estimation errors bounded on currently feasible actions, the guarded
minimum-resource action has actual quality at least that of `stay`. -/
theorem guardedMinimumResource_quality_ge_stay (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (herr : ∀ a ∈ feasible p M C,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    p.value (p.step stay s) ≤ p.value (p.step
      (guardedMinimumResource p estimate eps s M C stay h0 hbase) s) := by
  classical
  by_cases hup : estimatedUpgrade p estimate eps s M C stay
  · let a0 := Classical.choose hup
    let hcert := baselineCertificate_of_margin p estimate eps s M C stay a0
      (Classical.choose_spec hup).1 hbase (Classical.choose_spec hup).2
    have hquality : p.value (p.step stay s) ≤ p.value (p.step
        (robustMinimumResource estimate s M C (p.value (p.step stay s)) eps
          a0 hcert) s) := by
      have hfeasible := robustMinimumResource_feasible estimate s M C
        (p.value (p.step stay s)) eps a0 hcert
      have hq := (robustMinimumResource_eligible estimate s M C
        (p.value (p.step stay s)) eps a0 hcert).2
      have he := (abs_le.mp (herr _ hfeasible)).1
      change p.value (p.step stay s) + eps ≤ estimate (p.step
        (robustMinimumResource estimate s M C (p.value (p.step stay s)) eps
          a0 hcert) s) at hq
      linarith
    unfold guardedMinimumResource
    rw [dite_eq_left]
    exact hquality
  · rw [guardedMinimumResource_of_no_upgrade
      p estimate eps s M C stay h0 hbase hup]

/-- For any feasible competitor whose actual quality exceeds the stay quality
by at least `2 * eps`, the guarded upgrade has no greater declared resource
cost. This is the existing certified-class minimum, not global optimality. -/
theorem guardedMinimumResource_cost_le (p : ControllerProblem A S)
    [DecidablePred p.safe] (estimate : S → ℝ) (eps : ℝ) (s : S)
    (M C : ℕ) (stay : A) (h0 : stay ∈ feasible p M C)
    (hbase : p.value (p.step stay s) - estimate (p.step stay s) ≤ eps)
    (h_up : estimatedUpgrade p estimate eps s M C stay)
    (b : A) (hb : b ∈ feasible p M C)
    (hgain : p.value (p.step stay s) + 2 * eps ≤ p.value (p.step b s))
    (herr : ∀ a ∈ feasible p M C,
      |p.value (p.step a s) - estimate (p.step a s)| ≤ eps) :
    resourceCost p (guardedMinimumResource p estimate eps s M C stay h0 hbase) ≤
      resourceCost p b := by
  classical
  have hb_upper := (abs_le.mp (herr b hb)).2
  have hbCert : qualityEligible (withEstimatedValue p estimate) s M C
      (p.value (p.step stay s) + eps) b := by
    refine ⟨(mem_feasible_withEstimatedValue p estimate).mpr hb, ?_⟩
    change p.value (p.step stay s) + eps ≤ estimate (p.step b s)
    linarith
  unfold guardedMinimumResource
  rw [dite_eq_left]
  · exact robustMinimumResource_cost_min _ _ _ _ _ _ _ _ b hbCert
  · exact h_up

end Hagi.Unified.GuardedRobustResourceMin
set_option linter.style.header false

/-!
# RobustCostSensitivity — uncertainty radius and least certified
resource cost (cycle 75)

Increasing epsilon shifts the estimator floor UP, hence shrinks the
lower-bound-certified finite class. If both radius levels have eligible
witnesses, the minimum declared resource cost cannot decrease: the
small-radius minimum can be compared with the selected large-radius
candidate, whose eligibility transfers into the smaller class.

The order remains the explicit `(memory, operations)` Prod.Lex order.
Memory itself is monotone; neither strict monotonicity nor a separate
operations-time/FLOPs monotonicity follows. Both witness hypotheses stay
visible because sufficiently high uncertainty may make the class empty.
This does not optimize over the wider truly-eligible class and does not
measure physical resources or make a statistical confidence assertion.
-/

namespace Hagi.Unified.RobustCostSensitivity

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin
open Hagi.Unified.RobustResourceMin

variable {A : Type} {S : Type*}

/-- Larger radius implies membership in the smaller-radius certified
class. The actual feasibility component is unchanged. -/
theorem robustEligible_mono_epsilon {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps1 eps2 : ℝ)
    (h_eps : eps1 ≤ eps2) {a : A}
    (ha : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps2) a) :
    qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps1) a := by
  exact ⟨ha.1, by linarith [ha.2]⟩

/-- Minimum declared resource cost is nondecreasing as the robustness
radius grows. Both eligible witnesses are required; this is not an
existence assertion for empty certified classes. -/
theorem robustMinimumResource_cost_mono {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps1 eps2 : ℝ) (a1 a2 : A)
    (h_eps : eps1 ≤ eps2)
    (h_small : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps1) a1)
    (h_large : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps2) a2) :
    resourceCost p (robustMinimumResource estimate s M C qfloor eps1 a1 h_small)
      ≤ resourceCost p
          (robustMinimumResource estimate s M C qfloor eps2 a2 h_large) := by
  apply robustMinimumResource_cost_min estimate s M C qfloor eps1 a1 h_small
    (robustMinimumResource estimate s M C qfloor eps2 a2 h_large)
  exact robustEligible_mono_epsilon estimate s M C qfloor eps1 eps2 h_eps
    (robustMinimumResource_eligible estimate s M C qfloor eps2 a2 h_large)

/-- The first memory coordinate is nondecreasing under the same witness
premises. No separate operations monotone claim is made. -/
theorem robustMinimumResource_memory_mono {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps1 eps2 : ℝ) (a1 a2 : A)
    (h_eps : eps1 ≤ eps2)
    (h_small : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps1) a1)
    (h_large : qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps2) a2) :
    p.memory (robustMinimumResource estimate s M C qfloor eps1 a1 h_small)
      ≤ p.memory
          (robustMinimumResource estimate s M C qfloor eps2 a2 h_large) := by
  have hcost := robustMinimumResource_cost_mono estimate s M C qfloor
    eps1 eps2 a1 a2 h_eps h_small h_large
  exact Prod.Lex.monotone_fst _ _ hcost

end Hagi.Unified.RobustCostSensitivity
set_option linter.style.header false

/-!
# RobustRadius — exact boundary for estimator-floor admissibility
(cycle 76)

For a given objective floor, the lower-bound-certified class is nonempty
precisely when `eps ≤ maxEstimate − qfloor`, where `maxEstimate` is the
existing finite selector's estimated value on its ACTUAL successor.
The boundary is included; a larger radius has no eligible action.

This reuses `ParetoExecution.selection` over `withEstimatedValue`.
`h_stay` supplies only the nonempty original feasible set, not arbitrary
robust-floor feasibility. Resource caps remain original and no minimum
resource or search-time engine is duplicated.

The scalar margin is not a conic/MIP robust-feasibility-radius algorithm,
an architecture optimum, physical resource certification or statistical
confidence. Actual objective-floor quality still requires the separate
absolute-error hypothesis from the previous connector.
-/

namespace Hagi.Unified.RobustRadius

open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin

variable {A : Type} {S : Type*}

/-- Maximum estimated value on an actual successor, computed by the
existing finite selector. Only its value estimate matters in the margin. -/
noncomputable def estimatedMaxValue {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (stay : A) (h_stay : stay ∈ feasible p M C) : ℝ :=
  (withEstimatedValue p estimate).value
    (selectedNext (withEstimatedValue p estimate) s M C stay
      ((mem_feasible_withEstimatedValue p estimate).mpr h_stay))

/-- The selected maximum dominates the estimated value on each actual
successor of every original-feasible candidate. -/
theorem estimatedMaxValue_upper {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (stay : A) (h_stay : stay ∈ feasible p M C)
    {a : A} (ha : a ∈ feasible p M C) :
    estimate (p.step a s) ≤ estimatedMaxValue estimate s M C stay h_stay := by
  have h := selection_quality_optimal (withEstimatedValue p estimate)
    s M C stay ((mem_feasible_withEstimatedValue p estimate).mpr h_stay)
    a ((mem_feasible_withEstimatedValue p estimate).mpr ha)
  exact h

/-- Exact admissibility criterion for existence of a conservative
floor-certified action. Boundary point included. -/
theorem robust_eligible_iff_radius_le_margin {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (stay : A)
    (h_stay : stay ∈ feasible p M C) :
    (∃ a, qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a) ↔
      eps ≤ estimatedMaxValue estimate s M C stay h_stay - qfloor := by
  constructor
  · rintro ⟨a, hfe, hq⟩
    have hb := estimatedMaxValue_upper estimate s M C stay h_stay hfe
    exact sub_nonneg.mp (by linarith : 0 ≤
      estimatedMaxValue estimate s M C stay h_stay - qfloor - eps)
  · intro he
    let hse : stay ∈ feasible (withEstimatedValue p estimate) M C :=
      (mem_feasible_withEstimatedValue p estimate).mpr h_stay
    refine ⟨selection (withEstimatedValue p estimate) s M C stay hse,
      selection_admissible (withEstimatedValue p estimate) s M C stay hse, ?_⟩
    change qfloor + eps ≤ estimate (p.step
      (selection (withEstimatedValue p estimate) s M C stay hse) s)
    dsimp [estimatedMaxValue, selectedNext] at he
    linarith

/-- After the maximum estimated margin, no candidate can be eligible. -/
theorem no_robust_eligible_above_margin {p : ControllerProblem A S}
    [Fintype A] [DecidablePred p.safe] (estimate : S → ℝ)
    (s : S) (M C : ℕ) (qfloor eps : ℝ) (stay : A)
    (h_stay : stay ∈ feasible p M C)
    (h_eps : estimatedMaxValue estimate s M C stay h_stay - qfloor < eps) :
    ∀ a, ¬ qualityEligible (withEstimatedValue p estimate) s M C
      (qfloor + eps) a := by
  intro a ha
  have hb := estimatedMaxValue_upper estimate s M C stay h_stay ha.1
  have hq := ha.2
  linarith

end Hagi.Unified.RobustRadius
set_option linter.style.header false

/-!
# Executable finite selection with logical guard and relation counters
(cycle 77)

This module instruments the existing `List.filter` and `List.argmin`
algorithms. It does not implement another minimum engine. Logical
composite-guard and pair-relation calls are counted, not physical
instructions, wall time, FLOPs, or allocations. In particular, a
comparison may evaluate its cost function more than once, and a
short-circuiting guard need not evaluate every field or successor.
-/

namespace Hagi.Unified.ExecutableSelection

/-- Filter a finite list while counting logical composite-guard calls. -/
def auditedFilter {α : Type*} (guard : α → Bool) : List α → List α × ℕ
  | [] => ([], 0)
  | a :: as =>
      let (accepted, n) := auditedFilter guard as
      (if guard a then a :: accepted else accepted, n + 1)

/-- The instrumented filter retains precisely the ordinary filter's
candidates. -/
theorem auditedFilter_fst {α : Type*} (guard : α → Bool) (as : List α) :
    (auditedFilter guard as).1 = as.filter guard := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases h : guard a <;> simp [auditedFilter, h, ih]

/-- Every supplied action is inspected by one logical composite guard. -/
theorem auditedFilter_snd {α : Type*} (guard : α → Bool) (as : List α) :
    (auditedFilter guard as).2 = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      cases h : guard a <;> simp [auditedFilter, h, ih]

/-- Same step as the library argmin fold, plus one counter increment
when there is an incumbent and hence a relation call. -/
private def argminStep {α R : Type*} [LinearOrder R] (cost : α → R)
    (incumbent : Option α × ℕ) (a : α) : Option α × ℕ :=
  (List.argAux (fun b c => cost b < cost c) incumbent.1 a,
    incumbent.2 + if incumbent.1.isSome then 1 else 0)

/-- Audited finite minimum. The second component counts relation cells
visited by the fold; it is not a measurement of run-time instructions. -/
def auditedArgmin {α R : Type*} [LinearOrder R] (cost : α → R) (as : List α) :
    Option α × ℕ :=
  as.foldl (argminStep cost) (none, 0)

private theorem foldl_argminStep_fst {α R : Type*} [LinearOrder R]
    (cost : α → R) (as : List α) (best : Option α) (n : ℕ) :
    (as.foldl (argminStep cost) (best, n)).1 =
      as.foldl (List.argAux fun b c => cost b < cost c) best := by
  induction as generalizing best n with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      exact ih _ _

private theorem foldl_argminStep_snd_some {α R : Type*} [LinearOrder R]
    (cost : α → R) (as : List α) (a : α) (n : ℕ) :
    (as.foldl (argminStep cost) (some a, n)).2 = n + as.length := by
  induction as generalizing a n with
  | nil => rfl
  | cons b as ih =>
      simp only [List.foldl_cons]
      by_cases h : cost b < cost a
      · have hi := ih b (n + 1)
        simp only [argminStep, List.argAux, h, ↓reduceIte,
          Option.isSome_some, List.length_cons]
        omega
      · have hi := ih a (n + 1)
        simp only [argminStep, List.argAux, h, ↓reduceIte,
          Option.isSome_some, List.length_cons]
        omega

private theorem foldl_argminStep_snd_none_cons {α R : Type*} [LinearOrder R]
    (cost : α → R) (a : α) (as : List α) (n : ℕ) :
    ((a :: as).foldl (argminStep cost) (none, n)).2 = n + as.length := by
  simp only [List.foldl_cons]
  simpa [argminStep, List.argAux] using foldl_argminStep_snd_some cost as a n

/-- The audited fold selects exactly the same candidate as `List.argmin`;
its first-on-tie and all minimum properties are inherited, not duplicated. -/
theorem auditedArgmin_fst {α R : Type*} [LinearOrder R] (cost : α → R)
    (as : List α) : (auditedArgmin cost as).1 = List.argmin cost as := by
  exact foldl_argminStep_fst cost as none 0

/-- Zero comparisons for no candidates; otherwise exactly one fewer than
the number of admitted candidates. This follows from the fold itself. -/
theorem auditedArgmin_snd {α R : Type*} [LinearOrder R] (cost : α → R)
    (as : List α) : (auditedArgmin cost as).2 = as.length - 1 := by
  cases as with
  | nil => rfl
  | cons a as =>
      simpa [auditedArgmin] using foldl_argminStep_snd_none_cons cost a as 0

end Hagi.Unified.ExecutableSelection


/-!
# Executable discrete finite resource selection (cycle 77)

A supplied action list is filtered by a concrete Bool guard, then the
existing `List.argmin` chooses minimum memory-first resource cost among
quality-eligible actions **in that list**. No `Classical.choose`, default
action, physical-safety claim, or arbitrary real-valued search is added.

The point-model adapter casts integer quality into the old real-valued
controller interface. Its guard equivalence and equality with the old
minimum cost use that cast model; they do not execute arbitrary real CE.
Completeness of the input list is a separate explicit premise whenever
whole-Fintype minimality is claimed. Instrumented counts are logical
guard and pair-relation calls, not hardware instructions or latency.
-/

namespace Hagi.Unified.ExecutableController

open Hagi.Unified.ExecutableSelection
open Hagi.Unified.ParetoExecution Hagi.Unified.QualityResourceMin

/-- A supplied discrete point model with the old controller's `A : Type`
action carrier. `safetyGuard` is only the model's Boolean admission
guard, not evidence of physical safety. -/
structure DiscreteProgram (A : Type) (S : Type*) where
  actions : List A
  state : S
  step : A → S → S
  quality : S → ℤ
  safetyGuard : A → S → Bool
  memory : A → ℕ
  operations : A → ℕ
  memoryCap : ℕ
  operationsCap : ℕ
  qualityFloor : ℤ

/-- Total executable admission at the supplied state. Quality is checked
at the actual successor. Boolean short-circuiting means that a rejected
prefix need not evaluate every later field or successor. -/
def admissionGuard {A : Type} {S : Type*} (p : DiscreteProgram A S) (a : A) : Bool :=
  p.safetyGuard a p.state && decide (p.memory a ≤ p.memoryCap) &&
    decide (p.operations a ≤ p.operationsCap) &&
    decide (p.qualityFloor ≤ p.quality (p.step a p.state))

theorem admissionGuard_eq_true {A : Type} {S : Type*} (p : DiscreteProgram A S) (a : A) :
    admissionGuard p a = true ↔
      p.safetyGuard a p.state = true ∧
        p.memory a ≤ p.memoryCap ∧ p.operations a ≤ p.operationsCap ∧
        p.qualityFloor ≤ p.quality (p.step a p.state) := by
  simp [admissionGuard, and_assoc]

/-- Adapter of the supplied point model into the old real-valued
controller. Only the quality value is cast; `step` and resources are
unchanged. `safe` captures the guard at the fixed supplied state. -/
@[reducible] def toController {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    ControllerProblem A S where
  value s := (p.quality s : ℝ)
  step := p.step
  memory := p.memory
  operations := p.operations
  safe a := p.safetyGuard a p.state = true

instance {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    DecidablePred (toController p).safe :=
  fun a => inferInstanceAs (Decidable (p.safetyGuard a p.state = true))

/-- The executable guard is exactly old eligibility in the integer-cast
controller. Both directions cover arbitrary signs of integer quality. -/
theorem admissionGuard_iff_qualityEligible {A : Type} {S : Type*} [Fintype A]
    (p : DiscreteProgram A S) (a : A) :
    admissionGuard p a = true ↔
      qualityEligible (p := toController p) p.state p.memoryCap p.operationsCap
        (p.qualityFloor : ℝ) a := by
  rw [admissionGuard_eq_true, qualityEligible, mem_feasible (p := toController p)]
  constructor
  · rintro ⟨hsafe, hmemory, hoperations, hquality⟩
    refine ⟨⟨hsafe, hmemory, hoperations⟩, ?_⟩
    change (p.qualityFloor : ℝ) ≤ (p.quality (p.step a p.state) : ℝ)
    exact_mod_cast hquality
  · rintro ⟨⟨hsafe, hmemory, hoperations⟩, hquality⟩
    refine ⟨hsafe, hmemory, hoperations, ?_⟩
    change (p.qualityFloor : ℝ) ≤ (p.quality (p.step a p.state) : ℝ) at hquality
    exact_mod_cast hquality

/-- Selection result together with its explicit logical work counters.
These are model counts, not an automatically generated native profile. -/
structure SelectionReport (A : Type) where
  selected : Option A
  guardCalls : ℕ
  comparisons : ℕ

/-- One guarded filter and one existing argmin fold. Both are inspected
only through the audited kernel; no second minimum algorithm is used. -/
def selectionReport {A : Type} {S : Type*} (p : DiscreteProgram A S) : SelectionReport A :=
  let admitted := auditedFilter (admissionGuard p) p.actions
  let best := auditedArgmin (fun a => resourceCost (toController p) a) admitted.1
  { selected := best.1
    guardCalls := admitted.2
    comparisons := best.2 }

/-- The executable selection as an option; no artificial default action. -/
def finiteSelection {A : Type} {S : Type*} (p : DiscreteProgram A S) : Option A :=
  (selectionReport p).selected

/-- Actual successor of the returned action at the supplied state. -/
def selectedNext {A : Type} {S : Type*} (p : DiscreteProgram A S) : Option S :=
  (finiteSelection p).map (fun a => p.step a p.state)

private theorem finiteSelection_eq_argmin {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    finiteSelection p =
      List.argmin (fun a => resourceCost (toController p) a)
        (p.actions.filter (admissionGuard p)) := by
  unfold finiteSelection selectionReport
  simp only [auditedArgmin_fst, auditedFilter_fst]

private theorem finiteSelection_mem_argmin {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) :
    a ∈ List.argmin (fun a => resourceCost (toController p) a)
      (p.actions.filter (admissionGuard p)) := by
  rw [← finiteSelection_eq_argmin]
  simp [ha]

/-- A returned action really occurs in the supplied list and passed the
complete composite guard. -/
theorem finiteSelection_mem {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) :
    a ∈ p.actions ∧ admissionGuard p a = true := by
  exact List.mem_filter.mp (List.argmin_mem (finiteSelection_mem_argmin p ha))

/-- Minimum memory-first resource cost over all eligible input-list
members. Nothing is claimed about unlisted candidates. -/
theorem finiteSelection_minimum {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) (b : A)
    (hb : b ∈ p.actions) (hguard : admissionGuard p b = true) :
    resourceCost (toController p) a ≤ resourceCost (toController p) b := by
  exact List.le_of_mem_argmin (List.mem_filter.mpr ⟨hb, hguard⟩)
    (finiteSelection_mem_argmin p ha)

/-- No returned action precisely when every input action fails the guard.
There is no fallback witness, and no physical state unchanged theorem. -/
theorem finiteSelection_none_iff {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    finiteSelection p = none ↔
      ∀ a ∈ p.actions, admissionGuard p a = false := by
  rw [finiteSelection_eq_argmin, List.argmin_eq_none, List.filter_eq_nil_iff]
  constructor
  · intro h a ha
    have hg := h a ha
    cases hb : admissionGuard p a <;> simp_all
  · intro h a ha
    have hb := h a ha
    simp [hb]

/-- The optional successor is the actual `step`, not an effects record. -/
theorem selectedNext_eq_some {A : Type} {S : Type*} (p : DiscreteProgram A S)
    {a : A} (ha : finiteSelection p = some a) :
    selectedNext p = some (p.step a p.state) := by
  simp [selectedNext, ha]

/-- Guard counter is exactly the number of supplied actions, including
when the filtered candidate list is empty. -/
theorem selectionReport_guardCalls {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    (selectionReport p).guardCalls = p.actions.length := by
  simpa [selectionReport] using auditedFilter_snd (admissionGuard p) p.actions

/-- Pair-relation comparisons are one fewer than admitted candidates,
or zero if there is no admitted candidate. -/
theorem selectionReport_comparisons {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    (selectionReport p).comparisons =
      (p.actions.filter (admissionGuard p)).length - 1 := by
  simpa [selectionReport, auditedFilter_fst] using
    auditedArgmin_snd (fun a => resourceCost (toController p) a)
      (auditedFilter (admissionGuard p) p.actions).1

/-- Model relation-call count is bounded by total inputs, but this is
not minimum CPU, FLOPs, wall time, or a universal search lower bound. -/
theorem selectionReport_comparisons_le {A : Type} {S : Type*} (p : DiscreteProgram A S) :
    (selectionReport p).comparisons ≤ p.actions.length := by
  rw [selectionReport_comparisons]
  exact (Nat.sub_le _ _).trans (List.length_filter_le _ _)

/-- Equality with the old mathematical minimum cost in the cast model,
provided the input list covers every action. The concrete selected
actions may differ under cost ties; only their resource costs are equal. -/
theorem finiteSelection_cost_eq_minimumResource {A : Type} {S : Type*} [Fintype A]
    (p : DiscreteProgram A S) {a : A} (ha : finiteSelection p = some a)
    (hcomplete : ∀ b, b ∈ p.actions) :
    resourceCost (toController p) a = resourceCost (toController p)
      (minimumResource (toController p) p.state p.memoryCap p.operationsCap
        (p.qualityFloor : ℝ) a
        ((admissionGuard_iff_qualityEligible p a).mp (finiteSelection_mem p ha).2)) := by
  let hquality : qualityEligible (toController p) p.state p.memoryCap p.operationsCap
      (p.qualityFloor : ℝ) a :=
    (admissionGuard_iff_qualityEligible p a).mp (finiteSelection_mem p ha).2
  change resourceCost (toController p) a = resourceCost (toController p)
    (minimumResource (toController p) p.state p.memoryCap p.operationsCap
      (p.qualityFloor : ℝ) a hquality)
  have hmin := minimumResource_spec (toController p) p.state p.memoryCap
    p.operationsCap (p.qualityFloor : ℝ) a hquality
  exact le_antisymm
    (finiteSelection_minimum p ha _ (hcomplete _)
      ((admissionGuard_iff_qualityEligible p _).mpr hmin.1))
    (hmin.2 a hquality)

end Hagi.Unified.ExecutableController
set_option linter.style.header false



