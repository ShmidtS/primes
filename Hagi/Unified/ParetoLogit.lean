import Mathlib.Tactic
import Hagi.Model.SoftmaxStep
import Hagi.Unified.ParetoExecution
import Hagi.Unified.LogitCert
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
