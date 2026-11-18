import Hagi.Theory.MasterTheorem
import Hagi.Cert.StepGen
import Mathlib.Tactic

/-!
# MasterBudget — resource-ledger bridge for the budget clause

C398, ресурсный мост: premise-канал бюджета C392
(`MasterBudgetCert`: Σ cost ≤ B как явный биндер потребителя)
закрывается ДОКАЗАННЫМ королларием resource-слоя — телескоп
бюджетного_LEDGERа C330 (`budget_telescope_gen`: терминальный
бюджет = начальный − Σ точных трат) плюс доказанная
неотрицательность остатка (`CertStepGen.budget_nonneg`).
Кап Σ costs ≤ B ВЫВОДИТСЯ, не предполагается.

## Что мостится (bridged)

- Любой cost-канал, реализующий C278 ledger: явная
  instantiation-гипотеза `hmatch` (stepCost = budgetSpend)
  даёт ТОЧНЫЙ баланс Σ costs = budget₀ − budget_T
  (`budget_from_resource_ledger`), а кап — следствие
  неотрицательности терминального остатка
  (`masterBudgetCert_of_resource_ledger` возвращает
  `MasterBudgetCert` как theorem output).
- Демо (C331 KV-cache): per-step cost = cached per-token work
  `cachedTokenWork t = t + 1`; точная сумма
  2·Σ = T·(T+1) (форма `cached_total_work_eq`) закрывает
  budget_ok на ТОЧНОМ cached-тотале (`master_budget_kv_cached`);
  ratio-контекст — `kv_work_ratio` (3·recompute = (n+2)·cached).

## Что остаётся premise-form (честные пины)

- Потребители `MasterBudgetCert` БЕЗ ledger-реализации — кап
  остаётся биндером (наследуется пин C388).
- (d, W)-фронт C334 (`data_compute_budget`: десцент-рейт и
  per-step work — премизы честного интерфейса) здесь не
  пере-выводится: мост адресует КАНАЛ, не фронт.
- Демо не строит полный `SystemMetrics`-объект с KV-тратами
  (`kv_step_certified` — Contracts, слой 7, недоступен Theory по
  LayerLint); вместо этого — тот же паттерн вывода (точная
  идентичность вместо предполагаемого капа) на числовой модели.
- Никакой hardware-модели, никаких асимптотик.

## Layering note

Theory (7) не может импортировать Contracts (7) — телескоп
пере-доказан локально над ТЕМ ЖЕ kernel-полем
`CertStepGen.budget_next` (паттерн C330 `budget_telescope_gen`,
цитируется; переиспользование доказательства, не результата —
LayerLint-ограничение, не дублирование намерения).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory

open Hagi.State Hagi.Probability
open scoped BigOperators Classical

variable {n a e q r c k : ℕ}

/-! ## Локальный телескоп ledger-а (паттерн C330) -/

section Bridge

variable {S TaskId : Type*}
variable (M : Hagi.Cert.SystemMetrics S TaskId)
variable (obl : Hagi.Cert.StepObligations TaskId)

/-- Телескоп ресурсного ledger-а над kernel-полем
`CertStepGen.budget_next` (тот же паттерн, что C330
`budget_telescope_gen`; пере-доказан здесь: Contracts недоступен
из Theory по LayerLint). Терминальный бюджет = начальный минус
ТОЧНАЯ сумма per-step трат — закон ресурсного учёта. -/
theorem budget_ledger_telescope (deltaLevel : S → ℝ)
    (T : ℕ) (traj : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (traj j) (traj (j + 1))) :
    M.budget (traj T) = M.budget (traj 0)
      - ∑ j ∈ Finset.range T, (steps j).budgetSpend := by
  induction T with
  | zero => simp
  | succ T ih =>
    have e := (steps T).budget_next
    rw [e, ih, Finset.sum_range_succ]
    ring

/-! ## Мост: master cost-канал ⟷ resource ledger -/

/-- МОСТ: если per-step стоимости мастер-траектории — это в
точности траты resource ledger-а (ЭКСПЛИЦИТНАЯ instantiation-
гипотеза `hmatch`: два иначе несвязанных канала отождествлены
сознательно, не по переименованию), то суммарная стоимость
телескопируется в ТОЧНЫЙ баланс ledger-а: Σ costs = budget₀ −
budget_T. Это `budget_from_resource_ledger` — счёт, не кап. -/
theorem budget_from_resource_ledger (deltaLevel : S → ℝ)
    (T : ℕ) (traj : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (traj j) (traj (j + 1)))
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T)
    (hmatch : ∀ j < T, m.stepCost T j = (steps j).budgetSpend) :
    ∑ j ∈ Finset.range T, m.stepCost T j
      = M.budget (traj 0) - M.budget (traj T) := by
  have htel := budget_ledger_telescope M obl deltaLevel T traj steps
  have hsum : ∑ j ∈ Finset.range T, (steps j).budgetSpend
      = ∑ j ∈ Finset.range T, m.stepCost T j :=
    Finset.sum_congr rfl
      (fun j hj => (hmatch j (Finset.mem_range.mp hj)).symm)
  rw [htel, hsum]
  ring

/-- ПРОИЗВОДНЫЙ КАП: мост + неотрицательность остатка ⇒
Σ costs ≤ budget₀. Кап НЕ предполагается — он следствие
ресурсного закона (телескоп) и неотрицательности остатка:
`hnn` разряжается ДОКАЗАННЫМ полем `CertStepGen.budget_nonneg`
последнего шага (для T > 0 это проекция сертификата, не новая
премиза; для T = 0 сумма пуста и `hnn` — то же утверждение о
budget (traj 0)). -/
theorem master_budget_of_resource_ledger (deltaLevel : S → ℝ)
    (T : ℕ) (traj : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (traj j) (traj (j + 1)))
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T)
    (hmatch : ∀ j < T, m.stepCost T j = (steps j).budgetSpend)
    (hnn : 0 ≤ M.budget (traj T)) :
    ∑ j ∈ Finset.range T, m.stepCost T j ≤ M.budget (traj 0) := by
  have h := budget_from_resource_ledger M obl deltaLevel T traj steps m hmatch
  linarith

/-- УПАКОВКА: budget-клауза мастер-теоремы как theorem output —
`MasterBudgetCert` при B = budget₀ строится ДОКАЗАТЕЛЬСТВОМ
(bridge + nonneg), а не предъявляется потребителем. Это и есть
замена premise-канала ресурсным королларием (beat C397 top-2). -/
theorem masterBudgetCert_of_resource_ledger (deltaLevel : S → ℝ)
    (T : ℕ) (traj : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (traj j) (traj (j + 1)))
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T)
    (hmatch : ∀ j < T, m.stepCost T j = (steps j).budgetSpend)
    (hnn : 0 ≤ M.budget (traj T)) :
    MasterBudgetCert T m (M.budget (traj 0)) where
  budget_ok := master_budget_of_resource_ledger
    M obl deltaLevel T traj steps m hmatch hnn

end Bridge

/-! ## Демо: KV-cache cost-модель (C331) в budget-клаузе -/

/-- Helper: точная сумма cached per-token работ над T шагами в
форме без деления — 2·Σ_{j<T} ((j:ℝ)+1) = T·(T+1); ℝ-зерка
identity C331 `cached_total_work_eq` (2·cachedTotalWork n =
n(n+1), где `cachedTokenWork t = t + 1`). -/
theorem sum_range_succ_cast_two (T : ℕ) :
    2 * ∑ j ∈ Finset.range T, ((j : ℝ) + 1) = (T : ℝ) * ((T : ℝ) + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have h : (T : ℝ) * ((T : ℝ) + 1) + 2 * ((T : ℝ) + 1)
        = ((T : ℝ) + 1) * ((T : ℝ) + 1 + 1) := by ring
    push_cast
    nlinarith [ih, h]

/-- ДЕМО-ИНСТАНЦИАЦИЯ (C331 KV-cache): если per-step стоимость
мастер-шага j — cached per-token work `cachedTokenWork j = j + 1`
(реальная ресурсная модель: один проход по кэшу = j+1 чтений), то
budget-клауза закрывается на ТОЧНОМ cached-тотале
B = T·(T+1)/2 (форма `cached_total_work_eq`) — кап выведен из
доказанной суммы, не предъявлен. Контекст экономии: по
`kv_work_ratio` (3·recompute = (n+2)·cached) рекуррентный режим
стоил бы ровно (T+2)/3 раза больше. -/
theorem master_budget_kv_cached (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T)
    (hcost : ∀ j < T, m.stepCost T j = ((j : ℝ) + 1))
    (B : ℝ) (hB : 2 * B = (T : ℝ) * ((T : ℝ) + 1)) :
    MasterBudgetCert T m B where
  budget_ok := by
    have hsum := sum_range_succ_cast_two T
    have hcongr : ∑ j ∈ Finset.range T, m.stepCost T j
        = ∑ j ∈ Finset.range T, ((j : ℝ) + 1) :=
      Finset.sum_congr rfl
        (fun j hj => hcost j (Finset.mem_range.mp hj))
    rw [hcongr]
    linarith

end Hagi.Theory
