/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Cert.StepGen
import Hagi.Cert.Telescope
import Hagi.Model.ReferenceMachine
import Hagi.State.TrainTrajectory
import Hagi.Step.NoisyPL
import Hagi.Unified.StochasticLoop
import Mathlib.Tactic


/-!
# MasterTheorem — сборная траекторная теорема certified-or-refuse

центральная теорема A17 (audit's master statement):

«EITHER performs a certified update with controlled descent and
preserved constraints, OR safely refuses; across the trajectory
total quality loss, risk, compute budget stay within proven
bounds.»

## Clause-by-clause honesty audit (mapping)

| Пункт аудита | Формальный пункт |
|---|---|
| EITHER certified update | `MasterStepCert` (drop ≥ 0, penalty ≥ 0 — форма `2·L_lip·ε_q`, cost ≥ 0, спуск `fullObjective s' ≤ fullObjective s − drop + penalty`) |
| OR safely refuses | `MasterTrajectory.holds`: hold ⇒ тождество состояния (семантика `hold_rollback_total`; та же дихотомия у `hold_refusal_safe` `refuse_safe`) |
| total quality loss bounded | `master_trajectory_bound` (ТЕЛЕСКОП `obj_telescope_err`, линейное накопление penalty) |
| compute budget in proven bounds | `MasterBudgetCert` (PREMISE-канал: Σ cost ≤ B, потребительский биндер) + доказанный `master_budget_uniform` (cap c ⇒ Σ ≤ T·c) |
| risk in proven bounds | whp-канал: `master_union_bound` (P[all good] ≥ 1 − Σδ_t, паттерн) + `master_conditional_bound` (телескоп на good-событии) |
| preserved constraints | указатель `master_accept_fullCert` (FullStepCert) → `fourCert_of_parts` (layer 8) + книги |

## Честные пины (premise-form)

- **Бюджет — premise-канал.** `MasterBudgetCert` — явный
  биндер, НЕ ресурсный учёт: пин (budget = 0 zero-channel)
  наследуется и становится явным. Реальный учёт — co-beat.
- **EF residual, траекторный член — ПИН.** endpoint-формы
  (`ef_compressed_step_bound`) цитируются; Σ‖e_t‖-телескоп —
  co-beat (ranked #2).
- **PL-геометрия — ПИН.** Теоремы живут на CE-reg
  носителе (`ce_global_convergence_reg_closed`), не на
  `fullObjective` канонического состояния; композиция требует
  carrier-моста (co-beat). Здесь: `master_uniform` даёт линейную
  замкнутую форму, геометрическая — при мосте.
- **whp — условно-на-good-событиях** (даунгрейд gap 3):
  union bound без независимости; δ-бюджет покрывает только
  descent-отказы шагов (caveats наследуются).
- **Four-cert — указатель.** LayerLint: Training (8) > Theory (7),
  `fourCert_of_parts` не импортируем — конструктивен до layer 3
  (`FullStepCert`), завершение композиции описано в docstring.
- Адаптивные данные: caveats (e-process fresh-data premise)
  наследуются без изменений.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory

open Hagi.State Hagi.Probability
open scoped BigOperators Classical

variable {n a e q r c k : ℕ}

/-! ## Сертификат одного шага: certified-or-refuse -/

/-- Сертификат ПРИНЯТОГО шага мастера: контролируемый спуск
(заявленный drop ≥ 0), аддитивный penalty ≥ 0 (форма
2·L_lip·ε_q на сжатых эндпоинтах), стоимость cost ≥ 0 (канал
бюджета) и доказанный спуск полной цели с penalty. Refusal НЕ
носит этот сертификат — refusal это Hold (см.
`MasterTrajectory.holds`). -/
structure MasterStepCert (s s' : CanonicalTrainState n a e q r c k) where
  /-- Заявленный спуск полной цели (certified drop). -/
  drop : ℝ
  /-- Спуск неотрицателен. -/
  drop_nonneg : 0 ≤ drop
  /-- Аддитивный штраф сжатия (форма 2·L_lip·ε_q). -/
  penalty : ℝ
  /-- Штраф неотрицателен. -/
  penalty_nonneg : 0 ≤ penalty
  /-- Стоимость шага (канал бюджета, premise-binder). -/
  cost : ℝ
  /-- Стоимость неотрицательна. -/
  cost_nonneg : 0 ≤ cost
  /-- Спуск ПОЛНОЙ цели с штрафом:(weights+буферы). -/
  descent : fullObjective s' ≤ fullObjective s - drop + penalty

/-- Траектория мастера: T шагов на каноническом состоянии, каждый
шаг ЛИБО сертифицированный accept (`outs j ≠ hold` несёт
`MasterStepCert`), ЛИБО отказ (`outs j = hold` ⇒ тождество
состояния, Hold). Бюджет B — PREMISE-канал (`MasterBudgetCert`): суммарная
стоимость ≤ B как явный биндер (не ресурсный учёт). -/
structure MasterTrajectory (T : ℕ) where
  /-- Состояния траектории: `states j` — после j шагов. -/
  states : ℕ → CanonicalTrainState n a e q r c k
  /-- Исход шага j: accept (progress) или отказ (hold). -/
  outs : ℕ → Outcome (CanonicalTrainState n a e q r c k)
  /-- Сертификат каждого ПРИНЯТОГО шага. -/
  certs : ∀ j < T, outs j ≠ Outcome.hold →
    MasterStepCert (states j) (states (j + 1))
  /-- Отказ — тождество состояния (safe refusal). -/
  holds : ∀ j < T, outs j = Outcome.hold → states (j + 1) = states j


/-! ## Тотальные функции шагов (паттерн stepDrop) -/

/-- Drop шага j как полная функция: 0 на отказах. -/
noncomputable def MasterTrajectory.stepDrop (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) (j : ℕ) : ℝ :=
  if h : j < T ∧ m.outs j ≠ Outcome.hold then (m.certs j h.1 h.2).drop else 0

/-- Penalty шага j как полная функция: 0 на отказах. -/
noncomputable def MasterTrajectory.stepPenalty (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) (j : ℕ) : ℝ :=
  if h : j < T ∧ m.outs j ≠ Outcome.hold then (m.certs j h.1 h.2).penalty else 0

/-- Стоимость шага j как полная функция: 0 на отказах. -/
noncomputable def MasterTrajectory.stepCost (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) (j : ℕ) : ℝ :=
  if h : j < T ∧ m.outs j ≠ Outcome.hold then (m.certs j h.1 h.2).cost else 0

theorem MasterTrajectory.stepDrop_eq (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) {j : ℕ} (hj : j < T)
    (hr : m.outs j ≠ Outcome.hold) :
    m.stepDrop T j = (m.certs j hj hr).drop :=
  by simp [stepDrop, hj, hr]

theorem MasterTrajectory.stepPenalty_eq (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) {j : ℕ} (hj : j < T)
    (hr : m.outs j ≠ Outcome.hold) :
    m.stepPenalty T j = (m.certs j hj hr).penalty :=
  by simp [stepPenalty, hj, hr]

theorem MasterTrajectory.stepCost_eq (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) {j : ℕ} (hj : j < T)
    (hr : m.outs j ≠ Outcome.hold) :
    m.stepCost T j = (m.certs j hj hr).cost :=
  by simp [stepCost, hj, hr]

/-- Бюджетный PREMISE-носитель: суммарная стоимость шагов
траектории ≤ B — как ЭКСПЛИЦИТНЫЙ биндер (потребитель
предъявляет; пин zero-budget наследуется и становится
явным; НЕ ресурсный учёт — co-beat). -/
structure MasterBudgetCert (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) (B : ℝ) where
  /-- Суммарная стоимость всех T шагов ≤ B (premise). -/
  budget_ok : ∑ j ∈ Finset.range T, m.stepCost T j ≤ B


/-! ## ГЛАВНАЯ теорема -/

/-- МАСТЕР-ТЕОРЕМА (детерминированный телескоп над either/or
шагами): после T шагов certified-or-refuse полная цель не выше
начальной минус сумма заявленных drop'ов плюс ЛИНЕЙНАЯ сумма
штрафов сжатия. Отказ (hold) вносит НУЛЕВОЙ drop И
нулевой penalty — по доказательству (тождество состояния,
`holds`), не по конвенции. Движок `obj_telescope_err`
(переиспользование, без новой индукции). -/
theorem master_trajectory_bound (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) :
    fullObjective (m.states T) ≤ fullObjective (m.states 0)
      - ∑ j ∈ Finset.range T, m.stepDrop T j
      + ∑ j ∈ Finset.range T, m.stepPenalty T j := by
  have key : ∀ j < T, fullObjective (m.states (j + 1))
      ≤ fullObjective (m.states j) - m.stepDrop T j
        + m.stepPenalty T j := by
    intro j hj
    by_cases hr : m.outs j = Outcome.hold
    · have hsd : m.stepDrop T j = 0 := by simp [MasterTrajectory.stepDrop, hr]
      have hsp : m.stepPenalty T j = 0 := by
        simp [MasterTrajectory.stepPenalty, hr]
      rw [m.holds j hj hr, hsd, hsp]
      linarith
    · have hd := (m.certs j hj hr).descent
      rw [m.stepDrop_eq T hj hr, m.stepPenalty_eq T hj hr]
      exact hd
  exact obj_telescope_err T (fun j => fullObjective (m.states j))
    (m.stepDrop T) (m.stepPenalty T) key

/-- СЛЕДСТВИЕ (quality floor): итоговая полная цель не выше
начальной плюс суммарный штраф — независимо от drop'ов. -/
theorem master_floor (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) :
    fullObjective (m.states T) ≤ fullObjective (m.states 0)
      + ∑ j ∈ Finset.range T, m.stepPenalty T j := by
  have h := master_trajectory_bound T m
  have hnn : ∀ j ∈ Finset.range T, (0 : ℝ) ≤ m.stepDrop T j := by
    intro j hj
    by_cases hr : m.outs j = Outcome.hold
    · simp [MasterTrajectory.stepDrop, hr]
    · rw [m.stepDrop_eq T (Finset.mem_range.mp hj) hr]
      exact (m.certs j (Finset.mem_range.mp hj) hr).drop_nonneg
  have := Finset.sum_nonneg hnn
  linarith

/-- СЛЕДСТВИЕ (чистый спуск): если все штрафы нулевые (нет
сжатия / ε_q = 0), траектория — чистый сертифицированный спуск. -/
theorem master_descent (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T)
    (hpen : ∀ j ∈ Finset.range T, m.stepPenalty T j = 0) :
    fullObjective (m.states T) ≤ fullObjective (m.states 0)
      - ∑ j ∈ Finset.range T, m.stepDrop T j := by
  have h := master_trajectory_bound T m
  rw [Finset.sum_congr rfl (fun j hj => hpen j hj)] at h
  simp at h
  exact h

/-- СЛЕДСТВИЕ (замкнутая форма): равномерные drop ≥ δ и penalty
≤ ε дают `L(S_T) ≤ L(S_0) − T·δ + T·ε` (паттерн
`rounded_trajectory_uniform`). -/
theorem master_uniform (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) (delta eps : ℝ)
    (hdelta : ∀ j < T, delta ≤ m.stepDrop T j)
    (heps : ∀ j < T, m.stepPenalty T j ≤ eps) :
    fullObjective (m.states T) ≤ fullObjective (m.states 0)
      - T * delta + T * eps := by
  have hmain := master_trajectory_bound T m
  have hsumd : T * delta ≤ ∑ j ∈ Finset.range T, m.stepDrop T j := by
    have hmem : ∀ j ∈ Finset.range T, delta ≤ m.stepDrop T j :=
      fun j hj => hdelta j (Finset.mem_range.mp hj)
    have hcard : ∑ j ∈ Finset.range T, delta = T * delta := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc T * delta = ∑ j ∈ Finset.range T, delta := hcard.symm
      _ ≤ ∑ j ∈ Finset.range T, m.stepDrop T j := Finset.sum_le_sum hmem
  have hsume : ∑ j ∈ Finset.range T, m.stepPenalty T j ≤ T * eps := by
    have hmem : ∀ j ∈ Finset.range T, m.stepPenalty T j ≤ eps :=
      fun j hj => heps j (Finset.mem_range.mp hj)
    have hcard : ∑ j ∈ Finset.range T, eps = T * eps := by
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ∑ j ∈ Finset.range T, m.stepPenalty T j
        ≤ ∑ j ∈ Finset.range T, eps := Finset.sum_le_sum hmem
      _ = T * eps := hcard
  linarith

/-! ## Бюджет: premise-канал + доказанный uniform cap -/

/-- БЮДЖЕТ, доказанная часть: равномерный cap стоимости c на
каждый шаг ⇒ суммарная стоимость ≤ T·c (телескоп-лемма бюджета).
Само B — premise (поле `budget_ok`): честный канал, реальный
ресурсный учёт — пин наследуется. -/
theorem master_budget_uniform (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) (cap : ℝ)
    (hcap : ∀ j < T, m.stepCost T j ≤ cap) :
    ∑ j ∈ Finset.range T, m.stepCost T j ≤ T * cap := by
  have hmem : ∀ j ∈ Finset.range T, m.stepCost T j ≤ cap :=
    fun j hj => hcap j (Finset.mem_range.mp hj)
  have hcard : ∑ j ∈ Finset.range T, cap = T * cap := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ j ∈ Finset.range T, m.stepCost T j
      ≤ ∑ j ∈ Finset.range T, cap := Finset.sum_le_sum hmem
    _ = T * cap := hcard

/-- СЛЕДСТВИЕ (бюджетная форма): равномерный cap c и T·c ≤ B
⇒ суммарная стоимость ≤ B — как канал budget_ok предъявляет
потребитель (premise-канал замкнут доказанной оценкой). -/
theorem master_budget_of_cap (T : ℕ)
    (m : MasterTrajectory (n := n) (a := a) (e := e) (q := q)
      (r := r) (c := c) (k := k) T) (cap B : ℝ)
    (hcap : ∀ j < T, m.stepCost T j ≤ cap)
    (hB : T * cap ≤ B) :
    ∑ j ∈ Finset.range T, m.stepCost T j ≤ B :=
  le_trans (master_budget_uniform T m cap hcap) hB

/-! ## whp-канал: union bound + условный телескоп (паттерн) -/

variable {Ω : Type*} [Fintype Ω]

/-- pmfMean/Finset.sum перестановка (линейность ожидания,
индукция по `pmfMean_add`) — ингредиент union bound. -/
theorem pmfMean_sum_range (law : PMF Ω) (f : ℕ → Ω → ℝ) (T : ℕ) :
    pmfMean law (fun ω => ∑ j ∈ Finset.range T, f j ω)
      = ∑ j ∈ Finset.range T, pmfMean law (f j) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hfun : ∀ ω, ∑ j ∈ Finset.range (T + 1), f j ω
        = (∑ j ∈ Finset.range T, f j ω) + f T ω := by
      intro ω; simp [Finset.sum_range_succ]
    calc pmfMean law (fun ω => ∑ j ∈ Finset.range (T + 1), f j ω)
        = pmfMean law (fun ω =>
            (∑ j ∈ Finset.range T, f j ω) + f T ω) :=
          pmfMean_congr law (fun ω _ => hfun ω)
      _ = pmfMean law (fun ω => ∑ j ∈ Finset.range T, f j ω)
          + pmfMean law (f T) := pmfMean_add law _ _
      _ = ∑ j ∈ Finset.range (T + 1), pmfMean law (f j) := by
          rw [Finset.sum_range_succ, ih]

/-- UNION BOUND (паттерн `stochastic_loop_certified`,
без независимости): если bad-событие шага j имеет вероятность
≤ δ_j, то вероятность того, что ВСЕ T шагов good, ≥ 1 − Σδ_j.
Риск-канал мастера: Σδ_t и есть траекторный риск-бюджет
(δ покрывает descent-отказы шагов; caveats
наследуются). -/
theorem master_union_bound (law : PMF Ω) (good : ℕ → Ω → Prop)
    (T : ℕ) (deltas : ℕ → ℝ)
    (hbad : ∀ j < T, pmfMean law (fun ω =>
      if good j ω then (0 : ℝ) else 1) ≤ deltas j) :
    pmfMean law (fun ω =>
      if ∀ j < T, good j ω then (1 : ℝ) else 0)
      ≥ 1 - ∑ j ∈ Finset.range T, deltas j := by
  have hpoint : ∀ ω : Ω, (1 : ℝ)
      - ∑ j ∈ Finset.range T, (if good j ω then (0 : ℝ) else 1)
      ≤ (if ∀ j < T, good j ω then (1 : ℝ) else 0) := by
    intro ω
    by_cases hall : ∀ j < T, good j ω
    · rw [if_pos hall]
      have hnn' : ∀ j ∈ Finset.range T, (0 : ℝ)
        ≤ (if good j ω then (0 : ℝ) else 1) := fun j _ => by
        by_cases h : good j ω <;> simp [h]
      have hsum := Finset.sum_nonneg hnn'
      linarith
    · rw [if_neg hall]
      push_neg at hall
      obtain ⟨j, hjT, hg⟩ := hall
      have hmem : j ∈ Finset.range T := Finset.mem_range.mpr hjT
      have h1 : (1 : ℝ)
          ≤ ∑ i ∈ Finset.range T, (if good i ω then (0 : ℝ) else 1) := by
        calc (1 : ℝ) = (if good j ω then (0 : ℝ) else 1) := by simp [hg]
          _ ≤ ∑ i ∈ Finset.range T, (if good i ω then (0 : ℝ) else 1) :=
            Finset.single_le_sum
              (f := fun i => (if good i ω then (0 : ℝ) else 1))
              (fun i _ => by by_cases h : good i ω <;> simp [h]) hmem
      linarith
  have h1 : pmfMean law (fun ω => if ∀ j < T, good j ω then (1 : ℝ) else 0)
      ≥ pmfMean law (fun ω => (1 : ℝ)
        - ∑ j ∈ Finset.range T, (if good j ω then (0 : ℝ) else 1)) :=
    pmfMean_mono law (fun a _ => hpoint a)
  rw [pmfMean_sub, pmfMean_const, pmfMean_sum_range] at h1
  have h2 : ∑ j ∈ Finset.range T,
      pmfMean law (fun ω => if good j ω then (0 : ℝ) else 1)
      ≤ ∑ j ∈ Finset.range T, deltas j :=
    Finset.sum_le_sum (fun j hj => hbad j (Finset.mem_range.mp hj))
  linarith

omit [Fintype Ω] in
/-- УСЛОВНЫЙ ТЕЛЕСКОП (честная композиция gap 3): ЕСЛИ на
good-событии (все шаги good при данном ω) пер-шаговое
неравенство мастера выполнено ω-точечно, ТО на good-событии
справедлив мастер-телескоп. Композиция с `master_union_bound`
даёт whp-форму: с вероятностью ≥ 1 − Σδ_t траектория
удовлетворяет мастер-границе. Никакой независимости. -/
theorem master_conditional_bound (T : ℕ)
    (obj : ℕ → Ω → ℝ) (drop_ pen : ℕ → ℝ) (good : ℕ → Ω → Prop)
    (hkey : ∀ ω, (∀ j < T, good j ω) → ∀ j < T,
      obj (j + 1) ω ≤ obj j ω - drop_ j + pen j) :
    ∀ ω, (∀ j < T, good j ω) →
      obj T ω ≤ obj 0 ω
        - ∑ j ∈ Finset.range T, drop_ j
        + ∑ j ∈ Finset.range T, pen j := by
  intro ω hall
  exact obj_telescope_err T (fun j => obj j ω) drop_ pen
    (hkey ω hall)

/-! ## Указатель four-cert (layer 8 — по ссылке) -/

/-- FOUR-CERT УКАЗАТЕЛЬ: принятый шаг мастера с положительным
drop, бюджетным законом ledger'а (premise) и риск-каналом ledger'а
(premise) даёт `FullStepCert` — ингредиент, который
`fourCert_of_parts` (layer 8, Training — LayerLint запрещает
импорт сюда) собирает с growth-книгой (
`growthCert_of_admission`) и macro-книгой в
`FourCertTransition`. Управляющая дихотомия мастера
(accept/refuse) совпадает с дихотомией поэтому каждый
принятый шаг траектории мастера FOUR-CERT-композируем;
`hpen : penalty = 0` — честный мост: FullStepCert
формулируется БЕЗ penalty-канала, поэтому указатель покрывает
бесштрафный (несжатый) случай; сжатый случай потребует
penalty-aware расширения сертификата — co-beat. -/
def master_accept_fullCert {s s' : CanonicalTrainState n a e q r c k}
    (mstep : MasterStepCert s s') (hpos : 0 < mstep.drop)
    (hpen : mstep.penalty = 0)
    (hbnb : 0 ≤ s'.core.res.budget)
    (hbudget : s'.core.res.budget = s.core.res.budget - mstep.cost)
    (rSpend rRem : ℝ) (hrnext : s'.core.saf.risk = rRem)
    (hrsplit : s.core.saf.risk = rSpend + rRem)
    (hrnn : 0 ≤ rRem) :
    FullStepCert s s' where
  drop := mstep.drop
  drop_pos := hpos
  descent := by
    have h1 := mstep.descent
    rw [hpen] at h1
    linarith
  budgetSpend := mstep.cost
  budget_next := hbudget
  budget_nonneg := hbnb
  riskSpend := rSpend
  riskRem := rRem
  risk_next := hrnext
  risk_split := hrsplit
  risk_nonneg := hrnn

end Hagi.Theory

/-! ## MasterBudget — compute budget as a premise channel (ns Hagi.Theory, section labels preserved) -/

/-!
# MasterBudget — resource-ledger bridge for the budget clause

ресурсный мост: premise-канал бюджета
(`MasterBudgetCert`: Σ cost ≤ B как явный биндер потребителя)
закрывается ДОКАЗАННЫМ королларием resource-слоя — телескоп
бюджетного_LEDGERа (`budget_telescope_gen`: терминальный
бюджет = начальный − Σ точных трат) плюс доказанная
неотрицательность остатка (`CertStepGen.budget_nonneg`).
Кап Σ costs ≤ B ВЫВОДИТСЯ, не предполагается.

## Что мостится (bridged)

- Любой cost-канал, реализующий ledger: явная
  instantiation-гипотеза `hmatch` (stepCost = budgetSpend)
  даёт ТОЧНЫЙ баланс Σ costs = budget₀ − budget_T
  (`budget_from_resource_ledger`), а кап — следствие
  неотрицательности терминального остатка
  (`masterBudgetCert_of_resource_ledger` возвращает
  `MasterBudgetCert` как theorem output).
- Демо (KV-cache): per-step cost = cached per-token work
  `cachedTokenWork t = t + 1`; точная сумма
  2·Σ = T·(T+1) (форма `cached_total_work_eq`) закрывает
  budget_ok на ТОЧНОМ cached-тотале (`master_budget_kv_cached`);
  ratio-контекст — `kv_work_ratio` (3·recompute = (n+2)·cached).

## Что остаётся premise-form (честные пины)

- Потребители `MasterBudgetCert` БЕЗ ledger-реализации — кап
  остаётся биндером (наследуется пин).
- (d, W)-фронт (`data_compute_budget`: десцент-рейт и
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
`CertStepGen.budget_next` (паттерн `budget_telescope_gen`,
цитируется; переиспользование доказательства, не результата —
LayerLint-ограничение, не дублирование намерения).
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory

open Hagi.State Hagi.Probability
open scoped BigOperators Classical

variable {n a e q r c k : ℕ}

/-! ## Локальный телескоп ledger-а (паттерн) -/

section Bridge

variable {S TaskId : Type*}
variable (M : Hagi.Cert.SystemMetrics S TaskId)
variable (obl : Hagi.Cert.StepObligations TaskId)

/-- Телескоп ресурсного ledger-а над kernel-полем
`CertStepGen.budget_next` (тот же паттерн
`budget_telescope_gen`; с A18.3/С425 — one-line специализация
обобщённого `additive_ledger_telescope_eq` через budget-инстанс
`Hagi.Cert.ExactAdditiveLedger`). Терминальный бюджет = начальный минус
ТОЧНАЯ сумма per-step трат — закон ресурсного учёта. -/
theorem budget_ledger_telescope (deltaLevel : S → ℝ)
    (T : ℕ) (traj : ℕ → S)
    (steps : ∀ j : ℕ, Hagi.Cert.CertStepGen M obl deltaLevel (traj j) (traj (j + 1))) :
    M.budget (traj T) = M.budget (traj 0)
      - ∑ j ∈ Finset.range T, (steps j).budgetSpend :=
  Hagi.Cert.additive_ledger_telescope_eq (level := M.budget) T traj steps

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
замена premise-канала ресурсным королларием (beat top-2). -/
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

/-! ## Демо: KV-cache cost-модель в budget-клаузе -/

/-- Helper: точная сумма cached per-token работ над T шагами в
форме без деления — 2·Σ_{j<T} ((j:ℝ)+1) = T·(T+1); ℝ-зерка
identity `cached_total_work_eq` (2·cachedTotalWork n =
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

/-- ДЕМО-ИНСТАНЦИАЦИЯ (KV-cache): если per-step стоимость
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


/-! ## VerticalCapstone — accuracy for budget, the vertical capstone (ns Hagi.Unified preserved) -/

set_option linter.style.header false

/-!
# VerticalCapstone — итоговая теорема вертикали: точность за бюджет

Композиция всех звеньев сертифицированной цепи: noisy PL-спуск
(NoisyPL) + термостат-отжиг (ReferenceMachine.batch_anneal_floor).
Рекуррентность `e(t+1) <= q·e(t) + d(t)`, `d(t) = sigma^2/(B0·c^t)`,
q < 1, c > 1 даёт `e(t) <= E* + q^t·(e0 - E*) + sigma^2/B0/(1-q)`:
два экспоненциальных члена (сжатие спуска и охлаждение пола)
плюс консервативный пол d(0)/(1-q). Точность за бюджет
(t циклов, B0·c^t измерений) в закрытой форме.
-/

namespace Hagi.Unified

/-- Лемма о стационарном члене: `q·x/(1-q) + x = x/(1-q)`
при `q < 1`. -/
theorem affine_stationary (q x : ℝ) (hq1 : q < 1) :
    q * (x / (1 - q)) + x = x / (1 - q) := by
  have hd : (0:ℝ) < 1 - q := by linarith
  field_simp
  ring

/-- КАПСТОН ВЕРТИКАЛИ: noisy-спуск с отжигающим полом
`d(t) = sigma^2/(B0·c^t)`: `e t <= Estar + q^t·(e0 - Estar)
+ sigma^2/B0/(1-q)` — спуск сжимает начальный зазор
экспоненциально, отжиг измерений опускает пол (floor(t)
<= d(0)/(1-q) — консервативная закрытая форма). Точность за
бюджет: t циклов + B0·c^t измерений. -/
theorem accuracy_for_budget (e : ℕ → ℝ) (Estar q sigma B0 c : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hsigma : 0 ≤ sigma)
    (hB0 : 0 < B0) (hc1 : 1 < c) (hEstar0 : 0 ≤ Estar)
    (hstep : ∀ s, e (s + 1) ≤ q * e s + sigma ^ 2 / (B0 * c ^ s))
    (t : ℕ) :
    e t ≤ Estar + q ^ t * (e 0 - Estar)
      + sigma ^ 2 / B0 / (1 - q) := by
  have hqpos : (0:ℝ) < 1 - q := by linarith
  have hstep' : ∀ s, (e (s + 1) - Estar)
      ≤ q * (e s - Estar) + sigma ^ 2 / (B0 * c ^ s) := by
    intro s
    have h0 := hstep s
    have hdist : q * (e s - Estar) = q * e s - q * Estar := by
      ring
    rw [hdist]
    have hpos : (0:ℝ) ≤ (1 - q) * Estar := by
      exact mul_nonneg (by linarith) hEstar0
    linarith
  have hmain : ∀ t : ℕ, (e t - Estar)
      ≤ q ^ t * (e 0 - Estar)
        + sigma ^ 2 / B0 / (1 - q) := by
    intro t
    induction t with
    | zero =>
      have h2 : (0:ℝ) ≤ sigma ^ 2 / B0 / (1 - q) := by
        positivity
      linarith
    | succ t ih =>
      have hst := hstep' t
      have hshift : e t - Estar
          ≤ q ^ t * (e 0 - Estar)
            + sigma ^ 2 / B0 / (1 - q) := ih
      have hA : q * (sigma ^ 2 / B0 / (1 - q))
          + sigma ^ 2 / (B0 * c ^ t)
          ≤ sigma ^ 2 / B0 / (1 - q) := by
        have hcore := affine_stationary q (sigma ^ 2 / B0) hq1
        have hle : sigma ^ 2 / (B0 * c ^ t) ≤ sigma ^ 2 / B0 := by
          have hc0 : (0:ℝ) < c := by linarith
          have hpow1 : (1:ℝ) ≤ c ^ t := by
            have hmono : (1:ℝ) ≤ c := by linarith
            exact one_le_pow₀ hmono (n := t)
          have hden : B0 * 1 ≤ B0 * c ^ t :=
            mul_le_mul_of_nonneg_left hpow1 (le_of_lt hB0)
          rw [mul_one] at hden
          exact div_le_div_of_nonneg_left (sq_nonneg sigma)
            hB0 hden
        linarith [hcore, hle]
      calc e (t + 1) - Estar
          ≤ q * (e t - Estar)
            + sigma ^ 2 / (B0 * c ^ t) := hst
        _ ≤ q * (q ^ t * (e 0 - Estar)
              + sigma ^ 2 / B0 / (1 - q))
            + sigma ^ 2 / (B0 * c ^ t) := by
            have h1 := mul_le_mul_of_nonneg_left hshift hq
            linarith
        _ ≤ q ^ (t + 1) * (e 0 - Estar)
            + sigma ^ 2 / B0 / (1 - q) := by
            have hdist : q * (q ^ t * (e 0 - Estar))
                = q ^ (t + 1) * (e 0 - Estar) := by
              rw [pow_succ]
              ring
            linarith [hdist, hA]
  linarith [hmain t]

end Hagi.Unified

