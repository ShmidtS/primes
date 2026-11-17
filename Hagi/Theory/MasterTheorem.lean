import Mathlib.Tactic
import Hagi.State.TrainTrajectory
import Hagi.Unified.StochasticLoop

/-!
# MasterTheorem — сборная траекторная теорема certified-or-refuse

C392, центральная теорема A17 (audit's master statement):

«EITHER performs a certified update with controlled descent and
preserved constraints, OR safely refuses; across the trajectory
total quality loss, risk, compute budget stay within proven
bounds.»

## Clause-by-clause honesty audit (mapping)

| Пункт аудита | Формальный пункт |
|---|---|
| EITHER certified update | `MasterStepCert` (drop ≥ 0, penalty ≥ 0 — форма C389 `2·L_lip·ε_q`, cost ≥ 0, спуск `fullObjective s' ≤ fullObjective s − drop + penalty`) |
| OR safely refuses | `MasterTrajectory.holds`: hold ⇒ тождество состояния (семантика C363 `hold_rollback_total`; та же дихотомия у C388 `hold_refusal_safe` и C390 `refuse_safe`) |
| total quality loss bounded | `master_trajectory_bound` (ТЕЛЕСКОП C375 `obj_telescope_err`, линейное накопление penalty) |
| compute budget in proven bounds | `MasterBudgetCert` (PREMISE-канал: Σ cost ≤ B, потребительский биндер) + доказанный `master_budget_uniform` (cap c ⇒ Σ ≤ T·c) |
| risk in proven bounds | whp-канал: `master_union_bound` (P[all good] ≥ 1 − Σδ_t, паттерн C353) + `master_conditional_bound` (телескоп на good-событии) |
| preserved constraints | указатель `master_accept_fullCert` (C363 FullStepCert) → C383 `fourCert_of_parts` (layer 8) + C380/C390 книги |

## Честные пины (premise-form)

- **Бюджет — premise-канал.** `MasterBudgetCert` — явный
  биндер, НЕ ресурсный учёт: пин C388 (budget = 0 zero-channel)
  наследуется и становится явным. Реальный учёт — co-beat.
- **EF residual, траекторный член — ПИН.** C381 endpoint-формы
  (`ef_compressed_step_bound`) цитируются; Σ‖e_t‖-телескоп —
  co-beat (C391 ranked #2).
- **PL-геометрия (C351/C357) — ПИН.** Теоремы живут на CE-reg
  носителе (`ce_global_convergence_reg_closed`), не на
  `fullObjective` канонического состояния; композиция требует
  carrier-моста (co-beat). Здесь: `master_uniform` даёт линейную
  замкнутую форму, геометрическая — при мосте.
- **whp — условно-на-good-событиях** (даунгрейд C391 gap 3):
  union bound без независимости; δ-бюджет покрывает только
  descent-отказы шагов (caveats C353/C380 наследуются).
- **Four-cert — указатель.** LayerLint: Training (8) > Theory (7),
  `fourCert_of_parts` не импортируем — конструктивен до layer 3
  (`FullStepCert`), завершение композиции описано в docstring.
- Адаптивные данные: caveats C380 (e-process fresh-data premise)
  наследуются без изменений.
-/

set_option relaxedAutoImplicit false

namespace Hagi.Theory

open Hagi.State Hagi.Probability
open scoped BigOperators Classical

variable {n a e q r c k : ℕ}

/-! ## Сертификат одного шага: certified-or-refuse -/

/-- Сертификат ПРИНЯТОГО шага мастера: контролируемый спуск
(заявленный drop ≥ 0), аддитивный penalty ≥ 0 (форма C389:
2·L_lip·ε_q на сжатых эндпоинтах), стоимость cost ≥ 0 (канал
бюджета) и доказанный спуск полной цели с penalty. Refusal НЕ
носит этот сертификат — refusal это Hold (см.
`MasterTrajectory.holds`). -/
structure MasterStepCert (s s' : CanonicalTrainState n a e q r c k) where
  /-- Заявленный спуск полной цели (certified drop). -/
  drop : ℝ
  /-- Спуск неотрицателен. -/
  drop_nonneg : 0 ≤ drop
  /-- Аддитивный штраф сжатия (форма C389: 2·L_lip·ε_q). -/
  penalty : ℝ
  /-- Штраф неотрицателен. -/
  penalty_nonneg : 0 ≤ penalty
  /-- Стоимость шага (канал бюджета, premise-binder). -/
  cost : ℝ
  /-- Стоимость неотрицательна. -/
  cost_nonneg : 0 ≤ cost
  /-- Спуск ПОЛНОЙ цели с штрафом:(weights+буферы, C363). -/
  descent : fullObjective s' ≤ fullObjective s - drop + penalty

/-- Траектория мастера: T шагов на каноническом состоянии, каждый
шаг ЛИБО сертифицированный accept (`outs j ≠ hold` несёт
`MasterStepCert`), ЛИБО отказ (`outs j = hold` ⇒ тождество
состояния, C363 Hold). Бюджет B — PREMISE-канал (`MasterBudgetCert`): суммарная
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


/-! ## Тотальные функции шагов (паттерн C375 stepDrop) -/

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
предъявляет; пин C388 zero-budget наследуется и становится
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
штрафов сжатия (форма C389). Отказ (hold) вносит НУЛЕВОЙ drop И
нулевой penalty — по доказательству (тождество состояния,
`holds`), не по конвенции. Движок — C375 `obj_telescope_err`
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
≤ ε дают `L(S_T) ≤ L(S_0) − T·δ + T·ε` (паттерн C375
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
ресурсный учёт — пин C388, наследуется. -/
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

/-! ## whp-канал: union bound + условный телескоп (паттерн C353) -/

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

/-- UNION BOUND (паттерн C353 `stochastic_loop_certified`,
без независимости): если bad-событие шага j имеет вероятность
≤ δ_j, то вероятность того, что ВСЕ T шагов good, ≥ 1 − Σδ_j.
Риск-канал мастера: Σδ_t и есть траекторный риск-бюджет
(δ покрывает descent-отказы шагов; caveats C353/C380
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

/-! ## Указатель four-cert (C383, layer 8 — по ссылке) -/

/-- FOUR-CERT УКАЗАТЕЛЬ: принятый шаг мастера с положительным
drop, бюджетным законом ledger'а (premise) и риск-каналом ledger'а
(premise) даёт C363 `FullStepCert` — ингредиент, который C383
`fourCert_of_parts` (layer 8, Training — LayerLint запрещает
импорт сюда) собирает с growth-книгой (C390
`growthCert_of_admission`) и macro-книгой (C380) в
`FourCertTransition`. Управляющая дихотомия мастера
(accept/refuse) совпадает с дихотомией C388/C390, поэтому каждый
принятый шаг траектории мастера FOUR-CERT-композируем;
`hpen : penalty = 0` — честный мост: FullStepCert (C363)
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
