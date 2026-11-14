/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Contracts.GatePipeline
set_option linter.style.header false
set_option linter.dupNamespace false

/-!
# Audit ledger (C274, audit item E7): Lean bridge for the Python
HoeffdingAudit protocol

Аудит-протокол (A10 synthesis) — это протокол НЕПРЕРЫВНОГО
тестирования: измерения нарезаются на непересекающиеся срезы,
каждая проверка тратит свой кусок α-бюджета, отклонённый кандидат
сжигает свой срез, финальный тест держится нетронутым. Этот модуль
формализует протокол как машину состояний над срезами тестов
(AuditLedger) и СВЯЗЫВАЕТ её инварианты с уже доказанными
статистическими границами C264/CertifiedEstimator — мост есть
суть задания E7, новая концентрационная математика не выводится.

**Соответствие полей компонентам Python-протокола (HoeffdingAudit):**

* `spent` (α per task) — alpha spending: пер-задачный расход
  доверительного бюджета; `audit_consume_alpha_exact` — расход
  уменьшает остаток РОВНО на α, `audit_consume_alpha_valid` —
  неотрицательный остаток — инвариант (Σ spent ≤ δtotal);
* `streamsDisjoint` — disjoint audit cursors / proposal-independent
  slices: потоки — ПОЛУИНТЕРВАЛЫ [lo, hi) на ℕ с попарным
  непересечением (простые интервалы, никакой общей топологии —
  KISS); `audit_streams_disjoint` — инвариант сохраняется шагами
  протокола (продвижение курсора не меняет lo/hi);
* старые задачи / floors — `floors` (taskId → floor metric value)
  хранит repeat-task floors; вред старым задачам входит через
  события Bad t в мастер-теореме `audit_false_harm_bounded`;
* текущий выигрыш (current gain) — дополнение: нет ложного вреда ⟹
  зарепорченные выигрыши над floors реальны (честно НЕ
  формализуется отдельно — потребовала бы полной семантики гейта);
* `rejected` + `audit_rejected_consumed` — rejected-candidate
  consumption: отклонённый кандидат сжигает срез — потреблённые
  индексы НИКОГДА не попадут в свежий срез никакого потока
  (курсоры только вперёд);
* `finalTest`/`finalLo`/`finalHi` + `final_test_untouched`,
  `audit_touch_final_flips`, `audit_touch_final_breaks` —
  final test untouched: пока флаг false, никакой поток не покрывает
  индексы финального теста; касание финального теста переключает
  флаг, и валидность аудита требует flag = false.

**Мост к C264/CertifiedEstimator:**

* `audit_false_harm_bounded` (MASTER): P(Bad t) ≤ spent t для
  каждого t ⟹ P(ни одного ложного вреда старым задачам за весь
  протокол) ≥ 1 − δtotal — ПРЯМОЕ применение
  `gate_pipeline_false_commit` с β := spent, δ := δtotal;
* `audit_alpha_spends_radius`: если Hoeffding-радиус
  2e^{−2nε²} (`hoeffding_two_sided` CertifiedEstimator) ≤ spent t,
  хвостовое событие покрыто бюджетом — радиус ОПРАВДЫВАЕТ расход
  (анализ гейта A10: расход α не меньше цены границы).

**Честная граница**: модуль формализует БУХГАЛТЕРИЮ протокола и её
мост к концентрации; семантика самих метрик (каким измерением
получен floor) остаётся на стороне измерения, как и в
CertifiedEstimator/GatePipeline.
-/

open Finset Real

namespace Hagi.Contracts.AuditLedger

/-! ## Срезы тестов -/

/-- Один поток аудита: полуинтервал [lo, hi) индексов образцов с
курсором (все индексы ниже курсора потреблены). Соответствует
disjoint audit cursor одного потока проверок Python-протокола
(proposal-independent slice: срез задаётся ТОЛЬКО интервалом
индексов, никак свойствами кандидата). -/
structure AuditStream where
  /-- Нижняя граница среза (включительно). -/
  lo : ℕ
  /-- Верхняя граница среза (исключительно). -/
  hi : ℕ
  /-- Позиция курсора: индексы < cursor потреблены. -/
  cursor : ℕ
  /-- Курсор не левее среза (поле-инвариант). -/
  lo_le_cursor : lo ≤ cursor
  /-- Курсор не правее среза (поле-инвариант). -/
  cursor_le_hi : cursor ≤ hi

/-! ## Реестр аудита -/

variable {σ : Type} [Fintype σ] [DecidableEq σ] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Реестр аудита — машина состояний протокола над срезами тестов.
Поля-инварианты (streamsDisjoint, spentNonneg, spentTotal,
finalIsolated) поддерживаются каждым шагом протокола
(`audit_consume_alpha_valid`, `audit_streams_disjoint`). -/
structure AuditLedger (σ : Type) [Fintype σ] [DecidableEq σ]
    (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- Суммарный доверительный бюджет протокола (δ_total). -/
  δtotal : ℝ
  /-- Потоки аудита: по одному полуинтервалу на поток. -/
  streams : σ → AuditStream
  /-- Repeat-task floors: taskId → floor metric value (старые
  задачи; вред им входит через Bad t в мастер-теореме). -/
  floors : ι → ℝ
  /-- Alpha spending: потраченный α per task (старый расход). -/
  spent : ι → ℝ
  /-- Счётчик отклонённых кандидатов (rejected consumption). -/
  rejected : ℕ
  /-- Флаг финального теста: false = финальный тест ещё нетронут. -/
  finalTest : Bool
  /-- Нижняя граница полуинтервала финального теста. -/
  finalLo : ℕ
  /-- Верхняя граница полуинтервала финального теста. -/
  finalHi : ℕ
  /-- ИНВАРИАНТ disjoint cursors: потоки попарно не пересекаются
  (полуинтервалы упорядочены) — proposal-independent slices. -/
  streamsDisjoint : ∀ s t, s ≠ t →
    (streams s).hi ≤ (streams t).lo ∨ (streams t).hi ≤ (streams s).lo
  /-- ИНВАРИАНТ: расход неотрицателен per task. -/
  spentNonneg : ∀ t, 0 ≤ spent t
  /-- ИНВАРИАНТ: суммарный расход в бюджете (Σ spent ≤ δtotal). -/
  spentTotal : ∑ t, spent t ≤ δtotal
  /-- ИНВАРИАНТ held-out: пока финальный тест не тронут (flag =
  false), каждый поток вне [finalLo, finalHi). -/
  finalIsolated : finalTest = false → ∀ s,
    (streams s).hi ≤ finalLo ∨ finalHi ≤ (streams s).lo

/-! ## Остаток бюджета и alpha spending -/

/-- Остаток бюджета задачи t (per-task remaining δ). -/
def remainingOf (L : AuditLedger σ ι) (t : ι) : ℝ := L.δtotal - L.spent t

/-- Неотрицательный остаток: spent t ≤ Σ spent ≤ δtotal
(nonneg remainder invariant). -/
theorem audit_remaining_nonneg (L : AuditLedger σ ι) (t : ι) :
    0 ≤ remainingOf L t := by
  have hle : L.spent t ≤ ∑ u ∈ Finset.univ, L.spent u :=
    Finset.single_le_sum (f := fun u => L.spent u)
      (fun u _ => L.spentNonneg u) (Finset.mem_univ t)
  unfold remainingOf
  linarith [L.spentTotal]

/-- Трата α на задачу t — валидный шаг протокола при 0 ≤ α и
α ≤ свободного остатка суммарного бюджета; меняет только spent
(и поддерживает все поля-инварианты). -/
def auditSpend (L : AuditLedger σ ι) (t : ι) (α : ℝ)
    (hα : 0 ≤ α) (hle : α ≤ L.δtotal - ∑ u, L.spent u) :
    AuditLedger σ ι where
  δtotal := L.δtotal
  streams := L.streams
  floors := L.floors
  spent := fun u => L.spent u + if u = t then α else 0
  rejected := L.rejected
  finalTest := L.finalTest
  finalLo := L.finalLo
  finalHi := L.finalHi
  streamsDisjoint := L.streamsDisjoint
  spentNonneg := by
    intro u
    by_cases h : u = t
    · rw [h, if_pos rfl]
      exact add_nonneg (L.spentNonneg t) hα
    · rw [if_neg h, add_zero]
      exact L.spentNonneg u
  spentTotal := by
    have hsplit : ∑ u, (L.spent u + if u = t then α else 0)
        = (∑ u, L.spent u) + α := by
      rw [Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ t (fun _ => α)]
      simp
    rw [hsplit]
    linarith [L.spentTotal]
  finalIsolated := L.finalIsolated

/-- Расход α уменьшает остаток задачи t РОВНО на α (exact
decrement: α_k спендится с remaining δ поточно). -/
theorem audit_consume_alpha_exact (L : AuditLedger σ ι) (t : ι)
    (α : ℝ) (hα : 0 ≤ α) (hle : α ≤ L.δtotal - ∑ u, L.spent u) :
    (auditSpend L t α hα hle).spent t = L.spent t + α ∧
      remainingOf (auditSpend L t α hα hle) t
        = remainingOf L t - α := by
  constructor
  · show L.spent t + (if t = t then α else 0) = L.spent t + α
    rw [if_pos rfl]
  · show L.δtotal - (L.spent t + (if t = t then α else 0))
      = (L.δtotal - L.spent t) - α
    rw [if_pos rfl]
    ring

/-- Инварианты реестра переживают трату α: суммарный расход
растёт ровно на α и остаётся ≤ δtotal; остаток задачи t
неотрицателен (nonneg remainder invariant). -/
theorem audit_consume_alpha_valid (L : AuditLedger σ ι) (t : ι)
    (α : ℝ) (hα : 0 ≤ α) (hle : α ≤ L.δtotal - ∑ u, L.spent u) :
    ∑ u, (auditSpend L t α hα hle).spent u = (∑ u, L.spent u) + α ∧
      ∑ u, (auditSpend L t α hα hle).spent u ≤ L.δtotal ∧
      0 ≤ remainingOf (auditSpend L t α hα hle) t := by
  refine ⟨?_, ?_, ?_⟩
  · have hsplit : ∑ u, (L.spent u + if u = t then α else 0)
        = (∑ u, L.spent u) + α := by
      rw [Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ t (fun _ => α)]
      simp
    exact hsplit
  · show ∑ u, (L.spent u + if u = t then α else 0) ≤ L.δtotal
    have hsplit : ∑ u, (L.spent u + if u = t then α else 0)
        = (∑ u, L.spent u) + α := by
      rw [Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ t (fun _ => α)]
      simp
    rw [hsplit]
    linarith [L.spentTotal]
  · exact audit_remaining_nonneg (auditSpend L t α hα hle) t

/-! ## Disjoint cursors: шаги протокола -/

/-- Поток после продвижения курсора s на k: только курсор s
меняется (границы срезов не трогаются). -/
def advStream (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) :
    σ → AuditStream :=
  fun u =>
    if u = s then
      ⟨(L.streams s).lo, (L.streams s).hi,
        (L.streams s).cursor + k,
        by have h1 := (L.streams s).lo_le_cursor; omega,
        by omega⟩
    else L.streams u

theorem advStream_of_ne (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) (u : σ)
    (h : u ≠ s) : advStream L s k hk u = L.streams u := by
  unfold advStream
  rw [if_neg h]

theorem advStream_self (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) :
    advStream L s k hk s =
      ⟨(L.streams s).lo, (L.streams s).hi,
        (L.streams s).cursor + k,
        by have h1 := (L.streams s).lo_le_cursor; omega, hk⟩ := by
  unfold advStream
  rw [if_pos rfl]

theorem advStream_lo (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) (u : σ) :
    (advStream L s k hk u).lo = (L.streams u).lo := by
  by_cases h : u = s
  · simp [advStream, h]
  · simp [advStream, h]

theorem advStream_hi (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) (u : σ) :
    (advStream L s k hk u).hi = (L.streams u).hi := by
  by_cases h : u = s
  · simp [advStream, h]
  · simp [advStream, h]

theorem advStream_cursor_self (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) :
    (advStream L s k hk s).cursor = (L.streams s).cursor + k := by
  simp [advStream]

theorem advStream_cursor_of_ne (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) (u : σ)
    (h : u ≠ s) :
    (advStream L s k hk u).cursor = (L.streams u).cursor := by
  simp [advStream, h]

theorem advStream_hi_self (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) :
    (advStream L s k hk s).hi = (L.streams s).hi := by
  simp [advStream]

/-- Продвижение курсора потока s на k шагов (валидно при
cursor + k ≤ hi) — потребление среза без изменения границ. -/
def auditAdvance (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) :
    AuditLedger σ ι where
  δtotal := L.δtotal
  streams := advStream L s k hk
  floors := L.floors
  spent := L.spent
  rejected := L.rejected
  finalTest := L.finalTest
  finalLo := L.finalLo
  finalHi := L.finalHi
  streamsDisjoint := by
    intro u v huv
    have hlo_u := advStream_lo L s k hk u
    have hlo_v := advStream_lo L s k hk v
    have hhi_u := advStream_hi L s k hk u
    have hhi_v := advStream_hi L s k hk v
    rcases L.streamsDisjoint u v huv with h | h
    · exact Or.inl (by rw [hhi_u, hlo_v]; exact h)
    · exact Or.inr (by rw [hhi_v, hlo_u]; exact h)
  spentNonneg := L.spentNonneg
  spentTotal := L.spentTotal
  finalIsolated := by
    intro hflag u
    rcases L.finalIsolated hflag u with h | h
    · exact Or.inl (by rw [advStream_hi L s k hk u]; exact h)
    · exact Or.inr (by rw [advStream_lo L s k hk u]; exact h)

/-- ИНВАРИАНТ disjoint cursors сохраняется продвижением (slices
remain proposal-independent): продвижение трогает ТОЛЬКО курсор —
границы срезов не меняются, попарное непересечение — по построению
(шаг протокола не может сломать независимость срезов). -/
theorem audit_streams_disjoint (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) (u v : σ)
    (huv : u ≠ v) :
    ((auditAdvance L s k hk).streams u).hi
      ≤ ((auditAdvance L s k hk).streams v).lo
      ∨ ((auditAdvance L s k hk).streams v).hi
        ≤ ((auditAdvance L s k hk).streams u).lo :=
  (auditAdvance L s k hk).streamsDisjoint u v huv

/-- Отклонение кандидата: продвижение курсора потока s + инкремент
счётчика rejected. -/
def auditReject (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi) :
    AuditLedger σ ι where
  δtotal := L.δtotal
  streams := (auditAdvance L s k hk).streams
  floors := L.floors
  spent := L.spent
  rejected := L.rejected + 1
  finalTest := L.finalTest
  finalLo := L.finalLo
  finalHi := L.finalHi
  streamsDisjoint := (auditAdvance L s k hk).streamsDisjoint
  spentNonneg := L.spentNonneg
  spentTotal := L.spentTotal
  finalIsolated := (auditAdvance L s k hk).finalIsolated

/-! ## Rejected consumption: потреблённое не возвращается -/

/-- Индексы, потреблённые потоком (ниже его курсора). -/
def consumedIdx (S : AuditStream) (i : ℕ) : Prop :=
  S.lo ≤ i ∧ i < S.cursor

/-- Индексы свежего среза потока (над курсором, внутри [lo, hi)):
именно из них берутся будущие проверки; курсоры двигаются только
вперёд, поэтому свежие срезы только сужаются. -/
def freshIdx (S : AuditStream) (i : ℕ) : Prop :=
  S.cursor ≤ i ∧ i < S.hi

/-- Rejected-candidate consumption: индекс, потреблённый
отклонённым потоком s (ниже ЕГО продвинутого курсора в состоянии
ПОСЛЕ отклонения), НЕ лежит в свежем срезе НИКАКОГО потока t в том
же состоянии — те образцы уже никогда не войдут в поздний принятый
аудит: дальнейшие шаги протокола только двигают курсоры вперёд,
поэтому свежие срезы только сужаются (случай t = s — противоречие
с продвинутым курсором; случай t ≠ s — попарное непересечение
полуинтервалов). -/
theorem audit_rejected_consumed (L : AuditLedger σ ι) (s : σ) (k : ℕ)
    (hk : (L.streams s).cursor + k ≤ (L.streams s).hi)
    (t : σ) (i : ℕ)
    (hc : consumedIdx ((auditReject L s k hk).streams s) i) :
    ¬ freshIdx ((auditReject L s k hk).streams t) i := by
  by_cases h : t = s
  · subst h
    have e1 : ((auditReject L t k hk).streams t).lo
        = (L.streams t).lo := by
      simp only [auditReject, auditAdvance, advStream, ite_true]
    have e2 : ((auditReject L t k hk).streams t).cursor
        = (L.streams t).cursor + k := by
      simp only [auditReject, auditAdvance, advStream, ite_true]
    have e3 : ((auditReject L t k hk).streams t).hi
        = (L.streams t).hi := by
      simp only [auditReject, auditAdvance, advStream, ite_true]
    unfold consumedIdx at hc
    rw [e1, e2] at hc
    obtain ⟨hc1, hc2⟩ := hc
    intro hf
    unfold freshIdx at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [e2] at hf1
    rw [e3] at hf2
    omega
  · have e1 : ((auditReject L s k hk).streams s).lo
        = (L.streams s).lo := by
      simp only [auditReject, auditAdvance, advStream, ite_true]
    have e2 : ((auditReject L s k hk).streams s).cursor
        = (L.streams s).cursor + k := by
      simp only [auditReject, auditAdvance, advStream, ite_true]
    have e3 : ((auditReject L s k hk).streams t).cursor
        = (L.streams t).cursor := by
      simp only [auditReject, auditAdvance, advStream, if_neg h]
    have e4 : ((auditReject L s k hk).streams t).hi
        = (L.streams t).hi := by
      simp only [auditReject, auditAdvance, advStream, if_neg h]
    unfold consumedIdx at hc
    rw [e1, e2] at hc
    obtain ⟨hc1, hc2⟩ := hc
    intro hf
    unfold freshIdx at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [e3] at hf1
    rw [e4] at hf2
    have hlo_s := (L.streams s).lo_le_cursor
    have hhi_s := (L.streams s).cursor_le_hi
    have hlo_t := (L.streams t).lo_le_cursor
    have hhi_t := (L.streams t).cursor_le_hi
    rcases L.streamsDisjoint s t (Ne.symm h) with hcase | hcase
    · omega
    · omega

/-! ## Мастер-теорема: связка с C264 gate_pipeline_false_commit -/

/-- MASTER (E7): если событие Bad t «floor старой задачи t
ложно пострадал» имеет вероятность ≤ spent t (форма
CertifiedEstimator e^{−2nε²}, см. `audit_alpha_spends_radius`), то
вероятность, что НИ одна старая задача не пострадает ложно за весь
протокол, ≥ 1 − δtotal. ПРЯМОЕ применение C264
`gate_pipeline_false_commit` с β := spent, δ := δtotal —
инвариант-поле spentTotal реестра есть в точности посылка Σ β ≤ δ
гейта; новая union-математика НЕ выводится (challenge-pin
плана C274). -/
theorem audit_false_harm_bounded {V : Type} [Fintype V] [Nonempty V]
    {n : ℕ} (L : AuditLedger σ ι) (p : Fin n → V → ℝ)
    (hp : Hagi.Probability.IsProbSys p)
    (Bad : ι → (Fin n → V) → Prop) [∀ t, DecidablePred (Bad t)]
    [DecidablePred (fun ω => ∀ t ∈ (Finset.univ : Finset ι), ¬ Bad t ω)]
    (htail : ∀ t, Hagi.Probability.prodPq p (Bad t) ≤ L.spent t) :
    1 - L.δtotal ≤ Hagi.Probability.prodPq p
      (fun ω => ∀ t ∈ (Finset.univ : Finset ι), ¬ Bad t ω) :=
  Hagi.Contracts.GatePipeline.gate_pipeline_false_commit p hp Bad
    L.spent htail L.spentTotal

/-- Мост радиуса: если Hoeffding-радиус 2e^{−2nε²}
(CertifiedEstimator `hoeffding_two_sided`) помещается в потраченный
α задачи t, то двустороннее хвостовое событие покрыто бюджетом
реестра — радиус ОПРАВДЫВАЕТ расход (расход α не меньше цены
границы; анализ A10 гейта). -/
theorem audit_alpha_spends_radius {V : Type} [Fintype V] [Nonempty V]
    {n : ℕ} (L : AuditLedger σ ι) (t : ι)
    (p : Fin n → V → ℝ) (hp : Hagi.Probability.IsProbSys p)
    (X : Fin n → V → ℝ) (hX : ∀ i v, 0 ≤ X i v ∧ X i v ≤ 1)
    (hn : 0 < n) (eps : ℝ) (heps : 0 < eps)
    (hr : 2 * Real.exp (- 2 * (n : ℝ) * eps ^ 2) ≤ L.spent t) :
    Hagi.Probability.prodPq p
      (fun ω => (n : ℝ) * eps ≤ Hagi.Probability.centeredSum p X ω
        ∨ Hagi.Probability.centeredSum p X ω ≤ - (n : ℝ) * eps)
      ≤ L.spent t :=
  le_trans
    (Hagi.Probability.hoeffding_two_sided p hp X hX hn eps heps) hr

/-! ## Финальный тест: held-out гарантия -/

/-- Индекс внутри среза потока s (полуинтервал [lo, hi)). -/
def streamIdx (L : AuditLedger σ ι) (s : σ) (i : ℕ) : Prop :=
  (L.streams s).lo ≤ i ∧ i < (L.streams s).hi

/-- Индекс внутри полуинтервала финального теста. -/
def finalIdx (L : AuditLedger σ ι) (i : ℕ) : Prop :=
  L.finalLo ≤ i ∧ i < L.finalHi

/-- Held-out гарантия (final test untouched): пока флаг финального
теста false, НИ один поток аудита не покрывает индекс финального
теста — поле-инвариант finalIsolated плюс курсор в границах среза. -/
theorem final_test_untouched (L : AuditLedger σ ι)
    (hflag : L.finalTest = false) (s : σ) (i : ℕ)
    (hIn : streamIdx L s i) : ¬ finalIdx L i := by
  obtain ⟨h1, h2⟩ := hIn
  have hcur := (L.streams s).lo_le_cursor
  have hcur2 := (L.streams s).cursor_le_hi
  rcases L.finalIsolated hflag s with h | h
  · rintro ⟨hf1, hf2⟩
    omega
  · rintro ⟨hf1, hf2⟩
    omega

/-- Касание финального теста: запуск финальной оценки переключает
флаг (финальный тест выполняется ОДИН раз, после аудитов). -/
def auditTouchFinal (L : AuditLedger σ ι) : AuditLedger σ ι where
  δtotal := L.δtotal
  streams := L.streams
  floors := L.floors
  spent := L.spent
  rejected := L.rejected
  finalTest := true
  finalLo := L.finalLo
  finalHi := L.finalHi
  streamsDisjoint := L.streamsDisjoint
  spentNonneg := L.spentNonneg
  spentTotal := L.spentTotal
  finalIsolated := by
    intro hflag
    exact absurd hflag (by simp)

/-- Касание переключает флаг: finalTest = true после
`auditTouchFinal`. -/
theorem audit_touch_final_flips (L : AuditLedger σ ι) :
    (auditTouchFinal L).finalTest = true := rfl

/-- Аудит-валидность held-out состояния: финальный тест ещё не
запущен (flag = false) — необходимое условие валидности аудита. -/
def auditFinalHolds (L : AuditLedger σ ι) : Prop := L.finalTest = false

/-- После касания финального теста held-out валидность нарушена:
аудит с тронутым финальным тестом больше не является валидным
аудитом (flag = false — необходимое условие). -/
theorem audit_touch_final_breaks (L : AuditLedger σ ι) :
    ¬ auditFinalHolds (auditTouchFinal L) := by
  unfold auditFinalHolds
  simp [auditTouchFinal]

end Hagi.Contracts.AuditLedger
