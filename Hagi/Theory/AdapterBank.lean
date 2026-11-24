/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/

import Mathlib.Tactic
import Hagi.Theory.AdapterGrowth

/-!
# AdapterBank — bank доменных адаптеров + warm-start

Source-anchored мост к HAGI_v2 (волны 210/210b): upstream-код
реализовал bank per-domain адаптеров и warm-start перенос — этот
модуль формализует семантику КОДА точно.

Upstream source-anchors (C:\HAGI_v2, read-only):
- `hagi/trunk_ops.py:310-345` — класс `AdapterBank`: per-domain
  independent adapters, ONE shared trunk/head + isolated low-rank
  side-branches; apply — residual через СВОЙ слот только
  («isolation by construction, forgetA=0 bit-exact»);
- `hagi/trunk_ops.py:286-303` — adapter_warm_start: копия
  факторов src в dst («copy semantics — source untouched by
  construction»);
- `hagi/unified.py:147-165` — wave210 использование: fresh слот
  нейтрален (B=0 ⇒ identity), certified-обучение только
  fresh-домена;
- `hagi/lm.py:770-777` — forward `x + B(A x)` из своего слота.

Формализация:
- банк = тотальная карта `ι → AdaptState r d` (слоты гомогенные
  d×r — как `dict[str, LowRankAdapter]` с одним (d, r));
- `bankUpdate bank j a` — обновление РОВНО одного слота j
  (семантика get/apply/transfer: трогают один слот);
- `warmTransfer bank src dst` — копия слота src в слот dst
  (adapter_warm_start).

Теоремы:
- `adapter_bank_isolation` — структурная изоляция:
  гипотеза `s' i = s i` у `adapter_isolation_zero_forgetting`
  становится СТРУКТУРНЫМ фактом (достаточно `i ≠ j`);
- `warm_transfer_sound` — forgetA=0 (слот src не меняется при
  ЛЮБОМ соотношении src/dst, включая вырожденную копию себя) ∧
  dst-слот = копия src ∧ certified-шаг с warm-init (та же
  гарантия, что `adapter_step_certified` — init в statement
  не входит; honest-заметка поднята до теоремы);
- `warm_transfer_train_isolation` — certified-обучение dst ПОСЛЕ
  warm-transfer не трогает src (забывание = 0 структурно);
- `bank_composition` — N доменных обновлений (fold bankBatch):
  слот, которого не касались, держит выход ТОЧНО — индукция по
  списку обновлений.

## Honest pins (что этот мост НЕ покрывает)

- **Transfer-качество НЕ гарантируется**: T1/T2 (better/worse
  than cold) — bench-ЭМПИРИКА (3/3 пары T1 по AUC), не
  теорема; warm-init может быть хуже cold (bench-негатив). Решение «когда переносить» —
  caller (unified.py:156, pre-registered closeness).
- **Shape-mismatch ветка transfer → False** (разные (d,r)) —
  ВНЕ модели: внутри банка формы совпадают по построению
  (`__init__(d, r)` один на все слоты).
- **Ленивое создание слота** (get, seed = len(_adapters)) —
  в банке-как-тотальной-карте отражается нейтральным дефолтом
  (B=0 ⇒ identity, `adapter_neutral_B`); в теоремах изоляции
  не участвует.
- **Обучение trunk/head** — вне носителя: банк замораживает
  общий trunk (wave210: «never changes the incumbent path»);
  если trunk обновляется — см. `trunk_update_needs_projection`.
-/

set_option relaxedAutoImplicit false
set_option linter.style.header false

namespace Hagi.Theory.AdapterBank

open Hagi.Theory.AdapterGrowth

/-! ## Bank-структура: слоты и обновление одного слота -/

section Bank

variable {ι r d : Type*} [Fintype r] [Fintype d] [DecidableEq ι]

/-- Bank доменных адаптеров (wave210): тотальная карта домен →
слот-пара (down `A`, up `B`) — Lean-форма `AdapterBank.
_adapters : dict[domain, LowRankAdapter]` (trunk_ops.py:317).
Слоты гомогенные: один (r, d) на банк по построению. -/
abbrev AdapterBankState (ι r d : Type*) [Fintype r] [Fintype d] :=
  ι → AdaptState r d

/-- Обновление РОВНО одного слота j (семантика всех операций
кода над словарём: get/apply/transfer/обучение трогают
свой слот только). Ключевая структура: `i ≠ j` ⇒ слот i
нетронут БЕЗ гипотез. -/
def bankUpdate (bank : AdapterBankState ι r d) (j : ι)
    (a : AdaptState r d) : AdapterBankState ι r d :=
  fun i => if i = j then a else bank i

/-- Warm-start перенос (wave210b / adapter_warm_start,
trunk_ops.py:286): слот dst получает КОПИЮ факторов слота src.
Копия, не ссылка: в Lean-значениях присваивание пары = копия —
source untouched by construction. -/
def warmTransfer (bank : AdapterBankState ι r d) (src dst : ι) :
    AdapterBankState ι r d :=
  bankUpdate bank dst (bank src)

/-- **(a) adapter_bank_isolation**: обновление слота `j`
не меняет выход слота `i ≠ j` ТОЧНО (ни при каком содержимом
нового слота `a` и входе `x`). Конечная форма
`adapter_isolation_zero_forgetting`: там изоляция — ГИПОТЕЗА
`s' i = s i`; здесь она — структурный факт `bankUpdate`.
Upstream-семантика trunk_ops.py:327 «isolation by construction
(forgetA=0 bit-exact)». -/
theorem adapter_bank_isolation (bank : AdapterBankState ι r d)
    (j : ι) (a : AdaptState r d) (i : ι) (hij : i ≠ j)
    (x : d → ℝ) :
    perTaskVec (bankUpdate bank j a) i x = perTaskVec bank i x := by
  simp only [bankUpdate, perTaskVec]
  rw [if_neg hij]

/-- **(a, obj-форма)**: при изоляции слотов любой функционал от
выхода задачи `i` неизменен после обновления ЧУЖОГО слота `j` —
zero-forgetting сертификат в obj-терминах (loss задачи i —
частный случай). -/
theorem adapter_bank_isolation_obj (bank : AdapterBankState ι r d)
    (j : ι) (a : AdaptState r d) (i : ι) (hij : i ≠ j)
    (obj : (d → ℝ) → ℝ) (x : d → ℝ) :
    obj (perTaskVec (bankUpdate bank j a) i x)
      = obj (perTaskVec bank i x) := by
  rw [adapter_bank_isolation bank j a i hij]

end Bank

/-! ## Warm-transfer: копия + certified-обучение с любого init -/

section Warm

variable {ι r d : Type*} [Fintype r] [Fintype d] [DecidableEq ι]

/-- **Копия не мутирует источник**: после warm-transfer слот
`src` равен исходному при ЛЮБОМ соотношении src/dst — включая
вырожденный случай src = dst (копия слота самого себя = тождество
банка). Python-семантика `dst.A = src.A.copy()` (trunk_ops.py:299):
forgetA = 0 по построению, upstream-measured bit-exact. -/
theorem warm_transfer_source_unchanged
    (bank : AdapterBankState ι r d) (src dst : ι) :
    warmTransfer bank src dst src = bank src := by
  unfold warmTransfer bankUpdate
  by_cases h : src = dst
  · subst h; simp
  · simp [h]

/-- **(b) warm_transfer_sound**: конъюнкция гарантий
warm-start — ровно то, что код даёт и ничего больше:
(1) forgetA = 0: слот src не меняется (`copy semantics`);
(2) dst-слот = копия src (`dst.A = src.A.copy()` + `dst.B =
src.B.copy()`);
(3) certified-обучаемость с warm-init: measured drop
`obj cand < obj (bank src)` ⇒ шаг `adapterStep obj (bank src) cand`
COMMIT-ится и obj строго убывает — та же гарантия
`adapter_step_certified`, init в её statement не входит
(honest-заметка AdapterGrowth — теперь ЯВНАЯ теорема). -/
theorem warm_transfer_sound (bank : AdapterBankState ι r d)
    (src dst : ι) (obj : AdaptState r d → ℝ)
    (cand : AdaptState r d)
    (hdrop : obj cand < obj (bank src)) :
    warmTransfer bank src dst src = bank src ∧
      warmTransfer bank src dst dst = bank src ∧
      adapterStep obj (bank src) cand = cand ∧
      obj (adapterStep obj (bank src) cand) < obj (bank src) := by
  refine ⟨warm_transfer_source_unchanged bank src dst, ?_,
    (adapter_step_certified obj (bank src) cand hdrop).1,
    (adapter_step_certified obj (bank src) cand hdrop).2⟩
  simp [warmTransfer, bankUpdate]

/-- **(b, изоляция после переноса)**: certified-обучение слота
dst ПОСЛЕ warm-transfer (обновление ОДНОГО слота dst) не трогает
выход слота src — forgetA = 0 на протяжении всего цикла переноса
И обучения B. Честная гипотеза `src ≠ dst`: при src = dst
«обучение dst» и есть обучение A (слоты совпадают), забывание
семантически возможно — код (`transfer(src, src)` затем train)
ведёт себя так же. -/
theorem warm_transfer_train_isolation (bank : AdapterBankState ι r d)
    (src dst : ι) (hsd : src ≠ dst) (cand : AdaptState r d)
    (x : d → ℝ) :
    perTaskVec (bankUpdate (warmTransfer bank src dst) dst cand) src x
      = perTaskVec bank src x := by
  rw [adapter_bank_isolation _ dst cand src hsd x]
  unfold perTaskVec
  rw [warm_transfer_source_unchanged bank src dst]

end Warm

/-! ## Композиция: N доменных обновлений -/

section Composition

variable {ι r d : Type*} [Fintype r] [Fintype d] [DecidableEq ι]

/-- Пакетное обновление банка: fold обновлений слотов по списку
(домен, новое состояние) — последовательный continual-цикл N
доменов, каждый своим слотом (get → train → freeze). -/
def bankBatch (bank : AdapterBankState ι r d)
    (upd : List (ι × AdaptState r d)) : AdapterBankState ι r d :=
  upd.foldl (fun b p => bankUpdate b p.1 p.2) bank

/-- **(c) bank_composition**: после N доменных обновлений
(bankBatch, каждый домен — СВОЙ слот) выход слота `i`, которого
НЕ касался ни один шаг, неизменен ТОЧНО — все инварианты
нетронутых доменов держатся при любом числе доменов. Индукция по
списку обновлений с шагом `adapter_bank_isolation` (паттерн
`adapter_per_task_sound`, но структурно: без гипотез заморозки —
нетронутость видна из списка). -/
theorem bank_composition (bank : AdapterBankState ι r d)
    (upd : List (ι × AdaptState r d)) (i : ι)
    (h : ∀ p ∈ upd, p.1 ≠ i) (x : d → ℝ) :
    perTaskVec (bankBatch bank upd) i x = perTaskVec bank i x := by
  induction upd generalizing bank with
  | nil => rfl
  | cons p upd ih =>
      have h1 : p.1 ≠ i := h p List.mem_cons_self
      have hrest : ∀ q ∈ upd, q.1 ≠ i :=
        fun q hq => h q (List.mem_cons_of_mem _ hq)
      unfold bankBatch at *; rw [List.foldl_cons]
      rw [ih (bankUpdate bank p.1 p.2) hrest]
      exact adapter_bank_isolation bank p.1 p.2 i (Ne.symm h1) x

end Composition

end Hagi.Theory.AdapterBank
