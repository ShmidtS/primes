/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# FactLedger — append-only факт-леджер memory store

Bench-мост к HAGI_v2 волны 219–220 (external memory
store, `hagi/memory_store/facts.py:1` — WAVE 219). Класс
`ConflictAwareFactStore` («append-only evidence ledger with guarded
current-value updates», facts.py:56-59): каждое `facts.propose` INSERT-ит
новую строку в `facts.guarded_fact_history` (facts.py:171-177), DELETE
записей истории нет; найденный ключ `guarded_fact_current` не
удаляется (facts.py:178-186). Идемпотентности append НЕ гарантирует
(повтор того же значения всё равно INSERT-ится, facts.py:152-154) —
dedup-теорема честно опущена.

Fresh-minimal инвариант (KISS, 2 теоремы): история фактов — список
записей, append = `facts ++ [e]`.

- `fact_append_preserves` — существующие записи идентичны после
  append (`List.take_length_append`: take по длине старой истории);
- `fact_lookup_monotone` — найденный факт остаётся найденным
  (`List.mem_append`): append-монотонность запроса.

Обе — мост к Mathlib-леммам `List.take_length_append` /
`List.mem_append`; вклад витка = framing в fact-терминах
(недублирование: леммы Mathlib переиспользуются как есть).
-/

namespace Hagi.Theory.FactLedger

/-- Запись истории фактов (модель строки `facts.guarded_fact_history`,
facts.py:60-69: ключ, значение, источник — идентичность записи). -/
structure FactEntry where
  /-- Ключ факта (столбец fact_key, facts.py:106). -/
  key : String
  /-- Значение факта (`value`, facts.py:107). -/
  value : String
  /-- Источник наблюдения (`source`, facts.py:108). -/
  source : String
  deriving DecidableEq

/-- История фактов — append-only список записей
(`facts.guarded_fact_history`, facts.py:66-76). -/
abbrev FactHistory := List FactEntry

/-- Append нового факта в историю (INSERT в таблицу истории,
facts.py:171-177): только добавление, существующие записи не
переписываются. -/
def factAppend (facts : FactHistory) (e : FactEntry) : FactHistory :=
  facts ++ [e]

/-- **Append-only истории**: существующие записи идентичны после
append — префикс длины старой истории нового состояния равен
старой истории (в `facts.propose` нет путей, меняющих уже записанные
строки значения/источника/порядка, facts.py:141-236). -/
theorem fact_append_preserves (facts : FactHistory) (e : FactEntry) :
    (facts ++ [e]).take facts.length = facts := by
  simp

/-- **Lookup-монотонность**: факт, найденный в истории, остаётся
найденным после append (запрос по истории монотонен по append;
`get`/`history` читают `facts.guarded_fact_history`, которая только
растёт, facts.py:124-140, 196-210). -/
theorem fact_lookup_monotone (facts : FactHistory) (e e' : FactEntry)
    (h : e' ∈ facts) : e' ∈ factAppend facts e :=
  List.mem_append_left _ h

end Hagi.Theory.FactLedger
