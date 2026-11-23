/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic

set_option relaxedAutoImplicit false

/-!
# KnowledgeConsolidation — knowledge consolidation from external
memory

Roadmap top-1: мост к HAGI_v2 wave225 (commit d2ef948, READ-ONLY).
Секция `WAVE 225: knowledge consolidation from external memory`,
`hagi/unified.py:285-315`: `Unified` получает `memory()` /
`remember()` / `consolidate()` / `learn_from_dialog()` поверх
`SemanticMemory` (SQLite/FTS5 append-only архив страниц +
gemma-cosine rerank, `hagi/memory_store/__init__.py:11-31`).
Родня: FactLedger (append-only история фактов).

Fresh-minimal инварианты (KISS, 3 теоремы):

- `consolidate_prompt_empty` — graceful degradation: при пустой
  выдаче памяти retrieval-префикс не добавляется, prompt = запрос
  (unified.py:303-305: `if evidence else query`);
- `remember_preserves_pages` — append-only покрытие: ранее
  хранимая страница остаётся в памяти после `remember`
  (DiskBackedContext.append + flush, только INSERT; веса модели не
  трогаются, unified.py:295-297, memory_store/__init__.py:25-27);
- `learn_from_dialog_archives` — полный цикл консолидации
  (dialog → permanent memory → ingest) архивирует текст диалога в
  память ДО ingest (unified.py:308-315).

Honest: top-k ранжирование НЕ монотонно (новая страница может
вытеснить старую из top-3) — теорема про top-k честно опущена;
гарантируется только membership в store. Волна стабильна
(d2ef948 = HEAD HAGI_v2) — мост не откладывается.
-/

namespace Hagi.Theory.KnowledgeConsolidation

/-- Внешняя память — список страниц (append-only архив таблицы
pages, memory_store/streaming; строки только добавляются). -/
abbrev PageStore := List String

/-- `remember text` (unified.py:295-297): добавить текст как новую
страницу постоянного архива; веса модели не затрагиваются. -/
def remember (m : PageStore) (text : String) : PageStore :=
  m ++ [text]

/-- Prompt-сборка `consolidate` (unified.py:299-306): непустая
выдача памяти → evidence-префикс + два перевода строки + запрос;
пустая выдача → запрос как есть. -/
def buildPrompt (hits : List String) (query : String) : String :=
  match hits with
  | [] => query
  | _ => String.intercalate "\n" hits ++ "\n\n" ++ query

/-- Полный цикл консолидации `learn_from_dialog`
(unified.py:308-315): диалог архивируется в память, затем
ингестируется как тренировочный домен. -/
def learnFromDialog (m : PageStore) (dialog : String) :
    PageStore × String :=
  (remember m dialog, dialog)

/-- **Graceful degradation**: при пустой выдаче памяти
retrieval-префикс не добавляется — consolidate вырождается в
чистый ask по запросу (unified.py:304-305). -/
theorem consolidate_prompt_empty (query : String) :
    buildPrompt [] query = query := rfl

/-- **Append-only покрытие**: ранее хранимая страница остаётся
в памяти после remember — консолидация не теряет знание на
уровне store (только INSERT, пути удаления нет). -/
theorem remember_preserves_pages (m : PageStore) (t p : String)
    (h : p ∈ m) : p ∈ remember m t :=
  List.mem_append_left _ h

/-- **Архивация диалога**: после полного цикла консолидации
текст диалога присутствует в постоянной памяти (remember
выполняется ДО ingest, unified.py:312-315). -/
theorem learn_from_dialog_archives (m : PageStore) (d : String) :
    d ∈ (learnFromDialog m d).1 :=
  List.mem_append_right _ (List.mem_singleton_self _)

end Hagi.Theory.KnowledgeConsolidation
