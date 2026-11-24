# CONSOLIDATION-GAPS — карта остатков формализации memory-consolidation HAGI_v2

Beat: C636 (23.11.2026). Источник-код: `C:\HAGI_v2` (READ-ONLY,
HEAD 41b6e89, wave241). Наш мост: C584
`Hagi/Theory/KnowledgeConsolidation.lean` (wave225,
unified.py:285-358: `memory`/`remember`/`consolidate`/
`learn_from_dialog` поверх SQLite/FTS5-архива) — 3 инварианта
(`consolidate_prompt_empty`, `remember_preserves_pages`,
`learn_from_dialog_archives`).

Таблица: что из механизмов consolidation-эры (волны 225–241)
НЕ формализовано (сверено с репозиторием primes на HEAD, без
изменений: C584 — 3 теоремы, C592 `warm_transfer_sound`). Каждая строка — rg-факт (файл:строка),
не фантазия. Сложность: low = List/String-композиция уровня
C584; med = нужна новая модель или честный суррогат-инвариант;
high = floating/NN-семантика вне Nat/ℚ-ядра.

| Механизм | Код-якорь (HAGI_v2) | Формализовано? | Сложность |
| --- | --- | --- | --- |
| Wave225 memory/remember/consolidate/learn_from_dialog (prompt-сборка, append-only, архивация-до-ingest) | hagi/unified.py:330-358 | Да — C584 (3 теоремы, membership-уровень) | (done) |
| Hybrid retrieval: FTS5-bm25 candidate set → gemma-cosine rerank (+ fallback полный cosine-sweep на rare-token) | hagi/memory_store/__init__.py:55-80 | Нет; honest pin C584: top-k ранжирование НЕ монотонно — теорема про top-k опущена | med |
| Incremental embedding-индекс (страницы после первого запроса эмбеддятся лениво; wave230 fix про «stale semantic index») | hagi/memory_store/__init__.py:24-54 | Нет | low |
| Replay budget-split: fresh + cumulative replay всех доменов, replay_cap = total budget, per_domain = budget/n_past, floor 8000 байт | hagi/unified.py:93-113 | Нет | med |
| Forgetting-метрика: per-domain CE на собственном holdout после cumulative-тренировки (evolve_step) | hagi/unified.py:565-595 | Нет (CE над NN-выходами) | high |
| Anti-forgetting gate wave241 (P0 fix): incumbent CE измеряется ДО weight-обновлений; деплой-лог = CE последнего repeat, не min | hagi/unified.py:142-146, 155-158 | Нет (порядок измерение→обновление формализуем как state-monotonicity, но сам CE — high) | med |
| Semantic distill ALWAYS ON (wave234/220): gemma-учитель → cosine-align hidden LM на фрагментах (SemanticDistillHead.align_step) | hagi/lm.py:68-140; scripts/restore_domains.py:42-43; scripts/neuro_symbolic_cycle.py:152-190 | Частично смежное: topk-бюджет/хвосты (Hagi/Data/Distill.lean), quant-сертификат + consolidation_bound (Hagi/Model/DistillCert.lean); сам align-цикл — нет | high |
| Warm-start адаптера best-домена (ce ≤ 0.5, identity в B=0) | hagi/unified.py:174-186 | Да — C592 (`warm_transfer_sound`, sufficient-transfer gate) | (done) |
| Полный хронологический контекст отдельно от retrieval (wave241) | hagi/pipeline.py:140 | Нет (тривиально-составной) | low |

Итого гэпов: 7 — low 2, med 3, high 2.

Рекомендация порядка (Pareto): low-гэпы (incremental-index
membership, chronological-context composition) — следующие
C-beats по канону C584; med (replay budget-split как ℕ-модель,
pre/post-измерение как state-монотонность) — после; high
(CE-метрика, cosine-align) — честно отложены до появления
Real/float-слоя (прецедент honest-набросков STATUS.md).
